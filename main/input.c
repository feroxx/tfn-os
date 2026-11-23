// Touch events, in a task of their own. The render loop needs about 19 ms
// for a frame, which is too slow to time touches well.
//
// Rules:
//  - The touch panel can drop contact for a short time during a touch.
//    A touch ends only after RELEASE_DEBOUNCE_MS with no contact.
//  - It can also lose ONE of two fingers for a short time: the points of input_points() come from the finger
//    tracker (input_fingers.inc): a lost finger stays for RELEASE_DEBOUNCE_MS, and the order stays.
//  - A tap: shorter than LONG_PRESS_MS (TAP_MAX_MS), no point TAP_SLOP_UM (1.8 mm) or more from the first point.
//  - A long press: the finger stays less than TAP_SLOP_UM from the first point for LONG_PRESS_MS.
//    A slop in mm, not in touch px: 10 px are only 0.9-1.3 mm, and a thumb that rolls would lose its tap.
//  - The pull zone of the settings panel (input.h): a finger that comes down in the zone is held; a pull is
//    the panel's finger (the app never sees it), else its held events go to the app with their own times. The events
//    follow the first point of each report that is not the panel's; while
//    a held finger is the first finger, the reports wait in a short list (s_wait) and go through the event machine when
//    the hold ends. A finger that comes down out of the zone is never held: then nothing changes.
//  - The origin of each event (input_injected(), the rule of a consent): the touch task marks each event of a touch
//    that had a virtual finger (a test, a tap of the manager page) in one of its reports, and input_inject() marks
//    each event that it puts in the queue. The mark goes through the queue with the event (IN_NOT_FINGER over the
//    kind), and input_get() takes it off.

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include "power.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"
#include "freertos/semphr.h"
#include "driver/gpio.h"
#include "esp_sleep.h"
#include "esp_timer.h"
#include "esp_log.h"
#include "board.h"
#include "input.h"
#include "settings.h"
#ifdef ESP_PLATFORM
#include "esp_attr.h"  // (EXT_RAM_BSS_ATTR: the lists of the pull guard in PSRAM: the internal RAM is short)
#else
#define EXT_RAM_BSS_ATTR
#endif

#define POLL_MS             10
#define RELEASE_DEBOUNCE_MS 40
// The tap rule: no gap between a tap and a long press, and a slop in
// mm, not in px (the touch px of each board has its own size). 1.8 mm: a thumb that rolls stays in it, and a drag of
// 2 mm goes out of it on each board, also when the panel rounds both of its ends to the touch px (up to 1.4 px less).
// (A box of 10 touch px goes 14.1 px to its corners: on the 3.49 and the CoreS3 the circle of 1.8 mm, 13.5 and
// 14.1 px, does not hold the far corners. So a touch that moves more than 9 px on BOTH axes is not a tap.)
#define TAP_MAX_MS  LONG_PRESS_MS
#define TAP_SLOP_UM 1800
#include "gfx.h"  // (BOARD_TOUCH_PX_UM can read the frame now)
// The size of one px of board_touch_points() (um): the 3.49 panel 133, the CoreS3 panel 128, the AMOLED 111
// (board_amoled.c gives the 240 x 320 frame: 1.4 panel px of 79 um), the Watcher (BOARD_TOUCH_LOGICAL: px of the frame
// now) 89 in the native frame (the round layouts) and 115 in the zoomed CoreS3 frame. (round_fit gives px of 89 um, but
// input.c cannot see it: the slop there is 1.39 mm.)
static int touch_px_um(void)
{
    return BOARD_TOUCH_PX_UM;
}

static QueueHandle_t s_queue;
#define INT_CHECK_MS 250  // the screen off with a touch INT line: a read each 250 ms too (a lost INT)

static volatile int s_poll_ms = POLL_MS;
static volatile bool s_slow;
void input_slow(bool slow)
{
    s_poll_ms = slow ? 5 * POLL_MS : POLL_MS;
    s_slow = slow;
}

// the touch INT line (board_touch_int_gpio): the screen off: the task waits for it (fewer CPU wakes). A level
// interrupt that turns itself off; the line also wakes the CPU from the light sleep.
static int s_int_pin = -1;
static SemaphoreHandle_t s_int_sem;
static void touch_isr(void *arg)
{
    gpio_intr_disable((gpio_num_t)(intptr_t)arg);  // (the pin comes as the argument: s_int_pin is set later)
    BaseType_t hp = pdFALSE;
    xSemaphoreGiveFromISR(s_int_sem, &hp);
    if (hp) {
        portYIELD_FROM_ISR();
    }
}

static void int_init(void)
{
    int pin = board_touch_int_gpio();
    if (pin < 0) {
        return;
    }
    s_int_sem = xSemaphoreCreateBinary();
    // the interrupt stays off (the line can be low now: the CoreS3 AW9523B keeps it low until a read); the task turns
    // it on only while it waits
    gpio_config_t gc = {.pin_bit_mask = 1ULL << pin,
                        .mode = GPIO_MODE_INPUT,
                        .pull_up_en = GPIO_PULLUP_ENABLE,
                        .intr_type = GPIO_INTR_DISABLE};
    if (!s_int_sem || gpio_config(&gc) != ESP_OK) {
        return;
    }
    esp_err_t e = gpio_install_isr_service(0);
    if ((e != ESP_OK && e != ESP_ERR_INVALID_STATE) ||
        gpio_isr_handler_add(pin, touch_isr, (void *)(intptr_t)pin) != ESP_OK) {
        return;
    }
    gpio_set_intr_type(pin, GPIO_INTR_LOW_LEVEL);
    gpio_intr_disable(pin);
    gpio_wakeup_enable(pin, GPIO_INTR_LOW_LEVEL);
    esp_sleep_enable_gpio_wakeup();
    s_int_pin = pin;
}
static input_end_t s_ends[2];
static volatile bool s_multi;
static int16_t s_pt_x[INPUT_MAX_POINTS], s_pt_y[INPUT_MAX_POINTS];
static int s_npt;
static portMUX_TYPE s_ends_lock = portMUX_INITIALIZER_UNLOCKED;
// the virtual fingers of the tests (s_ends_lock: a 64-bit value is two words on this CPU)
static int s_vf_x, s_vf_y;
static int64_t s_vf_until;  // the virtual finger (input_virtual_finger)
static int s_vf2_x, s_vf2_y;
static int64_t s_vf2_until;  // the second virtual finger (input_virtual_finger2): the last point
// the mark of an event that is not by a finger on the panel (in the queue only: input_get() takes it off)
#define IN_NOT_FINGER 0x100
// the event that input_get() gave last (input_injected()): its kind, its time, and finger = by a finger on the panel
// (zero = not by a finger: the safe value before the first event)
static struct {
    int64_t t_ms;
    input_kind_t kind;
    bool finger;
} s_got EXT_RAM_BSS_ATTR;

#define FINGER_HOLD_MS RELEASE_DEBOUNCE_MS
#include "input_fingers.inc"

// ---------------------------------------------------------------- the pull zone of the settings panel (input.h)
enum {
    FZ_NONE,
    FZ_HELD,
    FZ_PULL,
    FZ_WATCH,
    FZ_CUT
};  // finger_t.zone (FZ_CUT: input_cut(), nobody's until it goes up)
static volatile bool s_cut_req;
static input_zone_t s_zone_req;  // the zone of main.c (s_ends_lock)
static volatile bool s_zone_new;
static input_zone_t s_zone;  // the copy of the touch task
static input_pull_t s_pull;  // the finger of the panel (s_ends_lock)
static bool s_pull_any;
static int s_pull_slot = -1;       // its slot (the touch task)
static int s_held = -1;            // the slot in the hold (one at a time), -1 = none
static volatile bool s_hide;       // input_hide(): the app sees no finger
static volatile int64_t s_tshift;  // input_time_shift()
// the reports that wait while a held finger is the first finger (the event machine waits): for each, the first point
// that is not the panel's without the held finger (a) and with it (b), and v = a virtual finger in the report
#define WAIT_MAX (PULL_WIN_MS / POLL_MS + 6)
typedef struct {
    uint16_t dt;
    int16_t ax, ay, bx, by;
    uint8_t a, b, v;
} wait_t;  // dt: ms after s_wait_t0
static wait_t s_wait[WAIT_MAX] EXT_RAM_BSS_ATTR;
static int s_nwait;
static bool s_waiting;
static int64_t s_wait_t0;
#define PULL_RING 12  // the last points of the panel's finger (the flick speed)
static struct {
    uint32_t t;
    int16_t x, y;
} s_ring[PULL_RING] EXT_RAM_BSS_ATTR;
static int s_ring_i;
// a held finger that went up (a tap, not a pull): the app never saw it in input_points(), so it shows there at its last
// point for GHOST_MS after the release (an app that reads the points gets the tap, late)
#define GHOST_MS 60
static int16_t s_ghost_x, s_ghost_y;
static int64_t s_ghost_until;

void input_pull_zone(const input_zone_t *z)
{
    portENTER_CRITICAL(&s_ends_lock);
    s_zone_req = *z;
    s_zone_new = true;
    portEXIT_CRITICAL(&s_ends_lock);
}

bool input_pull_get(input_pull_t *p)
{
    portENTER_CRITICAL(&s_ends_lock);
    *p = s_pull;
    bool any = s_pull_any;
    portEXIT_CRITICAL(&s_ends_lock);
    return any;
}

void input_hide(bool hide)
{
    s_hide = hide;
}
void input_cut(void)
{
    s_cut_req = true;
}
void input_time_shift(int64_t ms)
{
    s_tshift = ms;
}

// the touch calibration (input.h) and the raw points of the panel
static float s_tc[6] = {1, 0, 0, 0, 1, 0};
static volatile bool s_tc_on;
static int16_t s_raw_x[INPUT_MAX_POINTS], s_raw_y[INPUT_MAX_POINTS];
static int s_nraw;
static const char *const TC_KEY[6] = {"tc0", "tc1", "tc2", "tc3", "tc4", "tc5"};

void input_touch_cal_set(const float m[6])
{
    if (!m) {
        s_tc_on = false;
        store_set("tc_on", 0);
        return;
    }
    s_tc_on = false;  // (the touch task does not use half of a new map)
    for (int i = 0; i < 6; i++) {
        s_tc[i] = m[i];
        store_set(TC_KEY[i], (uint32_t)(int32_t)lroundf(m[i] * 10000));
    }
    s_tc_on = true;
    store_set("tc_on", 1);
}

bool input_touch_cal_get(float m[6])
{
    for (int i = 0; i < 6; i++) {
        m[i] = s_tc[i];
    }
    return s_tc_on;
}

int input_points_raw(int16_t *x, int16_t *y, int max)
{
    portENTER_CRITICAL(&s_ends_lock);
    int n = s_nraw < max ? s_nraw : max;
    for (int i = 0; i < n; i++) {
        x[i] = s_raw_x[i];
        y[i] = s_raw_y[i];
    }
    portEXIT_CRITICAL(&s_ends_lock);
    return n;
}

static void touch_cal_load(void)
{
    if (store_get("tc_on", 0) != 1) {
        return;
    }
    float m[6];
    for (int i = 0; i < 6; i++) {
        m[i] = (float)(int32_t)store_get(TC_KEY[i], (i == 0 || i == 4) ? 10000 : 0) / 10000.0f;
    }
    // a sane map only: each scale near 1 (or -1), offsets on the panel
    if (fabsf(m[0]) + fabsf(m[1]) < 0.5f || fabsf(m[3]) + fabsf(m[4]) < 0.5f || fabsf(m[2]) > 2 * LCD_H ||
        fabsf(m[5]) > 2 * LCD_H) {
        return;
    }
    for (int i = 0; i < 6; i++) {
        s_tc[i] = m[i];
    }
    s_tc_on = true;
}

void input_virtual_finger(int px, int py, int64_t until_ms)
{
    portENTER_CRITICAL(&s_ends_lock);
    s_vf_x = px;
    s_vf_y = py;
    s_vf_until = until_ms;
    portEXIT_CRITICAL(&s_ends_lock);
}

void input_virtual_finger2(int px, int py, int64_t until_ms)
{
    portENTER_CRITICAL(&s_ends_lock);
    s_vf2_x = px;
    s_vf2_y = py;
    s_vf2_until = until_ms;
    portEXIT_CRITICAL(&s_ends_lock);
}

// The event machine (es_step): the touch now. virt: a virtual finger was in a report of this touch (its events are
// not by a finger on the panel).
static struct {
    bool down, moved, long_sent, virt;
    int64_t t_down, t_seen;
    int x0, y0, lx, ly;
    int sx, sy, sn;  // the sum of the points of this contact (for the mean point)
    int um;          // touch_px_um() at the IN_DOWN (one slop for all of the touch)
} s_es;

static void emit(input_kind_t kind, int x, int y, int64_t t)
{
    const int k = (int)kind | (s_es.virt ? IN_NOT_FINGER : 0);
    input_event_t ev = {.kind = (input_kind_t)k, .x = (int16_t)x, .y = (int16_t)y, .t_ms = t};
    xQueueSend(s_queue, &ev, 0);
}

// The two end buttons: a touch in the zone presses it; a release needs
// RELEASE_DEBOUNCE_MS with no contact, as for the main touch.
static void ends_update(const int *py, int n, int64_t t)
{
    static int64_t seen[2];
    portENTER_CRITICAL(&s_ends_lock);
    for (int e = 0; e < 2; e++) {
        bool contact = false;
        for (int i = 0; i < n; i++) {
            if (e == 0 ? py[i] < INPUT_END_PX : py[i] >= LCD_H - INPUT_END_PX) {
                contact = true;
            }
        }
        input_end_t *b = &s_ends[e];
        if (contact) {
            if (!b->down) {
                b->down = true;
                b->down_ms = t;
                b->presses++;
            }
            seen[e] = t;
        } else if (b->down && t - seen[e] >= RELEASE_DEBOUNCE_MS) {
            b->down = false;
            b->up_ms = seen[e];
        }
    }
    portEXIT_CRITICAL(&s_ends_lock);
}

void input_ends(input_end_t out[2])
{
    portENTER_CRITICAL(&s_ends_lock);
    out[0] = s_ends[0];
    out[1] = s_ends[1];
    portEXIT_CRITICAL(&s_ends_lock);
    for (int e = 0; e < 2; e++) {  // (the app clock: input_time_shift)
        out[e].down_ms -= s_tshift;
        out[e].up_ms -= s_tshift;
    }
}

bool input_multitouch(void)
{
    return s_multi;
}

int input_points(int16_t *x, int16_t *y, int max)
{
    portENTER_CRITICAL(&s_ends_lock);
    int n = s_npt < max ? s_npt : max;
    for (int i = 0; i < n; i++) {
        x[i] = s_pt_x[i];
        y[i] = s_pt_y[i];
    }
    portEXIT_CRITICAL(&s_ends_lock);
    return n;
}

// The event machine: one report (contact = a point that is not the panel's, at x, y) at the time t. virt: a virtual
// finger is in the report (also when the events follow another point: the touch gets the mark).
static void es_step(bool contact, int x, int y, int64_t t, bool virt)
{
    if (s_es.down) {
        s_es.virt = s_es.virt || virt;
    }
    if (contact) {
        if (!s_es.down) {
            s_es.down = true;
            s_es.virt = virt;
            s_es.t_down = t;
            s_es.x0 = s_es.lx = x;
            s_es.y0 = s_es.ly = y;
            s_es.moved = false;
            s_es.long_sent = false;
            s_es.sx = s_es.sy = s_es.sn = 0;
            s_es.um = touch_px_um();
            emit(IN_DOWN, x, y, t);
        } else if (x != s_es.lx || y != s_es.ly) {
            s_es.lx = x;
            s_es.ly = y;
            emit(IN_MOVE, x, y, t);
        }
        s_es.t_seen = t;
        const int dx = x - s_es.x0, dy = y - s_es.y0;  // (the distance in um: 1.8 mm or more = not a tap)
        if ((int64_t)(dx * dx + dy * dy) * s_es.um * s_es.um >= (int64_t)TAP_SLOP_UM * TAP_SLOP_UM) {
            s_es.moved = true;
        }
        // the mean point of the contact: the edge of a finger touches first, so the first point
        // is often off the middle of the finger; a tap and a long press use the mean point
        if (!s_es.moved) {
            s_es.sx += x;
            s_es.sy += y;
            s_es.sn++;
        }
        if (!s_es.moved && !s_es.long_sent && t - s_es.t_down >= LONG_PRESS_MS) {
            s_es.long_sent = true;
            emit(IN_LONG, s_es.sx / s_es.sn, s_es.sy / s_es.sn, t);
        }
        return;
    }
    if (s_es.down && t - s_es.t_seen >= RELEASE_DEBOUNCE_MS) {
        s_es.down = false;
        emit(IN_UP, s_es.lx, s_es.ly, s_es.t_seen);
        if (!s_es.moved && !s_es.long_sent && s_es.t_seen - s_es.t_down < TAP_MAX_MS) {
            emit(IN_TAP, s_es.sn ? s_es.sx / s_es.sn : s_es.x0, s_es.sn ? s_es.sy / s_es.sn : s_es.y0, s_es.t_seen);
        }
    }
}

// the move of a finger from where it came down: along "down" of the app frame, and to the side (touch px)
static void zone_move(const finger_t *f, int *along, int *side)
{
    int dx = f->x - f->zx, dy = f->y - f->zy;
    *along = dx * s_zone.dx + dy * s_zone.dy;
    *side = abs(dx * s_zone.dy - dy * s_zone.dx);
}
static bool zone_pull_ok(int along, int side)
{
    return along >= s_zone.pull_px && 2 * along >= 3 * side;
}
// the panel's finger: a new pull (slot i), and its point in each report
static void pull_begin(int i, bool watch)
{
    const finger_t *f = &s_fing[i];
    s_pull_slot = watch ? -1 : i;
    s_ring_i = 0;
    for (int k = 0; k < PULL_RING; k++) {
        s_ring[k].t = 0;
    }
    portENTER_CRITICAL(&s_ends_lock);
    s_pull = (input_pull_t){.seq = s_pull.seq + 1,
                            .down = !watch,
                            .watch = watch,
                            .x = f->x,
                            .y = f->y,
                            .x0 = f->zx,
                            .y0 = f->zy,
                            .xp = f->zx,
                            .yp = f->zy,
                            .t_ms = f->seen,
                            .t0_ms = f->t0,
                            .tp_ms = f->t0};
    s_pull_any = true;
    portEXIT_CRITICAL(&s_ends_lock);
}
static void pull_track(int64_t t)
{
    if (s_pull_slot < 0) {
        return;
    }
    const finger_t *f = &s_fing[s_pull_slot];
    if (!f->on || f->zone != FZ_PULL) {
        portENTER_CRITICAL(&s_ends_lock);
        s_pull.down = false;  // (the point and the time of its last report stay)
        portEXIT_CRITICAL(&s_ends_lock);
        s_pull_slot = -1;
        return;
    }
    if (f->seen != t) {
        return;  // (lost for this report: no new point)
    }
    const uint32_t t32 = (uint32_t)t | 1u;  // (0 = an empty place of the ring)
    s_ring[s_ring_i % PULL_RING].t = t32;
    s_ring[s_ring_i % PULL_RING].x = f->x;
    s_ring[s_ring_i % PULL_RING].y = f->y;
    s_ring_i++;
    int pk = -1;  // the newest point 80 ms or more old
    for (int k = 0; k < PULL_RING; k++) {
        if (s_ring[k].t && t32 - s_ring[k].t >= 80 && (pk < 0 || t32 - s_ring[k].t < t32 - s_ring[pk].t)) {
            pk = k;
        }
    }
    portENTER_CRITICAL(&s_ends_lock);
    s_pull.x = f->x;
    s_pull.y = f->y;
    s_pull.t_ms = t;
    if (pk >= 0) {
        s_pull.xp = s_ring[pk].x;
        s_pull.yp = s_ring[pk].y;
        s_pull.tp_ms = t - (int64_t)(t32 - s_ring[pk].t);
    }
    portEXIT_CRITICAL(&s_ends_lock);
}
// the end of the hold: pulled = the finger is the panel's, else it is a normal finger now (cut: nobody's). The reports
// that waited go through the event machine (with their own times).
static void zone_release_as(bool pulled, bool cut)
{
    const bool gone = pulled || cut;  // (the app does not get it)
    if (s_held >= 0) {
        s_fing[s_held].zone = pulled ? FZ_PULL : cut ? FZ_CUT : FZ_NONE;
    }
    if (pulled && s_held >= 0) {
        pull_begin(s_held, false);
    }
    s_held = -1;
    if (s_waiting) {
        for (int k = 0; k < s_nwait; k++) {
            const wait_t *w = &s_wait[k];
            if (gone) {
                es_step(w->a, w->ax, w->ay, s_wait_t0 + w->dt, w->v);
            } else {
                es_step(w->b, w->bx, w->by, s_wait_t0 + w->dt, w->v);
            }
        }
        s_nwait = 0;
        s_waiting = false;
    }
}
static void zone_release(bool pulled)
{
    zone_release_as(pulled, false);
}
// input_cut(): each finger that is down now is nobody's until it goes up (no events, no points, no end button); the
// touch of the event stream ends with an IN_UP and no IN_TAP (main.c gives it to the app that has the touch: at the start of
// the panel the app has its IN_UP already; a touch that comes down in the last frame of the close gets its pair)
static void cut_now(void)
{
    s_cut_req = false;
    if (s_held >= 0) {
        zone_release_as(false, true);
    }
    for (int i = 0; i < INPUT_MAX_POINTS; i++) {
        if (s_fing[i].on && (s_fing[i].zone == FZ_NONE || s_fing[i].zone == FZ_WATCH)) {
            s_fing[i].zone = FZ_CUT;
        }
    }
    if (s_es.down) {
        emit(IN_UP, s_es.lx, s_es.ly, s_es.t_seen);
    }
    s_es.down = false;
    s_ghost_until = 0;
}
// Each report, after the finger tracker: new fingers in the zone, the decision for the held finger.
static void zone_step(int64_t t)
{
    if (s_zone_new) {
        portENTER_CRITICAL(&s_ends_lock);
        s_zone = s_zone_req;
        s_zone_new = false;
        portEXIT_CRITICAL(&s_ends_lock);
    }
    const bool on = s_zone.on && !s_slow && s_zone.x1 > s_zone.x0 && s_zone.y1 > s_zone.y0 && (s_zone.dx || s_zone.dy);
    for (int i = 0; i < INPUT_MAX_POINTS; i++) {
        finger_t *f = &s_fing[i];
        if (!f->on || f->t0 != t || f->zone != FZ_NONE) {
            continue;  // (a new finger: it came down in this report)
        }
        if (!on || f->x < s_zone.x0 || f->x >= s_zone.x1 || f->y < s_zone.y0 || f->y >= s_zone.y1) {
            continue;
        }
        if (s_zone.mode == ZONE_TAKE) {
            f->zone = FZ_PULL;  // (the tab: a touch on it is the panel's at once)
            pull_begin(i, false);
        } else if (s_zone.mode == ZONE_WATCH) {
            f->zone = FZ_WATCH;
        } else if (s_held < 0) {
            f->zone = FZ_HELD;
            s_held = i;
            s_waiting = !s_es.down;  // it is the first finger: the event machine waits for the decision
            s_nwait = 0;
            s_wait_t0 = t;
        }
    }
    for (int i = 0; i < INPUT_MAX_POINTS; i++) {
        finger_t *f = &s_fing[i];
        if (!f->on || f->zone != FZ_WATCH) {
            continue;
        }
        int along, side;
        zone_move(f, &along, &side);
        if (zone_pull_ok(along, side) && t - f->t0 <= PULL_WIN_MS) {
            f->zone = FZ_NONE;
            pull_begin(i, true);  // (a report only: the app keeps the finger)
        } else if (side >= s_zone.side_px || along <= -s_zone.side_px / 2 || t - f->t0 > PULL_WIN_MS) {
            f->zone = FZ_NONE;
        }
    }
    if (s_held >= 0) {
        finger_t *f = &s_fing[s_held];
        int along = 0, side = 0;
        if (f->on) {
            zone_move(f, &along, &side);
        }
        const int64_t age = t - f->t0;
        if (!f->on) {  // it went up (a tap): its events go to the app, and its ghost
            s_ghost_x = f->x;
            s_ghost_y = f->y;
            s_ghost_until = t + GHOST_MS;
            zone_release(false);
        } else if (!on) {
            zone_release(false);  // (the zone went off)
        } else if (zone_pull_ok(along, side) && age <= PULL_WIN_MS) {
            zone_release(true);
        } else if (side >= s_zone.side_px || along <= -s_zone.side_px / 2 || age >= PULL_WIN_MS ||
                   (age >= PULL_HOLD_MS && 3 * along < s_zone.pull_px) || s_nwait >= WAIT_MAX - 1) {
            zone_release(false);
        }
    }
}
// a point of the report that the app may see (its finger is not the panel's, not cut, and not in the hold)
static bool pt_app(const int8_t *own, int j, bool with_held)
{
    int s = own[j];
    if (s < 0) {
        return true;
    }
    int z = s_fing[s].zone;
    return z != FZ_PULL && z != FZ_CUT && (z != FZ_HELD || with_held);
}

// One report of the touch panel at the time t (ms): the calibration, the virtual fingers of the tests, the finger
// tracker, the pull zone, the points and the end buttons of the app, the events. Returns the count of the points of the
// panel.
// THE SCREEN OFF: A NEW TOUCH MUST BE IN TWO READS. A touch chip sometimes sends one report with a point and no
// finger (the AMOLED-1.8 on USB power woke its dark screen by itself about once an hour). With the screen off and no
// finger down, the panel is read again up to CONFIRM_READS times, CONFIRM_MS apart, after the first point of a new
// touch. A point in one of these reads = a real touch (it goes on at once). No point in all of them = a false report:
// no event, no wake. A real tap on the dark AMOLED-1.8 had no point in the read 20 ms after its first one, so one read
// again is not enough. The log line shows the points of each read (the data to tell a tap from a false report).
#define CONFIRM_MS    20
#define CONFIRM_READS 5
static int touch_confirmed(int *px, int *py)
{
    int n = board_touch_points(px, py, INPUT_MAX_POINTS);
    if (n == 0 || !s_slow || s_es.down) {
        return n;
    }
    const int x0 = px[0], y0 = py[0];
    char seq[CONFIRM_READS + 1];
    int k = 0;
    while (k < CONFIRM_READS) {
        vTaskDelay(pdMS_TO_TICKS(CONFIRM_MS));
        n = board_touch_points(px, py, INPUT_MAX_POINTS);
        seq[k++] = (char)('0' + n);
        if (n) {
            break;
        }
    }
    seq[k] = 0;
    static uint32_t s_false;
    s_false += n == 0;
    ESP_LOGI("input", "touch: the screen off, a new touch at (%d,%d), the reads after it: %s: %s (%lu false)", x0, y0,
             seq, n ? "a touch" : "a false report, ignored", (unsigned long)s_false);
    return n;
}

static int input_poll(int64_t t)
{
    {
        int px[INPUT_MAX_POINTS] = {0}, py[INPUT_MAX_POINTS] = {0};
        int n = touch_confirmed(px, py);
        const int n_panel = n;
        // the raw points (SETUP > TOUCH TEST), then the calibration; a copy of the virtual fingers
        portENTER_CRITICAL(&s_ends_lock);
        s_nraw = n;
        for (int i = 0; i < n; i++) {
            s_raw_x[i] = (int16_t)px[i];
            s_raw_y[i] = (int16_t)py[i];
        }
        const int64_t vf_until = s_vf_until, vf2_until = s_vf2_until;
        const int vf_x = s_vf_x, vf_y = s_vf_y, vf2_x = s_vf2_x, vf2_y = s_vf2_y;
        portEXIT_CRITICAL(&s_ends_lock);
        if (s_tc_on) {
            for (int i = 0; i < n; i++) {
                float fx = (float)px[i], fy = (float)py[i];
                int cx = (int)lroundf(s_tc[0] * fx + s_tc[1] * fy + s_tc[2]);
                int cy = (int)lroundf(s_tc[3] * fx + s_tc[4] * fy + s_tc[5]);
                px[i] = cx < 0 ? 0 : (cx >= LCD_W ? LCD_W - 1 : cx);
                py[i] = cy < 0 ? 0 : (cy >= LCD_H ? LCD_H - 1 : cy);
            }
        }
        bool virt = false;  // a virtual finger is in this report (the touch of the events gets the mark)
        if (vf_until && t < vf_until && n < INPUT_MAX_POINTS) {
            // the virtual finger of a test: first, as the finger that the events follow
            for (int i = n; i > 0; i--) {
                px[i] = px[i - 1];
                py[i] = py[i - 1];
            }
            px[0] = vf_x;
            py[0] = vf_y;
            n++;
            virt = true;
        }
        if (vf2_until && t < vf2_until && n < INPUT_MAX_POINTS) {
            px[n] = vf2_x;  // the second virtual finger: the last point
            py[n] = vf2_y;
            n++;
            virt = true;
        }
        if (n >= 2) {
            s_multi = true;
        }
        // The panel sometimes reports no point (or one point less) for a poll while the fingers stay down:
        // the finger tracker keeps a lost finger for the release debounce time (as the events do), so that a
        // stick or a drag that reads the points does not see a short "finger up", also with two thumbs.
        int16_t fx[INPUT_MAX_POINTS], fy[INPUT_MAX_POINTS];
        int8_t fslot[INPUT_MAX_POINTS], own[INPUT_MAX_POINTS];
        int64_t seen0[INPUT_MAX_POINTS];
        for (int i = 0; i < INPUT_MAX_POINTS; i++) {
            seen0[i] = s_fing[i].seen;
        }
        int fn = fingers_track(px, py, n, t, fx, fy, fslot, own);
        // a cut finger that comes back after more than FINGER_HOLD_MS with no point is a new grip (the tracker can give it
        // the slot of the cut thumb): not while the panel shows (the cut keeps RESUME safe), not with the screen off
        for (int i = 0; i < INPUT_MAX_POINTS; i++) {
            finger_t *f = &s_fing[i];
            if (f->on && f->zone == FZ_CUT && f->seen == t && t - seen0[i] > FINGER_HOLD_MS && !s_hide && !s_slow) {
                f->zone = FZ_NONE;
                f->zx = f->x;
                f->zy = f->y;
            }
        }
        if (n > INPUT_MAX_POINTS) {
            n = INPUT_MAX_POINTS;
        }
        if (s_cut_req) {
            cut_now();
        }
        zone_step(t);
        pull_track(t);
        // the points that the app sees: not the panel's finger, not the finger in the hold; none while the panel shows
        const bool hide = s_hide;
        {
            int ey[INPUT_MAX_POINTS], en = 0;
            for (int j = 0; j < n && !hide; j++) {
                if (pt_app(own, j, false)) {
                    ey[en++] = py[j];
                }
            }
            ends_update(ey, en, t);
            portENTER_CRITICAL(&s_ends_lock);
            int k = 0;
            for (int i = 0; i < fn && !hide; i++) {
                int z = s_fing[(int)fslot[i]].zone;
                if (z == FZ_HELD || z == FZ_PULL || z == FZ_CUT) {
                    continue;
                }
                s_pt_x[k] = fx[i];
                s_pt_y[k] = fy[i];
                k++;
            }
            if (t < s_ghost_until && k < INPUT_MAX_POINTS && !hide) {
                s_pt_x[k] = s_ghost_x;
                s_pt_y[k] = s_ghost_y;
                k++;
            }
            s_npt = k;
            portEXIT_CRITICAL(&s_ends_lock);
        }
        // the events: the first point of the report that is not the panel's (the held finger: see s_wait)
        int ja = -1, jb = -1;
        for (int j = 0; j < n; j++) {
            if (ja < 0 && pt_app(own, j, false)) {
                ja = j;
            }
            if (jb < 0 && pt_app(own, j, true)) {
                jb = j;
            }
        }
        if (s_waiting) {
            wait_t *w = &s_wait[s_nwait < WAIT_MAX ? s_nwait++ : WAIT_MAX - 1];
            *w = (wait_t){.dt = (uint16_t)(t - s_wait_t0), .a = ja >= 0, .b = jb >= 0, .v = virt};
            if (ja >= 0) {
                w->ax = (int16_t)px[ja];
                w->ay = (int16_t)py[ja];
            }
            if (jb >= 0) {
                w->bx = (int16_t)px[jb];
                w->by = (int16_t)py[jb];
            }
        } else {
            es_step(ja >= 0, ja >= 0 ? px[ja] : 0, ja >= 0 ? py[ja] : 0, t, virt);
        }
        return n_panel;
    }
}

static void input_task(void *arg)
{
    (void)arg;
    TickType_t wake = xTaskGetTickCount();
    for (;;) {
        bool by_int = false;
        if (s_slow && s_int_pin >= 0 && !s_es.down && s_held < 0 && s_pull_slot < 0) {
            // the screen off and no finger: wait for the touch INT (or 250 ms)
            board_touch_int_ack();
            xSemaphoreTake(s_int_sem, 0);  // (an old signal)
            gpio_intr_enable(s_int_pin);
            by_int = xSemaphoreTake(s_int_sem, pdMS_TO_TICKS(INT_CHECK_MS)) == pdTRUE;
            gpio_intr_disable(s_int_pin);
            wake = xTaskGetTickCount();
        } else {
            vTaskDelayUntil(&wake, pdMS_TO_TICKS(s_slow && (power_x() & PWX_TOUCH) ? 500 : s_poll_ms));
        }
        int n = input_poll(esp_timer_get_time() / 1000);
        if (by_int && n == 0) {
            vTaskDelay(pdMS_TO_TICKS(30));  // (the line is low with no touch: not a fast loop)
        }
    }
}

void input_init(void)
{
    touch_cal_load();
    s_queue = xQueueCreate(64, sizeof(input_event_t));
    int_init();
    xTaskCreatePinnedToCore(input_task, "input", 3072, NULL, 5, NULL, 1);
}

void input_inject(const input_event_t *ev)
{
    input_event_t e = *ev;
    e.kind = (input_kind_t)((int)e.kind | IN_NOT_FINGER);
    xQueueSend(s_queue, &e, 0);
}

bool input_injected(const input_event_t *ev)
{
    // (the event as input_get() gave it, or with the app clock of main.c: input_time_shift())
    const bool same = ev->kind == s_got.kind && (ev->t_ms == s_got.t_ms || ev->t_ms + s_tshift == s_got.t_ms);
    return !same || !s_got.finger;
}

// input_tap_cancel(): an app that starts its own drag (a scroll, a move) calls it in its
// input function. Then the IN_TAP and the IN_LONG of this touch do not come out of input_get(): the drag of the app
// wins. (A touch of 10-14 px can start the drag of an app AND be a tap, and a slow drag can stay in the slop for
// LONG_PRESS_MS.) The next
// IN_DOWN clears it.
static volatile bool s_tap_cancel;
void input_tap_cancel(void);  // (declared in input.h)
void input_tap_cancel(void)
{
    s_tap_cancel = true;
}

bool input_get(input_event_t *ev)
{
    while (xQueueReceive(s_queue, ev, 0) == pdTRUE) {
        const bool finger = ((int)ev->kind & IN_NOT_FINGER) == 0;
        ev->kind = (input_kind_t)((int)ev->kind & ~IN_NOT_FINGER);
        if (ev->kind == IN_DOWN) {
            s_tap_cancel = false;
        } else if ((ev->kind == IN_TAP || ev->kind == IN_LONG) && s_tap_cancel) {
            continue;  // (the dragged touch)
        }
        s_got.t_ms = ev->t_ms;
        s_got.kind = ev->kind;
        s_got.finger = finger;
        return true;
    }
    return false;
}

static volatile int s_wheel_presses;
static volatile bool s_wheel_down;
#if BOARD_WHEEL
static int s_wheel_last;
#endif

bool input_has_wheel(void)
{
    return BOARD_WHEEL;
}

static volatile int s_wheel_keys;  // the steps of the arrow keys (input_wheel_add)
void input_wheel_add(int steps)
{
    s_wheel_keys += steps;
}
int input_wheel(void)
{
    int k = s_wheel_keys;
    s_wheel_keys = 0;
#if BOARD_WHEEL
    int p = board_wheel_pos(), d = p - s_wheel_last;
    s_wheel_last = p;
    return d + k;
#else
    return k;
#endif
}

int input_wheel_presses(void)
{
    int n = s_wheel_presses;
    s_wheel_presses = 0;
    return n;
}

bool input_wheel_down(void)
{
    return s_wheel_down;
}

void input_wheel_press_add(void)
{
    s_wheel_presses++;
}

void input_wheel_set_down(bool down)
{
    s_wheel_down = down;
}

// ---- the keys of a keyboard (input.h: input_key_push / input_key_pop)
static uint32_t s_keys[128];  // (a held key repeats each 45 ms; a fast typist)
static volatile int s_key_r, s_key_w;
static portMUX_TYPE s_key_mux = portMUX_INITIALIZER_UNLOCKED;
void input_key_push(int key, int mods)
{
    portENTER_CRITICAL(&s_key_mux);
    int n = (s_key_w + 1) % 128;
    if (n != s_key_r) {  // (a full queue: the key goes)
        s_keys[s_key_w] = (uint32_t)(key & 0xFFFF) | (uint32_t)(mods & 0xFF) << 16;
        s_key_w = n;
    }
    portEXIT_CRITICAL(&s_key_mux);
}
bool input_key_pop(int *key, int *mods)
{
    bool got = false;
    portENTER_CRITICAL(&s_key_mux);
    if (s_key_r != s_key_w) {
        uint32_t v = s_keys[s_key_r];
        s_key_r = (s_key_r + 1) % 128;
        *key = (int)(v & 0xFFFF);
        *mods = (int)(v >> 16 & 0xFF);
        got = true;
    }
    portEXIT_CRITICAL(&s_key_mux);
    return got;
}

bool input_pending(void)
{
    return uxQueueMessagesWaiting(s_queue) > 0;
}

void input_flush(void)
{
    xQueueReset(s_queue);
    s_tap_cancel = false;
    s_wheel_presses = 0;
#if BOARD_WHEEL
    s_wheel_last = board_wheel_pos();
#endif
}
