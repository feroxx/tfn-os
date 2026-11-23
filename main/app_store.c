// STORE (TFN OS): the store on the board. The apps that the profile of this board shows, from
// the manager on the LAN or the VPN (main/tfn_store.c); INSTALL TO BOARD / TO CARD, UPDATE, OPEN, REMOVE.
//
// The tabs: FOR YOU (the recommended and the required apps that are not on the board; else all new apps), GAMES,
// UTIL, UPDATES (installed apps with a newer version in the store), INSTALLED (all app files on the board). A tap on
// the tab name or a swipe up / down goes to the next tab; a swipe left / right or a tap on an icon moves in the row.
//
// The network work (the catalog, the icons, the installs) runs on a worker task, so the screen never waits. The
// worker ends when the app closes (it finishes the file that it sends first). The layouts: the 3.49 bar (640 x 172:
// the row at the left, the details and two big buttons at the right) and the 320 x 240 frame (CoreS3, AMOLED; the
// Watcher shows the frame in its circle: round_fit).
//
// The app page: a tap on the app in the middle of the row (or on its name in the details) opens its page:
// the description of the store (English or Hebrew: the panel item LANGUAGE), the size, the version and the permission
// classes. The two buttons stay at their places. A tap on the name at the top or a swipe up or down closes the page; a
// swipe left or right shows the page of the next app of the tab.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "esp_timer.h"
#ifdef ESP_PLATFORM
#include "esp_vfs_fat.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#endif
#include "app.h"
#include "audio.h"
#include "board.h"
#include "gfx.h"
#include "kfont.h"
#include "mfont.h"
#include "settings.h"
#include "storage.h"
#include "sysui.h"
#include "tfn_app.h"
#include "tfn_pub.h"
#include "../libs/kscroll/kscroll.h"
#include "tfn_store.h"
#include "uikit.h"
#include "wifi.h"
#include "tfn/theme.h"

static const char *TAG = "store";

enum {
    T_FOR,
    T_GAMES,
    T_UTIL,
    T_UPD,
    T_INST,
    NT
};
static const char *const TAB_NAME[NT] = {"FOR YOU", "GAMES", "UTIL", "UPDATES", "INSTALLED"};

// ---------------------------------------------------------------- the catalog (written by the worker)
typedef struct {
    tfn_cat_t c;
    uint8_t *icon;  // icon.bin from the manager (PSRAM), NULL = not yet
    size_t icon_len;
    bool icon_tried;
} sitem_t;
static sitem_t *s_cat;  // PSRAM, TFN_CAT_MAX places
static volatile int s_ncat;
static volatile int s_cstate;  // 0 = loading, 1 = ready, -1 = no store
static char s_cerr[96];

// the worker
enum {
    J_NONE,
    J_REFRESH,
    J_INSTALL,
    J_UPDATE_ALL,
    J_MOVE
};
#ifdef ESP_PLATFORM
static TaskHandle_t s_task;
#else
static void *s_task;  // (the host: no worker; a demo catalog for the pictures)
#endif
static volatile bool s_quit;
static volatile int s_job;
static char s_job_id[24];
static volatile int s_job_place;
static volatile int s_pct = -1;  // the progress of an install (0..100), -1 = none
static char s_toast[120];
static volatile int64_t s_toast_at;
static volatile bool s_toast_new;

// the view
typedef struct {
    int16_t cat;
    int16_t inst;
} vitem_t;  // an index of s_cat and of the installed list (-1 = none)
static vitem_t s_view[TFN_CAT_MAX + TFN_MAX];
static bool built_only(const tfn_cat_t *c);  // (a built-in app: after acts_of)
static bool built_newer(const tfn_cat_t *c);
static int s_nview;
static int s_tab = T_FOR;
static int s_sel[NT];
static float s_pos;     // the row: the icon in the middle (a fraction while it moves)
static kscroll_t s_ks;  // the row as a carousel in px (libs/kscroll): the icon i is at i * s_gap
static float s_gap;     // the gap of the layout (px) that s_ks uses
static bool s_down, s_drag, s_vswipe, s_inrow;
static int s_x0, s_y0, s_lx;
static int64_t s_now;
static uint64_t s_bfree, s_btot;
static uint32_t s_ctot_kb, s_cfree_kb;
static bool s_card;
static int64_t s_space_at;
static char s_ask_id[24];    // the id of the REMOVE question (the list can change under the question)
static char s_ask_inst[24];  // the id of the install that waits for the permission question
static int s_ask_place;
static char s_want[24];   // a notice opened STORE at this app ("upd:<id>"): the selection when the catalog comes
static char s_page[24];   // the app page is open: the id of its app ("" = the row)
static bool s_he = true;  // the descriptions in Hebrew (the panel item LANGUAGE, the store key st_lang)

static void toast(const char *t)
{
    snprintf(s_toast, sizeof s_toast, "%s", t);
    for (char *p = s_toast; *p; p++) {
        if (*p >= 'a' && *p <= 'z') {
            *p = (char)(*p - 32);  // (the UI is in capitals)
        }
    }
    s_toast_new = true;
}

// ---------------------------------------------------------------- the worker task
// the icons and the catalog of the store go (the STORE closed); not while a worker can still read them
static void icons_free(void)
{
    s_cstate = 0;
    tfn_icon_cache_free();  // (the slots keep the places of these icons)
    for (int i = 0; i < s_ncat; i++) {
        free(s_cat[i].icon);
        s_cat[i].icon = NULL;
        s_cat[i].icon_len = 0;
        s_cat[i].icon_tried = false;
        tfn_store_cat_free(&s_cat[i].c, 1);
    }
    s_ncat = 0;
}

#ifdef ESP_PLATFORM
static void progress(int pct)
{
    s_pct = pct > 100 ? 100 : pct;
}

static void load_catalog(void)
{
    s_cstate = 0;
    vTaskDelay(pdMS_TO_TICKS(120));  // (a frame that draws the old catalog ends first: its icons and texts go now)
    for (int i = 0; i < s_ncat; i++) {
        free(s_cat[i].icon);
        tfn_store_cat_free(&s_cat[i].c, 1);
    }
    s_ncat = 0;
    tfn_cat_t *tmp = heap_caps_calloc(TFN_CAT_MAX, sizeof(tfn_cat_t), MALLOC_CAP_SPIRAM);
    char msg[96] = "";
    int n = tmp ? tfn_store_catalog(tmp, TFN_CAT_MAX, msg, sizeof msg) : -1;
    if (n < 0) {
        snprintf(s_cerr, sizeof s_cerr, "%s", tmp ? msg : "NO MEMORY");
        free(tmp);
        s_cstate = -1;
        return;
    }
    for (int i = 0; i < n; i++) {
        memset(&s_cat[i], 0, sizeof s_cat[i]);
        s_cat[i].c = tmp[i];  // (its description goes with it)
    }
    free(tmp);
    s_ncat = n;
    s_cstate = 1;
    ESP_LOGI(TAG, "%d apps in the store (profile %s)", n, tfn_store_profile());
}

static void worker(void *arg)
{
    (void)arg;
    while (!s_quit) {
        int job = s_job;
        if (job == J_REFRESH) {
            s_job = J_NONE;
            load_catalog();
        } else if (job == J_INSTALL) {
            char msg[120] = "";
            s_pct = 0;
            bool ok = tfn_store_install(s_job_id, s_job_place, progress, msg, sizeof msg);
            s_pct = -1;
            if (s_job == J_INSTALL) {
                s_job = J_NONE;  // (a new open of STORE can have asked a refresh)
            }
            toast(ok ? msg : msg[0] ? msg : "THE INSTALL FAILED");
            ESP_LOGI(TAG, "install %s: %s", s_job_id, msg);
        } else if (job == J_MOVE) {
            char msg[120] = "";
            s_pct = 0;
            bool ok = tfn_move(s_job_id, s_job_place, msg, sizeof msg);
            s_pct = -1;
            if (s_job == J_MOVE) {
                s_job = J_NONE;
            }
            toast(ok       ? (s_job_place == TFN_CARD ? "MOVED TO THE CARD" : "MOVED TO THE BOARD")
                  : msg[0] ? msg
                           : "THE MOVE FAILED");
            ESP_LOGI(TAG, "move %s: %s", s_job_id, ok ? "ok" : msg);
        } else if (job == J_UPDATE_ALL) {
            char msg[120] = "";
            int done = 0, asks = 0;
            for (int i = 0; i < s_ncat && !s_quit; i++) {
                const tfn_cat_t *c = &s_cat[i].c;
                for (int k = 0; k < tfn_count(); k++) {
                    const tfn_entry_t *e = tfn_entry(k);
                    if (strcmp(e->id, c->id) || e->code >= c->code) {
                        continue;
                    }
                    if (c->perms & ~e->perms) {
                        asks++;  // (a new permission class: UPDATE on the app asks the user first)
                        break;
                    }
                    snprintf(s_job_id, sizeof s_job_id, "%s", c->id);
                    s_pct = 0;
                    if (tfn_store_install(c->id, e->place, progress, msg, sizeof msg)) {
                        done++;
                    }
                    break;
                }
            }
            s_pct = -1;
            if (s_job == J_UPDATE_ALL) {
                s_job = J_NONE;
            }
            if (asks) {
                snprintf(msg, sizeof msg, "%d UPDATED, %d ASK FIRST", done, asks);
            } else {
                snprintf(msg, sizeof msg, "%d APPS UPDATED", done);
            }
            toast(msg);
        } else if (s_cstate == 1) {
            // the icons of the apps that the board does not have (one at a time; an install comes first)
            bool any = false;
            for (int i = 0; i < s_ncat && !s_quit && s_job == J_NONE; i++) {
                if (s_cat[i].icon_tried) {
                    continue;
                }
                s_cat[i].icon_tried = true;
                size_t len = 0;
                uint8_t *b = tfn_store_icon(s_cat[i].c.id, &len);
                s_cat[i].icon_len = len;
                s_cat[i].icon = b;
                any = true;
                vTaskDelay(1);
                break;
            }
            if (!any) {
                vTaskDelay(pdMS_TO_TICKS(100));
            }
        } else {
            vTaskDelay(pdMS_TO_TICKS(100));
        }
    }
    icons_free();  // (the STORE closed: its icons go; the next open reads the catalog again)
    s_task = NULL;
    vTaskDelete(NULL);
}
#else
static void host_demo(void)
{
    // the host pictures (tests/host): a small store (the descriptions: a long one, Latin words in a Hebrew one, none)
    static const struct {
        const char *id, *name, *ver, *group;
        uint32_t code, bytes, perms;
        uint8_t st;
        const char *en, *he;
    } D[] = {{"simon", "SIMON", "1.0.35", "GAMES", 1, 38420, 0, TFN_ST_RECOMMENDED,
              "The memory game of four coloured pads. The console plays a sequence of lights and tones; press it back. "
              "Each round adds one step and the steps get faster. Goals of 8, 14, 20 or 31 steps, a best score, and 2 "
              "PLAYERS: each adds a new colour.",
              "משחק הזיכרון של ארבע לוחיות צבעוניות. הקונסולה מנגנת רצף של אורות וצלילים; לחצו עליו בחזרה. כל סיבוב "
              "מוסיף צעד, והצעדים נעשים מהירים יותר. יעדים של 8, 14, 20 או 31 צעדים, שיא, ו-2 שחקנים: כל אחד מוסיף צבע "
              "חדש."},
             {"weather", "WEATHER", "1.0.35", "UTIL", 1, 270588, 0, TFN_ST_AVAILABLE,
              "Weather with a live sky: its colours follow the sun and the clouds of your place. It shows the weather "
              "now, the next 24 hours and 10 days, rain in the next 4 hours, wind, UV and air quality. Up to 8 places. "
              "Needs WiFi. English and Hebrew.",
              "מזג אוויר עם שמיים חיים: הצבעים עוקבים אחרי השמש והעננים במקום שלכם. מציג את המצב עכשיו, את 24 השעות "
              "הבאות ואת 10 הימים הבאים, גשם ב-4 השעות הקרובות, רוח, UV ואיכות אוויר. עד 8 מקומות. דורש WiFi. אנגלית "
              "ועברית."},
             {"hourglass", "HOURGLASS", "1.0.35", "UTIL", 1, 29876, 0, TFN_ST_REQUIRED,
              "A real sand timer. Turn the board over to start it, and lay it flat to stop it.",
              "שעון חול אמיתי. הופכים את הלוח כדי להתחיל, ומניחים אותו כדי לעצור."},
             {"tuner", "TUNER", "1.0.35", "UTIL", 1, 21000, 1, TFN_ST_AVAILABLE, "", ""}};
    for (int i = 0; i < s_ncat; i++) {
        tfn_store_cat_free(&s_cat[i].c, 1);
    }
    for (int i = 0; i < 4; i++) {
        memset(&s_cat[i], 0, sizeof s_cat[i]);
        snprintf(s_cat[i].c.id, sizeof s_cat[i].c.id, "%s", D[i].id);
        snprintf(s_cat[i].c.name, sizeof s_cat[i].c.name, "%s", D[i].name);
        snprintf(s_cat[i].c.ver, sizeof s_cat[i].c.ver, "%s", D[i].ver);
        snprintf(s_cat[i].c.group, sizeof s_cat[i].c.group, "%s", D[i].group);
        s_cat[i].c.code = D[i].code;
        s_cat[i].c.bytes = D[i].bytes;
        s_cat[i].c.perms = D[i].perms;
        s_cat[i].c.state = D[i].st;
        size_t le = strlen(D[i].en), lh = strlen(D[i].he);
        if (le + lh && (s_cat[i].c.desc = malloc(le + lh + 2))) {
            memcpy(s_cat[i].c.desc, D[i].en, le + 1);
            memcpy(s_cat[i].c.desc + le + 1, D[i].he, lh + 1);
        }
    }
    s_ncat = 4;
    s_cstate = 1;
}
#endif

// ---------------------------------------------------------------- the view
static const tfn_entry_t *inst_of(const char *id)
{
    for (int k = 0; k < tfn_count(); k++) {
        if (!strcmp(tfn_entry(k)->id, id)) {
            return tfn_entry(k);
        }
    }
    return NULL;
}

static int inst_index(const char *id)
{
    for (int k = 0; k < tfn_count(); k++) {
        if (!strcmp(tfn_entry(k)->id, id)) {
            return k;
        }
    }
    return -1;
}

static void build_view(void)
{
    s_nview = 0;
    int ready = s_cstate == 1 ? s_ncat : 0;
    if (s_tab == T_INST) {
        for (int k = 0; k < tfn_count(); k++) {
            int c = -1;
            for (int i = 0; i < ready; i++) {
                if (!strcmp(s_cat[i].c.id, tfn_entry(k)->id)) {
                    c = i;
                }
            }
            s_view[s_nview++] = (vitem_t){(int16_t)c, (int16_t)k};
        }
        return;
    }
    for (int pass = 0; pass < 2; pass++) {
        for (int i = 0; i < ready; i++) {
            const tfn_cat_t *c = &s_cat[i].c;
            const tfn_entry_t *e = inst_of(c->id);
            bool add = false;
            if (s_tab == T_GAMES) {
                add = pass == 0 && !strcasecmp(c->group, "GAMES");
            } else if (s_tab == T_UTIL) {
                add = pass == 0 && strcasecmp(c->group, "GAMES");
            } else if (s_tab == T_UPD) {
                add = pass == 0 && ((e && e->code < c->code) || (!e && built_newer(c)));
            } else if (s_tab == T_FOR) {
                add = !e && !built_only(c) && (pass == 0 ? c->state != TFN_ST_AVAILABLE : c->state == TFN_ST_AVAILABLE);
            }
            if (add) {
                s_view[s_nview++] = (vitem_t){(int16_t)i, (int16_t)inst_index(c->id)};
            }
        }
    }
}

static void space_now(void)
{
    if (s_space_at && s_now - s_space_at < 2000) {
        return;
    }
    s_space_at = s_now;
#ifdef ESP_PLATFORM
    if (esp_vfs_fat_info(STORAGE_ROOT, &s_btot, &s_bfree) != ESP_OK) {
        s_btot = s_bfree = 0;
    }
#else
    s_btot = 3993600;
    s_bfree = 1998848;
#endif
    s_card = board_sd_mounted() && board_sd_info(&s_ctot_kb, &s_cfree_kb);
}

static void fmt_size(char *o, int n, uint64_t b)
{
    if (b >= 1024ull * 1024 * 1024) {
        snprintf(o, n, "%.1f GB", b / 1073741824.0);
    } else if (b >= 1024 * 1024) {
        snprintf(o, n, "%.1f MB", b / 1048576.0);
    } else {
        snprintf(o, n, "%u KB", (unsigned)((b + 1023) / 1024));
    }
}

// ---------------------------------------------------------------- the layout
typedef struct {
    int x, y, w, h;
} box_t;
typedef struct {
    int row_cx, row_cy, big, small, gap;  // the row of icons
    box_t tab, b1, b2, panel;
    int name_x, name_y, info_y, chip_y, sel_name_y;
    bool bar;
    bool tall;  // the Tab5 (640 x 360): bigger icons, text and buttons
#if BOARD_ROUND
    bool round;  // a round panel (APP_ROUND_HI): the tab on the top cap, the buttons on the bottom cap
#endif
} lay_t;
#if BOARD_ROUND
#define L_RND(l) ((l).round)
#else
#define L_RND(l) false  // (no round panel: the layout has no round field)
#endif

#if BOARD_ROUND
// The round panels: the values are for 466 x 466; SR() scales them to the frame (412 on the Watcher).
#define SR(v) ((v) * gfx_w / 466)

// The half width of the circle at the height y (0 out of the circle).
static int chord_half(int y)
{
    int r = gfx_w / 2, dy = y - gfx_h / 2;
    return dy * dy >= r * r ? 0 : (int)sqrtf((float)(r * r - dy * dy));
}
#endif

static lay_t lay(void)
{
    lay_t L;
    memset(&L, 0, sizeof L);
#if BOARD_BAR_SCREEN
    L.bar = true;
    L.row_cx = 200;
    L.row_cy = 100;
    L.big = 92;
    L.small = 58;
    L.gap = 104;
    L.tab = (box_t){0, 0, 330, 38};
    L.panel = (box_t){400, 40, 232, 126};
    L.name_x = 414;
    L.name_y = 70;
    L.info_y = 90;
    L.chip_y = 0;
    L.b1 = (box_t){408, 100, 108, 60};
    L.b2 = (box_t){520, 100, 108, 60};
    L.sel_name_y = 164;
#elif BOARD_UI_TABLET
    L.tall = true;
    L.row_cx = 320;
    L.row_cy = 130;
    L.big = 132;
    L.small = 84;
    L.gap = 150;
    L.tab = (box_t){0, 0, 300, 40};
    L.panel = (box_t){0, 0, 0, 0};
    L.name_x = 320;
    L.name_y = 246;
    L.info_y = 272;
    L.chip_y = 0;
    L.b1 = (box_t){40, 292, 270, 56};
    L.b2 = (box_t){330, 292, 270, 56};
    L.sel_name_y = 0;
#elif BOARD_ROUND
    // the tab and the space on the top cap, the row of icons across the middle, the name under it, the two buttons on
    // the bottom cap (their low corners inside the circle)
    L_RND(L) = true;
    L.row_cx = gfx_w / 2;
    L.row_cy = SR(196);
    L.big = SR(116);
    L.small = SR(74);
    L.gap = SR(124);
    L.tab = (box_t){SR(103), SR(22), SR(260), SR(70)};
    L.name_x = gfx_w / 2;
    L.name_y = SR(298);
    L.info_y = SR(324);
    L.b1 = (box_t){SR(88), SR(342), SR(140), SR(58)};
    L.b2 = (box_t){SR(238), SR(342), SR(140), SR(58)};
#else
    L.row_cx = 160;
    L.row_cy = 92;
    L.big = 86;
    L.small = 54;
    L.gap = 92;
    L.tab = (box_t){0, 0, 200, 36};
    L.panel = (box_t){0, 0, 0, 0};
    L.name_x = 160;
    L.name_y = 160;
    L.info_y = 180;
    L.chip_y = 0;
    L.b1 = (box_t){8, 190, 148, 46};
    L.b2 = (box_t){164, 190, 148, 46};
    L.sel_name_y = 0;
#endif
    return L;
}

static bool in_box(const box_t *b, int x, int y)
{
    return b->w && ui_hit(x, y, b->x, b->y, b->w, b->h, 6);
}

// the two buttons of the selected item: their words, and whether they work now
typedef struct {
    const char *t1, *t2;
    bool on1, on2;
    int act1, act2;
} acts_t;
enum {
    A_NONE,
    A_INST_BOARD,
    A_INST_CARD,
    A_OPEN,
    A_UPDATE,
    A_REMOVE,
    A_UPDATE_ALL,
    A_RETRY,
    A_OPEN_BUILT
};

// a built-in app with no newer package: the store shows it as BUILT IN (Release A: all apps are built in)
static bool built_only(const tfn_cat_t *c)
{
    return c && menu_builtin(c->name) && !tfn_newer_than_fw(c->ver);
}
static bool built_newer(const tfn_cat_t *c)
{
    return c && menu_builtin(c->name) && tfn_newer_than_fw(c->ver);
}

static acts_t acts_of(const vitem_t *v)
{
    acts_t a = {"", "", false, false, A_NONE, A_NONE};
    const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
    const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
    bool busy = s_job != J_NONE || s_pct >= 0;
    if (!e && built_only(c)) {
        a.t1 = "OPEN";
        a.act1 = A_OPEN_BUILT;
        a.on1 = true;
        a.t2 = "BUILT IN";
        a.act2 = A_NONE;
        a.on2 = false;
        return a;
    }
    if (!e && c) {
        uint64_t need = (uint64_t)c->bytes + 64 * 1024;
        bool card_ok = s_card && (uint64_t)s_cfree_kb * 1024 >= need, board_ok = s_bfree >= need;
        bool to_card = s_card && tfn_inst_place_card();
        // INSTALL = to the place of INSTALL TO in the panel (the card when it is in); the second button: the other
        // place (a built-in app: UPDATE, its file takes the place)
        a.t1 = built_newer(c) ? "UPDATE" : "INSTALL";
        a.act1 = to_card ? A_INST_CARD : A_INST_BOARD;
        a.on1 = !busy && (to_card ? card_ok : board_ok);
        if (to_card) {
            a.t2 = "TO BOARD";
            a.act2 = A_INST_BOARD;
            a.on2 = !busy && board_ok;
        } else {
            a.t2 = "TO CARD";
            a.act2 = A_INST_CARD;
            a.on2 = !busy && card_ok;
        }
        return a;
    }
    if (e) {
        if (c && e->code < c->code) {
            a.t1 = "UPDATE";
            a.act1 = A_UPDATE;
            a.on1 = !busy;
        } else {
            a.t1 = "OPEN";
            a.act1 = A_OPEN;
            a.on1 = tfn_runs(e);
        }
        if (s_tab == T_UPD) {
            a.t2 = "UPDATE ALL";
            a.act2 = A_UPDATE_ALL;
            a.on2 = !busy;
        } else if (tfn_store_required(e->id)) {
            a.t2 = "KEPT";
            a.act2 = A_NONE;
            a.on2 = false;
        } else {
            a.t2 = "REMOVE";
            a.act2 = A_REMOVE;
            a.on2 = !busy;
        }
    }
    return a;
}

// ---------------------------------------------------------------- the panel
// INSTALL TO: the place of a new app (the store key st_place: 0 = CARD, 1 = BOARD; tfn_inst_place_card()). MOVE TO
// CARD / MOVE TO BOARD: the installed app in the middle of the row goes to the other place (a job of the worker).
// LANGUAGE: the language of the descriptions on the app page (the store key st_lang: 0 = English, 1 = Hebrew; the
// panel speaks it too: sysui.c app_hebrew()).
enum {
    IT_PLACE,
    IT_TOCARD,
    IT_TOBOARD,
    IT_LANG
};
static const char *const PLACE_VALS[] = {"CARD", "כרטיס", "BOARD", "לוח"};
static const char *const LANG_VALS[] = {"ENGLISH", "אנגלית", "HEBREW", "עברית"};
static const pitem_t ITEMS[] = {
        {PI_PICK, IT_PLACE, 2, 0, {"INSTALL TO", "התקנה אל"}, PLACE_VALS, "st_place"},
        {PI_ACT, IT_TOCARD, 0, 0, {"MOVE TO CARD", "העברה לכרטיס"}, NULL, NULL},
        {PI_ACT, IT_TOBOARD, 0, 0, {"MOVE TO BOARD", "העברה ללוח"}, NULL, NULL},
        {PI_PICK, IT_LANG, 2, 1, {"LANGUAGE", "שפה"}, LANG_VALS, "st_lang"},
};

static const tfn_entry_t *sel_entry(void)
{
    int sel = s_sel[s_tab];
    if (sel < 0 || sel >= s_nview || s_view[sel].inst < 0) {
        return NULL;
    }
    return tfn_entry(s_view[sel].inst);
}

static bool item_shown(int id)
{
    if (id == IT_PLACE || id == IT_LANG) {
        return true;
    }
    const tfn_entry_t *e = sel_entry();
    if (!e || s_job != J_NONE || s_pct >= 0) {
        return false;
    }
    return id == IT_TOCARD ? e->place == TFN_BOARD && s_card : e->place == TFN_CARD;
}

static void item_set(int id, int v)
{
    if (id == IT_LANG) {
        s_he = v == 1;
        return;
    }
    const tfn_entry_t *e = sel_entry();
    if (id == IT_PLACE || !e || s_job != J_NONE || s_pct >= 0) {
        return;
    }
    snprintf(s_job_id, sizeof s_job_id, "%s", e->id);
    s_job_place = id == IT_TOCARD ? TFN_CARD : TFN_BOARD;
    s_pct = 0;
    s_job = J_MOVE;
    sfx_ui(SFX_CLICK);
}

static const pitems_t PANEL = {ITEMS, 4, item_shown, NULL, item_set, NULL, NULL};

// ---------------------------------------------------------------- the app
// The row: the length of the carousel for the list now, and the selection in the middle at once.
static void row_jump(void)
{
    ks_set_max(&s_ks, s_nview > 1 ? (float)(s_nview - 1) * s_gap : 0);
    ks_jump(&s_ks, (float)s_sel[s_tab] * s_gap);
    s_pos = (float)s_sel[s_tab];
}

static void enter(int64_t now)
{
    s_now = now;
    s_down = s_drag = false;
    ks_init(&s_ks, 1, 0);
    s_gap = 0;  // (update() sets the gap, the snap and the view from the layout)
    s_space_at = 0;
    if (!s_cat) {
        s_cat = heap_caps_calloc(TFN_CAT_MAX, sizeof(sitem_t), MALLOC_CAP_SPIRAM);
    }
    s_cstate = 0;
    s_toast_at = 0;
#ifdef ESP_PLATFORM
    // (the worker of the last open can still end its file: wait a short time; it stops at its next look at s_quit.
    // When it still runs, it goes on as the worker of this open, and the refresh comes after its job)
    for (int i = 0; i < 50 && s_task; i++) {
        vTaskDelay(pdMS_TO_TICKS(100));
    }
    s_quit = false;
    s_job = J_REFRESH;
    // (the stack must be in internal RAM: the worker writes the flash (/data), and a flash write stops the cache, so a
    // task with its stack in PSRAM may not run then: ESP-IDF asserts)
    if (s_cat && !s_task) {
        xTaskCreatePinnedToCore(worker, "store", 7168, NULL, 2, &s_task, 1);
    }
#else
    if (s_cat) {
        host_demo();
    }
#endif
    s_tab = T_FOR;  // (the store opens on FOR YOU each time)
    s_want[0] = 0;
    s_page[0] = 0;
    s_he = store_get("st_lang", 1) == 1;
    const char *arg = app_launch_arg();
    if (!strncmp(arg, "upd:", 4)) {  // (a notice of an app update: the tab UPDATES, the app when the catalog comes)
        snprintf(s_want, sizeof s_want, "%s", arg + 4);
        s_tab = T_UPD;
    }
    build_view();
    row_jump();
    sysui_panel_items(&PANEL);
}

static const char *id_of(const vitem_t *v)
{
    return v->cat >= 0 ? s_cat[v->cat].c.id : v->inst >= 0 ? tfn_entry(v->inst)->id : "";
}

// the place of an app in the view of the tab now, -1 = not there
static int view_at(const char *id)
{
    for (int i = 0; i < s_nview; i++) {
        if (!strcmp(id_of(&s_view[i]), id)) {
            return i;
        }
    }
    return -1;
}

// the app of a notice (s_want) in the view of the tab now: its place, -1 = not there
static int want_at(void)
{
    return view_at(s_want);
}

// the app page (the head comment)
static void page_open(int i)
{
    if (i < 0 || i >= s_nview) {
        return;
    }
    s_sel[s_tab] = i;
    snprintf(s_page, sizeof s_page, "%s", id_of(&s_view[i]));
    row_jump();
    sfx_ui(SFX_CLICK);
}

static void page_close(void)
{
    s_page[0] = 0;
    sfx_ui(SFX_BACK);
}

static void page_step(int dir)
{
    int i = s_sel[s_tab] + dir;
    if (i < 0 || i >= s_nview) {
        sfx_ui(SFX_BACK);
        return;
    }
    s_sel[s_tab] = i;
    snprintf(s_page, sizeof s_page, "%s", id_of(&s_view[i]));
    row_jump();
    sfx_ui(SFX_TICK);
}

static void leave(void)
{
    s_quit = true;  // (the worker ends after the file that it sends now)
}

static void set_tab(int t)
{
    s_tab = (t + NT) % NT;
    build_view();
    if (s_sel[s_tab] >= s_nview) {
        s_sel[s_tab] = s_nview ? s_nview - 1 : 0;
    }
    row_jump();
    sfx_ui(SFX_TICK);
}

static void remove_answer(int a)
{
    if (a != 1 || !s_ask_id[0]) {
        return;
    }
    char msg[96];
    bool ok = tfn_remove(s_ask_id, msg, sizeof msg);
    sfx_play(ok ? SFX_CUT : SFX_BACK);
    toast(ok ? "REMOVED" : msg);
}

// the answer to the permission question: the install starts (by its id; the list can change under the question)
static void perm_answer(int a)
{
    if (a != 1 || !s_ask_inst[0] || s_job != J_NONE || s_pct >= 0) {
        return;
    }
    snprintf(s_job_id, sizeof s_job_id, "%s", s_ask_inst);
    s_job_place = s_ask_place;
    s_pct = 0;
    s_job = J_INSTALL;
    sfx_ui(SFX_CLICK);
}

static void act(int what, const vitem_t *v)
{
    const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
    const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
    switch (what) {
    case A_INST_BOARD:
    case A_INST_CARD:
    case A_UPDATE:
        if (!c) {
            return;
        }
        // a permission class (sdk/docs/raw.md) that the app does not have yet: the user says yes first
        if (c->perms & ~(e ? e->perms : 0)) {
            static char t[48], l[96];
            char p[80];
            snprintf(s_ask_inst, sizeof s_ask_inst, "%s", c->id);
            s_ask_place = what == A_INST_CARD ? TFN_CARD : what == A_UPDATE && e ? e->place : TFN_BOARD;
            tfn_perms_text(c->perms & ~(e ? e->perms : 0), p, sizeof p);
            snprintf(t, sizeof t, "%s %s?", e ? "UPDATE" : "INSTALL", c->name);
            snprintf(l, sizeof l, "IT CAN %s", p);
            sysui_ask(t, l, e ? "UPDATE" : "INSTALL", "NO", 20, perm_answer);
            sysui_ask_closable();
            sysui_ask_finger();  // (a new permission is a consent: a finger on the panel)
            sfx_ui(SFX_TICK);
            break;
        }
        snprintf(s_job_id, sizeof s_job_id, "%s", c->id);
        s_job_place = what == A_INST_CARD ? TFN_CARD : what == A_UPDATE && e ? e->place : TFN_BOARD;
        s_pct = 0;
        s_job = J_INSTALL;
        sfx_ui(SFX_CLICK);
        break;
    case A_UPDATE_ALL:
        s_job = J_UPDATE_ALL;
        sfx_ui(SFX_CLICK);
        break;
    case A_OPEN:
        if (e) {
            const app_t *a = tfn_find(e->name);
            if (a) {
                sfx_ui(SFX_CLICK);
                app_open(a);
            }
        }
        break;
    case A_OPEN_BUILT:
        if (c) {
            const app_t *a = app_find(c->name);
            if (a) {
                sfx_ui(SFX_CLICK);
                app_open(a);
            }
        }
        break;
    case A_REMOVE:
        if (e) {
            static char t[48];
            snprintf(s_ask_id, sizeof s_ask_id, "%s", e->id);
            snprintf(t, sizeof t, "REMOVE %s?", e->name);
            sysui_ask(t, "THE SAVES STAY", "REMOVE", "KEEP", 20, remove_answer);
            sysui_ask_closable();
        }
        break;
    case A_RETRY:
        s_job = J_REFRESH;
        sfx_ui(SFX_CLICK);
        break;
    }
}

static void input(const input_event_t *ev)
{
    lay_t L = lay();
    int sel = s_sel[s_tab];
    if (ev->kind == IN_DOWN) {
        s_down = true;
        s_drag = s_vswipe = false;
        s_x0 = s_lx = ev->x;
        s_y0 = ev->y;
        // a touch on the row goes to the carousel (a touch that stops a glide gives no tap); the page has no row
#if BOARD_ROUND
        s_inrow = !s_page[0] && (ev->y > L.tab.y + L.tab.h && ev->y < L.row_cy + 58);  // (under the top cap)
#else
        s_inrow = !s_page[0] && (L.bar ? ev->x < L.panel.x - 4 : (ev->y > 36 && ev->y < L.row_cy + 58));
#endif
        if (s_inrow) {
            ks_down(&s_ks, (float)ev->x, ev->t_ms);
        }
        return;
    }
    if (ev->kind == IN_MOVE && s_down && s_page[0]) {
        // the page: a swipe up or down closes it, a swipe left or right goes to the next app of the tab
        int dx = ev->x - s_x0, dy = ev->y - s_y0;
        if (s_vswipe) {
            return;
        }
        if (abs(dy) > 28 && abs(dy) > abs(dx) * 3 / 2) {
            s_vswipe = true;
            input_tap_cancel();
            page_close();
        } else if (abs(dx) > 40 && abs(dx) > abs(dy) * 3 / 2) {
            s_vswipe = true;
            input_tap_cancel();
            page_step(dx < 0 ? 1 : -1);
        }
        return;
    }
    if (ev->kind == IN_MOVE && s_down) {
        int dx = ev->x - s_x0, dy = ev->y - s_y0;
        if (!s_drag && !s_vswipe && abs(dy) > 28 && abs(dy) > abs(dx) * 3 / 2) {
            s_vswipe = true;
            input_tap_cancel();
            set_tab(s_tab + (dy < 0 ? 1 : -1));
            return;
        }
        if (!s_vswipe && s_inrow && ks_move(&s_ks, (float)ev->x, ev->t_ms)) {
            input_tap_cancel();
            s_drag = true;
        }
        if (s_drag && s_gap > 0) {
            s_pos = ks_pos(&s_ks) / s_gap;
        }
        return;
    }
    if (ev->kind == IN_UP) {
        if (s_inrow) {
            ks_up(&s_ks, ev->t_ms);
        }
        s_down = s_drag = false;
        return;
    }
    if (ev->kind != IN_TAP) {
        return;
    }
    if (s_inrow && !ks_tap_ok(&s_ks)) {
        return;
    }
    bool page = s_page[0] && s_cstate == 1;
    if (in_box(&L.tab, ev->x, ev->y)) {  // the tab name: the next tab; on the page: back to the row
        if (page) {
            page_close();
        } else {
            set_tab(s_tab + 1);
        }
        return;
    }
    if (s_cstate != 1) {
        if (s_cstate == -1 && in_box(&L.b1, ev->x, ev->y)) {
            act(A_RETRY, NULL);
        }
        return;
    }
    if (s_nview && sel < s_nview) {
        acts_t a = acts_of(&s_view[sel]);
        if (in_box(&L.b1, ev->x, ev->y)) {
            if (a.on1) {
                act(a.act1, &s_view[sel]);
            } else {
                sfx_ui(SFX_BACK);
            }
            return;
        }
        if (in_box(&L.b2, ev->x, ev->y)) {
            if (a.on2) {
                act(a.act2, &s_view[sel]);
            } else {
                sfx_ui(SFX_BACK);
            }
            return;
        }
        if (page) {
            return;
        }
        // the name and the facts of the selected app (over the buttons): its page
        const int ny = L.row_cy + L.big / 2 + 5;  // (under the icon of the row: 140 in the 320 x 240 frame)
        box_t nb = L.bar ? (box_t){L.panel.x, L.panel.y, L.panel.w, L.b1.y - 8 - L.panel.y}
                         : (box_t){0, ny, gfx_w, L.b1.y - 8 - ny};
        if (in_box(&nb, ev->x, ev->y)) {
            page_open(sel);
            return;
        }
    }
    if (page) {
        return;
    }
    // a tap on an icon of the row (the one in the middle: its page)
    for (int i = 0; i < s_nview; i++) {
        float d = i - s_pos;
        if (fabsf(d) > 2.5f) {
            continue;
        }
        int s = fabsf(d) < 0.5f ? L.big : L.small;
        int cx = L.row_cx + (int)(d * L.gap);
        if (ev->x >= cx - s / 2 - 6 && ev->x <= cx + s / 2 + 6 && ev->y >= L.row_cy - s / 2 - 6 &&
            ev->y <= L.row_cy + s / 2 + 6) {
            if (i != sel) {
                s_sel[s_tab] = i;
                ks_to(&s_ks, (float)i * s_gap);
                sfx_ui(SFX_TICK);
            } else {
                page_open(i);
            }
            return;
        }
    }
}

static void update(int64_t now)
{
    s_now = now;
    space_now();
    build_view();
    if (s_sel[s_tab] >= s_nview) {
        s_sel[s_tab] = s_nview ? s_nview - 1 : 0;
    }
    if (s_want[0] && s_cstate != 0) {  // the app of a notice: select it (UPDATES, else INSTALLED)
        int i = want_at();
        if (i < 0 && s_tab == T_UPD) {
            s_tab = T_INST;
            build_view();
            i = want_at();
        }
        if (i >= 0) {
            s_sel[s_tab] = i;
        }
        s_want[0] = 0;
        row_jump();
    }
    // the app of the page keeps its page when the list of the tab changes (an install takes it out of FOR YOU, an
    // update out of UPDATES: then INSTALLED has it)
    if (s_page[0] && s_cstate == 1) {
        int i = view_at(s_page);
        if (i < 0 && s_tab != T_INST) {
            s_tab = T_INST;
            build_view();
            i = view_at(s_page);
        }
        if (i < 0) {
            s_page[0] = 0;
        } else if (i != s_sel[s_tab]) {
            s_sel[s_tab] = i;
            row_jump();
        }
    } else if (s_cstate == -1) {
        s_page[0] = 0;
    }
    // the carousel: the gap of the layout (a turn of the board can change it), the length, the glide
    lay_t L = lay();
    if ((float)L.gap != s_gap) {
        s_gap = (float)L.gap;
        ks_set_snap(&s_ks, s_gap);
        ks_set_view(&s_ks, s_gap * 3);
        row_jump();
    }
    ks_set_max(&s_ks, s_nview > 1 ? (float)(s_nview - 1) * s_gap : 0);
    ks_update(&s_ks, now);
    s_pos = s_gap > 0 ? ks_pos(&s_ks) / s_gap : (float)s_sel[s_tab];
    if (s_nview) {
        int n = (int)lroundf(s_pos);
        n = n < 0 ? 0 : n >= s_nview ? s_nview - 1 : n;
        if (ks_moving(&s_ks)) {
            if (n != s_sel[s_tab]) {  // the icon in the middle is the selection: a tick for each icon
                s_sel[s_tab] = n;
                sfx_ui(SFX_TICK);
            }
        } else if (n != s_sel[s_tab]) {
            ks_to(&s_ks, (float)s_sel[s_tab] * s_gap);  // (a selection from elsewhere: the row goes to it)
        }
    }
    if (s_toast_new) {
        s_toast_new = false;
        s_toast_at = now;
    }
}

// ---------------------------------------------------------------- drawing
static uint16_t s_bg0, s_bg1;
static void background(void)
{
    // a dark violet field that is lighter at the top (the colours of the menu)
    for (int y = 0; y < gfx_h; y++) {
        uint16_t c = ui_mix(THEME_STORE_BG_TOP, THEME_STORE_BG_BOTTOM, y * 255 / gfx_h);
        for (int x = 0; x < gfx_w; x++) {
            g_fb[y * gfx_w + x] = c;
        }
    }
    (void)s_bg0;
    (void)s_bg1;
}

static void draw_icon_of(const vitem_t *v, int x, int y, int s)
{
    if (v->inst >= 0) {
        const tfn_entry_t *e = tfn_entry(v->inst);
        if (e && e->stub.draw_icon) {
            gfx_clip_box(x, y, x + s, y + s);
            e->stub.draw_icon(x, y, s);
            gfx_clip_box_off();
            gfx_clip_reset();
            return;
        }
    }
    if (v->cat >= 0) {
        const sitem_t *it = &s_cat[v->cat];
        if (it->icon && tfn_icon_draw(it->icon, it->icon_len, x, y, s)) {
            return;
        }
        tfn_icon_plain(it->c.name, x, y, s);
    }
}

static const char *name_of(const vitem_t *v)
{
    if (v->cat >= 0) {
        return s_cat[v->cat].c.name;
    }
    if (v->inst >= 0) {
        return tfn_entry(v->inst)->name;
    }
    return "";
}

static void button(const box_t *b, const char *t, bool on, bool main_btn)
{
    if (!b->w || !t[0]) {
        return;
    }
    uint16_t fill = !on ? THEME_STORE_BTN_OFF : main_btn ? THEME_STORE_BTN_MAIN : THEME_STORE_BTN;
    uint16_t edge = !on ? THEME_STORE_BTN_OFF_EDGE : main_btn ? THEME_STORE_BTN_MAIN_EDGE : THEME_STORE_BTN_EDGE;
    ui_rbox(b->x, b->y, b->w, b->h, 12, fill, edge, 2);
    const mfont_t *f = mf_width(&MF_N20, t, 1) <= b->w - 12 ? &MF_N20 : &MF_N16;
    mf_text_c(f, b->x + b->w / 2, b->y + b->h / 2 + f->asc / 2, t, on ? THEME_STORE_BTN_TEXT : THEME_STORE_BTN_TEXT_OFF,
              255, 1);
}

// the buttons of the selected item, or the progress of its install in their place
static void draw_actions(const lay_t *L, const vitem_t *v, const tfn_cat_t *c, const tfn_entry_t *e)
{
    char line[48];
    if (s_pct >= 0 && (!strcmp(s_job_id, c ? c->id : e ? e->id : "") || s_job == J_UPDATE_ALL)) {
        box_t b = {L->b1.x, L->b1.y, L->b2.x + L->b2.w - L->b1.x, L->b1.h};
        ui_rbox(b.x, b.y, b.w, b.h, 12, THEME_STORE_TRACK, THEME_STORE_TRACK_EDGE, 2);
        int w = (b.w - 8) * s_pct / 100;
        if (w > 0) {
            ui_rrect(b.x + 4, b.y + 4, w, b.h - 8, 9, THEME_STORE_PROGRESS);
        }
        snprintf(line, sizeof line, "INSTALLING %d%%", s_pct);
        mf_text_c(&MF_N16, b.x + b.w / 2, b.y + b.h / 2 + MF_N16.asc / 2, line, THEME_STORE_BTN_TEXT, 255, 1);
    } else {
        acts_t a = acts_of(v);
        button(&L->b1, a.t1, a.on1, true);
        button(&L->b2, a.t2, a.on2, false);
    }
}

// the size, the version and the place of an item ("46 KB  1.0.35  ON THE CARD")
static void facts_of(const tfn_cat_t *c, const tfn_entry_t *e, char *line, int len)
{
    char a1[24];
    fmt_size(a1, sizeof a1, c ? c->bytes : e ? e->bytes : 0);
    // (an app that a key of the publisher list signed: the name of the key, and NOT REVIEWED with no store signature)
    char by[40] = "";
    if (e && e->pub[0]) {
        snprintf(by, sizeof by, "BY %s%s", e->pub,
                 e->pub_st == TFN_PUB_NOT_REVIEWED ? ", NOT REVIEWED"
                 : e->pub_st == TFN_PUB_OK_TEST    ? ", TEST KEY"
                                                   : "");
    }
    const char *where = by[0]                                 ? by
                        : e                                   ? (e->place == TFN_CARD ? "ON THE CARD" : "ON THE BOARD")
                        : built_only(c)                       ? "BUILT IN"
                        : built_newer(c)                      ? "BUILT IN, NEW IN THE STORE"
                        : c && c->state == TFN_ST_REQUIRED    ? "REQUIRED"
                        : c && c->state == TFN_ST_RECOMMENDED ? "RECOMMENDED"
                                                              : "";
    if (e && c && e->code < c->code) {
        snprintf(line, len, "%s  NEW %s", a1, c->ver);
    } else {
        snprintf(line, len, "%s  %s%s%s", a1, c ? c->ver : e ? e->ver : "", where[0] ? "  " : "", where);
    }
}

// ---------------------------------------------------------------- the app page: the text
// The lines of the text flow: the 3.49: three long lines over the buttons, then short lines at their left; the frame:
// four lines at the right of the icon, then lines of the full width under the icon, over the buttons.
typedef struct {
    int16_t x0, x1, base;
} fline_t;
typedef struct {
    const char *s;
    int n;
} span_t;

static int page_flow(const lay_t *L, fline_t *o, int max)
{
    int n = 0;
    if (L->bar) {
        for (int b = 58; b <= 92 && n < max; b += 17) {
            o[n++] = (fline_t){140, 628, (int16_t)b};
        }
        for (int b = 112; b <= 163 && n < max; b += 17) {
            o[n++] = (fline_t){140, (int16_t)(L->b1.x - 12), (int16_t)b};
        }
#if BOARD_ROUND
    } else if (L_RND(*L)) {
        // (the round panels: four lines at the right of the icon, then lines across the circle, over the buttons;
        // each line ends at the circle)
        int lh = KF_TEXT.line, b = SR(132);
        for (int i = 0; i < 4 && n < max; i++, b += lh) {
            int h = chord_half(b - KF_TEXT.asc);
            o[n++] = (fline_t){(int16_t)SR(150), (int16_t)(gfx_w / 2 + h - SR(16)), (int16_t)b};
        }
        for (b = SR(132) + 4 * lh + SR(10); b <= L->b1.y - SR(12) && n < max; b += lh) {
            int h = chord_half(b > gfx_h / 2 ? b + 4 : b - KF_TEXT.asc);
            o[n++] = (fline_t){(int16_t)(gfx_w / 2 - h + SR(16)), (int16_t)(gfx_w / 2 + h - SR(16)), (int16_t)b};
        }
#endif
    } else if (L->tall) {
        // (the Tab5: five lines at the right of the big icon, then five lines of the full width)
        for (int b = 70; b <= 158 && n < max; b += 22) {
            o[n++] = (fline_t){150, (int16_t)(gfx_w - 12), (int16_t)b};
        }
        for (int b = 186; b <= 274 && n < max; b += 22) {
            o[n++] = (fline_t){16, (int16_t)(gfx_w - 12), (int16_t)b};
        }
    } else {
        for (int b = 58; b <= 109 && n < max; b += 17) {
            o[n++] = (fline_t){84, 310, (int16_t)b};
        }
        for (int b = 130; b <= 181 && n < max; b += 17) {
            o[n++] = (fline_t){10, 310, (int16_t)b};
        }
    }
    return n;
}

static int u8len(const char *s)
{
    uint8_t c = (uint8_t)*s;
    return c >= 0xF0 ? 4 : c >= 0xE0 ? 3 : c >= 0xC0 ? 2 : 1;
}
static uint32_t u8cp(const char *s)
{
    const uint8_t *p = (const uint8_t *)s;
    if (p[0] >= 0xE0 && p[1] && p[2]) {
        return ((p[0] & 15u) << 12) | ((p[1] & 63u) << 6) | (p[2] & 63u);
    }
    if (p[0] >= 0xC0 && p[1]) {
        return ((p[0] & 31u) << 6) | (p[1] & 63u);
    }
    return p[0];
}
static bool heb_cp(uint32_t c)
{
    return c >= 0x590 && c <= 0x5FF;
}
static bool has_heb(const char *s)
{
    for (; *s; s += u8len(s)) {
        if (heb_cp(u8cp(s))) {
            return true;
        }
    }
    return false;
}

// the width of the first n bytes of s
static int span_w(const kfont_t *f, const char *s, int n)
{
    char b[256];
    if (n > (int)sizeof b - 1) {
        n = (int)sizeof b - 1;
    }
    memcpy(b, s, (size_t)n);
    b[n] = 0;
    return ui_text_w(f, b);
}

// The text t in the lines of the flow from line k: each line gets the words that fit (a word longer than a line is
// cut). Returns the next free line; *rest = the text that did not fit ("" = all of it).
static int wrap_flow(const kfont_t *f, const char *t, const fline_t *fl, int nfl, int k, span_t *out, const char **rest)
{
    while (*t == ' ') {
        t++;
    }
    while (*t && k < nfl) {
        int w = fl[k].x1 - fl[k].x0, end = 0;
        for (;;) {
            int e = end;
            while (t[e] == ' ') {
                e++;
            }
            if (!t[e]) {
                break;
            }
            while (t[e] && t[e] != ' ') {
                e++;
            }
            if (e > 200 || span_w(f, t, e) > w) {
                break;
            }
            end = e;
        }
        if (!end) {  // a word longer than the line: the characters that fit
            while (t[end] && t[end] != ' ' && span_w(f, t, end + u8len(t + end)) <= w) {
                end += u8len(t + end);
            }
            if (!end) {
                end = u8len(t);
            }
        }
        out[k++] = (span_t){t, end};
        t += end;
        while (*t == ' ') {
            t++;
        }
    }
    *rest = t;
    return k;
}

// One line of a Hebrew text from its right end x1: the Hebrew parts from the right, a Latin part (a name, a number)
// from the left. A small form of the bidi rules: a pair of brackets with Hebrew in it is Hebrew, a pair with only Latin
// in it after a Latin part is Latin; a mark (a space, a point) between two Latin parts is Latin, else it is Hebrew; a
// bracket of a Hebrew part is mirrored. (ui_text keeps the order of each Latin word but puts the words of a name such as
// "BEEPER 97" from the right.)
static void line_rtl(const kfont_t *f, int x1, int base, const char *s, int n, uint16_t col)
{
    enum {
        MARK,
        HEB,
        LAT
    };
    uint8_t cls[200];
    int off[201], m = 0, i = 0;
    while (i < n && m < 200) {
        uint32_t c = u8cp(s + i);
        off[m] = i;
        cls[m++] = heb_cp(c) ? HEB
                   : ((c >= '0' && c <= '9') || ((c | 32) >= 'a' && (c | 32) <= 'z') || (c >= 0xC0 && c < 0x2000))
                           ? LAT
                           : MARK;
        i += u8len(s + i);
    }
    off[m] = i;
    int open[8], no = 0;  // the brackets (the inner pairs close first)
    for (int j = 0; j < m; j++) {
        if (s[off[j]] == '(' && no < 8) {
            open[no++] = j;
        } else if (s[off[j]] == ')' && no) {
            int o = open[--no], before = HEB;
            bool h = false, l = false;
            for (int q = o + 1; q < j; q++) {
                h |= cls[q] == HEB;
                l |= cls[q] == LAT;
            }
            for (int q = o - 1; q >= 0; q--) {
                if (cls[q] != MARK) {
                    before = cls[q];
                    break;
                }
            }
            cls[o] = cls[j] = (uint8_t)(!h && l && before == LAT ? LAT : HEB);
        }
    }
    for (int a = 0; a < m;) {  // the marks take the class of their side
        if (cls[a] != MARK) {
            a++;
            continue;
        }
        int b = a;
        while (b < m && cls[b] == MARK) {
            b++;
        }
        uint8_t k = a > 0 && b < m && cls[a - 1] == LAT && cls[b] == LAT ? LAT : HEB;
        for (int j = a; j < b; j++) {
            cls[j] = k;
        }
        a = b;
    }
    int x = x1;
    for (int a = 0; a < m;) {
        int b = a;
        while (b < m && cls[b] == cls[a]) {
            b++;
        }
        if (cls[a] == LAT) {
            char t[256];
            int len = off[b] - off[a] < (int)sizeof t - 1 ? off[b] - off[a] : (int)sizeof t - 1;
            memcpy(t, s + off[a], (size_t)len);
            t[len] = 0;
            x -= ui_text_w(f, t);
            ui_text(f, x, base, t, col);
        } else {
            for (int j = a; j < b; j++) {
                char t[5];
                int len = off[j + 1] - off[j];
                memcpy(t, s + off[j], (size_t)len);
                t[len] = 0;
                if (len == 1) {
                    static const char MIR[] = "()[]{}<>";
                    const char *p = strchr(MIR, t[0]);
                    if (p && t[0]) {
                        t[0] = MIR[(p - MIR) ^ 1];
                    }
                }
                x -= ui_text_w(f, t);
                if (t[0] != ' ') {
                    ui_text(f, x, base, t, col);
                }
            }
        }
        a = b;
    }
}

// one line of the flow (a Hebrew text from the right end); ell: an ellipsis at its end
static void flow_line(const kfont_t *f, const fline_t *fl, span_t sp, bool rtl, bool ell, uint16_t col)
{
    char t[260];
    int n = sp.n;
    if (ell) {  // the words that fit with the ellipsis
        while (n > 0 && span_w(f, sp.s, n) + ui_text_w(f, "…") > fl->x1 - fl->x0) {
            n--;
            while (n > 0 && sp.s[n] != ' ') {
                n--;
            }
        }
    }
    if (n > (int)sizeof t - 4) {
        n = (int)sizeof t - 4;
    }
    memcpy(t, sp.s, (size_t)n);
    if (ell) {
        memcpy(t + n, "…", 3), n += 3;
    }
    t[n] = 0;
    if (rtl) {
        line_rtl(f, fl->x1, fl->base, t, n, col);
    } else {
        ui_text(f, fl->x0, fl->base, t, col);
    }
}

// a back mark: an arrow head that points to the left, its tip at (x, y)
static void back_mark(int x, int y, int h, uint16_t col)
{
    for (int i = 0; i <= 10; i++) {
        int d = h * i / 20;
        ui_circle(x + d, y - d, 2, col, 255);
        ui_circle(x + d, y + d, 2, col, 255);
    }
}

// the toast (a short line after an install or a removal) at the top right, for 4 s; maxw: the room for it
static void draw_toast(const lay_t *L, int maxw)
{
    int w = ui_text_w(&KF_LABEL, s_toast) + 24;
    if (w > maxw) {
        w = maxw;
    }
    int x = gfx_w - 6 - w, y = L->bar ? 6 : 4;
#if BOARD_ROUND
    if (L_RND(*L)) {
        x = (gfx_w - w) / 2;  // (the round panels: in the middle, under the tab)
        y = L->tab.y + L->tab.h - 6;
    }
#endif
    ui_rrect(x, y, w, 26, 13, THEME_STORE_TOAST_BG);
    ui_text_c(&KF_LABEL, x + w / 2, y + 18, s_toast, THEME_STORE_TOAST_TEXT);
}

static void draw_actions(const lay_t *L, const vitem_t *v, const tfn_cat_t *c, const tfn_entry_t *e);

#if BOARD_ROUND
// the round app page: the description, then the permission classes (IT CAN ...), in the flow
static void page_text(const lay_t *L, const tfn_cat_t *c, const tfn_entry_t *e)
{
    char line[112];
    fline_t fl[12];
    span_t sp[12];
    int nfl = page_flow(L, fl, 12), k = 0;
    const char *d = tfn_store_desc(c, s_he), *rest = "";
    const kfont_t *df = &KF_TEXT;  // (a bigger text)
    if (d[0]) {
        bool rtl = has_heb(d);
        k = wrap_flow(df, d, fl, nfl, 0, sp, &rest);
        for (int i = 0; i < k; i++) {
            flow_line(df, &fl[i], sp[i], rtl, rest[0] && i == k - 1, THEME_STORE_DESC);
        }
    } else {
        flow_line(df, &fl[0], (span_t){"NO DESCRIPTION IN THE STORE YET", 31}, false, false, THEME_STORE_TEXT_FAINT);
        k = 1;
    }
    uint32_t pm = c ? c->perms : e ? e->perms : 0;
    char p[80] = "";
    if (pm) {
        tfn_perms_text(pm, p, sizeof p);
    }
    if (p[0] && k < nfl) {
        snprintf(line, sizeof line, "IT CAN %s", p);
        int k0 = k;
        k = wrap_flow(df, line, fl, nfl, k, sp, &rest);
        for (int i = k0; i < k; i++) {
            flow_line(df, &fl[i], sp[i], false, rest[0] && i == k - 1, THEME_STORE_WARN);
        }
    }
}

// The app page on a round panel: the back mark and the name on the top cap, the facts under them, the icon at the
// left of the first lines, the text across the circle, the buttons on the bottom cap.
static void render_page_round(int64_t now, const lay_t *L, const vitem_t *v)
{
    const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
    const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
    const char *nm = name_of(v);
    char line[112];
    static const kfont_t *const NF[] = {&KF_BIG, &KF_NAME, &KF_TEXT};
    const kfont_t *nf = ui_text_fit(NF, 3, nm, SR(250));
    int cx = gfx_w / 2, nb = SR(66), nw = ui_text_w(nf, nm);
    ui_text_c(nf, cx, nb, nm, THEME_STORE_TEXT);
    back_mark(cx - nw / 2 - SR(30), nb - nf->asc / 2, 18, THEME_STORE_ACCENT);
    if (s_toast_at && now - s_toast_at < 4000) {
        draw_toast(L, SR(320));
    } else {
        facts_of(c, e, line, sizeof line);
        const kfont_t *ff = ui_text_w(&KF_TEXT, line) <= 2 * chord_half(SR(78)) - SR(30) ? &KF_TEXT : &KF_LABEL;
        ui_text_c(ff, cx, SR(96), line, THEME_STORE_TEXT_DIM);
    }
    int is = SR(84), ix = SR(52), iy = SR(114);
    ui_circle(ix + is / 2, iy + is / 2, is * 6 / 10, THEME_STORE_GLOW, 70);
    ui_rbox(ix - 4, iy - 4, is + 8, is + 8, is / 6 + 4, THEME_STORE_SEL, THEME_STORE_SEL_EDGE, 2);
    draw_icon_of(v, ix, iy, is);
    page_text(L, c, e);
    draw_actions(L, v, c, e);
}
#endif

// the page of the selected app (the head comment)
static void render_page(int64_t now, const lay_t *L, const vitem_t *v)
{
#if BOARD_ROUND
    if (L_RND(*L)) {
        render_page_round(now, L, v);
        return;
    }
#endif
    const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
    const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
    const char *nm = name_of(v);
    char line[112];
    // the top: the back mark and the name (a tap on them closes the page), the facts at the right
    back_mark(L->bar ? 12 : 10, L->bar ? 20 : 18, 18, THEME_STORE_ACCENT);
    static const kfont_t *const NF[] = {&KF_BIG, &KF_NAME, &KF_TEXT};
    int nx = L->bar ? 32 : 28;
    const kfont_t *nf = ui_text_fit(NF, 3, nm, L->bar || L->tall ? 300 : 150);
    ui_text(nf, nx, L->bar ? 29 : 27, nm, THEME_STORE_TEXT);
    int tw = nx + ui_text_w(nf, nm) + 12;
    if (s_toast_at && now - s_toast_at < 4000) {
        draw_toast(L, gfx_w - tw - 8);
    } else {
        facts_of(c, e, line, sizeof line);
        int fw = ui_text_w(&KF_LABEL, line);
        if (fw <= gfx_w - tw - 10) {
            ui_text(&KF_LABEL, gfx_w - 10 - fw, L->bar ? 26 : 24, line, THEME_STORE_TEXT_DIM);
        }
    }
    // the icon with a light behind it
    int is = L->tall  ? 112
             : L->bar ? 96
                      : 64,
        ix = L->tall  ? 18
             : L->bar ? 22
                      : 10,
        iy = L->tall  ? 54
             : L->bar ? 50
                      : 44;
    ui_circle(ix + is / 2, iy + is / 2, is * (L->bar ? 7 : 6) / 10, THEME_STORE_GLOW, 70);
    ui_rbox(ix - 4, iy - 4, is + 8, is + 8, is / 6 + 4, THEME_STORE_SEL, THEME_STORE_SEL_EDGE, 2);
    draw_icon_of(v, ix, iy, is);
    // the description, then the permission classes (IT CAN ...), in the flow
    fline_t fl[12];
    span_t sp[12];
    int nfl = page_flow(L, fl, 12), k = 0;
    const char *d = tfn_store_desc(c, s_he), *rest = "";
    const kfont_t *df = L->tall ? &KF_NAME : &KF_LABEL;  // (the Tab5: a bigger text)
    if (d[0]) {
        bool rtl = has_heb(d);
        k = wrap_flow(df, d, fl, nfl, 0, sp, &rest);
        for (int i = 0; i < k; i++) {
            flow_line(df, &fl[i], sp[i], rtl, rest[0] && i == k - 1, THEME_STORE_DESC);
        }
    } else {
        flow_line(df, &fl[0], (span_t){"NO DESCRIPTION IN THE STORE YET", 31}, false, false, THEME_STORE_TEXT_FAINT);
        k = 1;
    }
    uint32_t pm = c ? c->perms : e ? e->perms : 0;
    char p[80] = "";
    if (pm) {
        tfn_perms_text(pm, p, sizeof p);
    }
    if (p[0] && k < nfl) {
        snprintf(line, sizeof line, "IT CAN %s", p);
        int k0 = k;
        k = wrap_flow(df, line, fl, nfl, k, sp, &rest);
        for (int i = k0; i < k; i++) {
            flow_line(df, &fl[i], sp[i], false, rest[0] && i == k - 1, THEME_STORE_WARN);
        }
    }
    draw_actions(L, v, c, e);
}

#if BOARD_ROUND
// the row of a tab on a round panel (the head comment of lay(): the part BOARD_ROUND)
static void render_round(int64_t now, lay_t L)
{
    char line[96], a1[24], a2[24];
    // the tab: its name, the dots of the tabs (the round panels: in the middle of the top cap, the dots under it)
    int tw;
    if (L_RND(L)) {
        mf_text_c(&MF_N24, gfx_w / 2, L.tab.y + 40 * L.tab.h / 70, TAB_NAME[s_tab], THEME_STORE_ACCENT, 255, 1);
        for (int i = 0; i < NT; i++) {
            ui_circle(gfx_w / 2 + (i - NT / 2) * 14, L.tab.y + 56 * L.tab.h / 70, i == s_tab ? 4 : 3,
                      i == s_tab ? THEME_STORE_ACCENT : THEME_STORE_DOT, 255);
        }
        tw = 0;
    } else {
        mf_text(&MF_N24, L.bar ? 14 : 10, L.bar ? 30 : 28, TAB_NAME[s_tab], THEME_STORE_ACCENT, 255, 1);
        tw = mf_width(&MF_N24, TAB_NAME[s_tab], 1) + (L.bar ? 24 : 18);
        for (int i = 0; i < NT; i++) {
            ui_circle(tw + i * 12, L.bar ? 21 : 19, i == s_tab ? 4 : 3,
                      i == s_tab ? THEME_STORE_ACCENT : THEME_STORE_DOT, 255);
        }
    }
    // the space (top right); a short line after an install or a removal takes its place for 4 s
    bool toast_on = s_toast_at && now - s_toast_at < 4000;
    fmt_size(a1, sizeof a1, s_bfree);
    if (s_card) {
        fmt_size(a2, sizeof a2, (uint64_t)s_cfree_kb * 1024);
    }
    snprintf(line, sizeof line, s_card ? "BOARD %s  CARD %s" : "BOARD %s  NO CARD", a1, a2);
    if (ui_text_w(&KF_LABEL, line) > gfx_w - 16 - tw - NT * 12) {  // (the 320 x 240 frame: the dots of the tabs)
        snprintf(line, sizeof line, s_card ? "FREE %s / %s" : "FREE %s", a1, a2);
    }
    if (L_RND(L)) {
        if (!toast_on) {
            ui_text_c(&KF_TEXT, gfx_w / 2, L.tab.y + L.tab.h + 16, line, THEME_STORE_SPACE);
        } else {
            draw_toast(&L, gfx_w * 7 / 10);
        }
    } else if (!toast_on) {
        ui_text(&KF_LABEL, gfx_w - 10 - ui_text_w(&KF_LABEL, line), L.bar ? 26 : 24, line, THEME_STORE_SPACE);
    } else {
        draw_toast(&L, gfx_w - tw - NT * 12 - 16);
    }
    // the state of the store
    if (s_cstate != 1) {
        const char *t1 = s_cstate == 0 ? "LOADING THE STORE..." : "THE STORE IS NOT REACHABLE";
        int cx = gfx_w / 2, cy = gfx_h / 2;
        ui_text_c(&KF_BIG, cx, cy - 4, t1, THEME_STORE_STATE);
        if (s_cstate == -1) {
            ui_text_c(&KF_LABEL, cx, cy + 18, s_cerr[0] ? s_cerr : "CONNECT TO YOUR WIFI OR THE VPN",
                      THEME_STORE_STATE_DIM);
            box_t b = L.b1;
            if (!L.bar && !L.tall && !L_RND(L)) {
                b = (box_t){gfx_w / 2 - 80, 186, 160, 46};  // (the Tab5, the round panels: at L.b1, where the tap goes)
            }
            button(&b, "TRY AGAIN", true, true);
        } else {
            for (int i = 0; i < 8; i++) {
                float a = now / 160.0f + i * 0.785f;
                ui_circle(cx + (int)(18 * cosf(a)), cy + 34 + (int)(18 * sinf(a)), 3, THEME_STORE_ACCENT, 40 + i * 26);
            }
        }
        return;
    }
    if (!s_nview) {
        const char *t = s_tab == T_UPD    ? "ALL APPS ARE NEW"
                        : s_tab == T_INST ? "NO INSTALLED APPS YET"
                        : s_tab == T_FOR  ? "NOTHING NEW FOR YOU"
                                          : "NO APPS HERE";
        ui_text_c(&KF_BIG, gfx_w / 2, gfx_h / 2 + 6, t, THEME_STORE_EMPTY);
        ui_text_c(&KF_LABEL, gfx_w / 2, gfx_h / 2 + 30, "SWIPE UP OR DOWN FOR THE OTHER TABS", THEME_STORE_TEXT_FAINT);
    } else {
        // the row of icons: the far ones first, the selected one big with a light behind it
        int sel = s_sel[s_tab];
        int order[8], n = 0;
        for (int i = 0; i < s_nview && n < 8; i++) {
            if (fabsf(i - s_pos) < 3.2f) {
                order[n++] = i;
            }
        }
        for (int a = 1; a < n; a++) {
            int v = order[a], j = a - 1;
            while (j >= 0 && fabsf(order[j] - s_pos) < fabsf(v - s_pos)) {
                order[j + 1] = order[j];
                j--;
            }
            order[j + 1] = v;
        }
        ui_circle(L.row_cx, L.row_cy, L.big * 7 / 10, THEME_STORE_GLOW, 70);
        for (int k = 0; k < n; k++) {
            int i = order[k];
            float d = i - s_pos, ad = fabsf(d);
            int s = (int)(L.big - (L.big - L.small) * (ad < 1 ? ad : 1));
            int cx = L.row_cx + (int)(d * L.gap);
            int x = cx - s / 2, y = L.row_cy - s / 2;
            if (L.bar && x + s > L.panel.x - 6) {
                continue;
            }
            if (ad < 0.5f) {
                ui_rbox(x - 4, y - 4, s + 8, s + 8, s / 6 + 4, THEME_STORE_SEL, THEME_STORE_SEL_EDGE, 2);
            }
            draw_icon_of(&s_view[i], x, y, s);
            if (ad > 0.6f) {
                gfx_darken_rect(x, y, s, s, 1);
            }
            const tfn_entry_t *e = s_view[i].inst >= 0 ? tfn_entry(s_view[i].inst) : NULL;
            if (e) {
                ui_circle(x + s - 6, y + s - 6, 6,
                          e->place == TFN_CARD ? THEME_STORE_PLACE_CARD : THEME_STORE_PLACE_BOARD, 255);
            }
        }
        // the details of the selected item
        const vitem_t *v = &s_view[sel < s_nview ? sel : 0];
        const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
        const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
        if (L.bar) {
            ui_rbox(L.panel.x, L.panel.y, L.panel.w, L.panel.h, 14, THEME_STORE_PANEL_BG, THEME_STORE_PANEL_EDGE, 1);
        }
        const char *nm = name_of(v);
        static const kfont_t *const NF[] = {&KF_BIG, &KF_NAME, &KF_TEXT}, *const NFT[] = {&KF_TITLE, &KF_BIG, &KF_NAME};
        const kfont_t *nf =
                ui_text_fit(L.tall ? NFT : NF, 3, nm, L.bar ? L.panel.w - 46 : gfx_w - 64);  // (room for the mark i)
        if (L.bar) {
            ui_text(nf, L.name_x, L.name_y, nm, THEME_STORE_TEXT);
        } else {
            ui_text_c(nf, L.name_x, L.name_y, nm, THEME_STORE_TEXT);
        }
        facts_of(c, e, line, sizeof line);
        if (L.bar) {
            ui_text(&KF_LABEL, L.name_x, L.info_y, line, THEME_STORE_TEXT_DIM);
        } else if (L_RND(L)) {
            ui_text_c(ui_text_w(&KF_TEXT, line) <= gfx_w - 60 ? &KF_TEXT : &KF_LABEL, L.name_x, L.info_y, line,
                      THEME_STORE_TEXT_DIM);
        } else {
            ui_text_c(L.tall ? &KF_NAME : &KF_LABEL, L.name_x, L.info_y, line, THEME_STORE_TEXT_DIM);
        }
        // the mark of the app page (a tap on the name or on the icon opens it)
        int mx = L.bar ? L.panel.x + L.panel.w - 18 : gfx_w - 18, my = L.bar ? L.panel.y + 17 : L.name_y - 6;
        if (L_RND(L)) {
            mx = L.name_x + ui_text_w(nf, nm) / 2 + 22;  // (the round panels: at the end of the name)
        }
        ui_circle(mx, my, 10, THEME_STORE_MARK, 255);
        ui_text_c(&KF_NAME, mx, my + 6, "i", THEME_STORE_MARK_TEXT);
        draw_actions(&L, v, c, e);
        if (L.bar) {
            ui_text_c(&KF_LABEL, L.row_cx, L.sel_name_y, nm, THEME_STORE_SEL_NAME);
        }
    }
}
#endif

static void render(int64_t now)
{
    lay_t L = lay();
    background();
    char line[96], a1[24], a2[24];
    if (s_page[0] && s_cstate == 1 && s_nview && s_sel[s_tab] < s_nview) {
        render_page(now, &L, &s_view[s_sel[s_tab]]);
        return;
    }
#if BOARD_ROUND
    if (L_RND(L)) {
        render_round(now, L);
        return;
    }
#endif
    // the tab: its name, the dots of the tabs
    mf_text(&MF_N24, L.bar ? 14 : 10, L.bar ? 30 : 28, TAB_NAME[s_tab], THEME_STORE_ACCENT, 255, 1);
    int tw = mf_width(&MF_N24, TAB_NAME[s_tab], 1) + (L.bar ? 24 : 18);
    for (int i = 0; i < NT; i++) {
        ui_circle(tw + i * 12, L.bar ? 21 : 19, i == s_tab ? 4 : 3, i == s_tab ? THEME_STORE_ACCENT : THEME_STORE_DOT,
                  255);
    }
    // the space (top right); a short line after an install or a removal takes its place for 4 s
    bool toast_on = s_toast_at && now - s_toast_at < 4000;
    fmt_size(a1, sizeof a1, s_bfree);
    if (s_card) {
        fmt_size(a2, sizeof a2, (uint64_t)s_cfree_kb * 1024);
    }
    snprintf(line, sizeof line, s_card ? "BOARD %s  CARD %s" : "BOARD %s  NO CARD", a1, a2);
    if (ui_text_w(&KF_LABEL, line) > gfx_w - 16 - tw - NT * 12) {  // (the 320 x 240 frame: the dots of the tabs)
        snprintf(line, sizeof line, s_card ? "FREE %s / %s" : "FREE %s", a1, a2);
    }
    if (!toast_on) {
        ui_text(&KF_LABEL, gfx_w - 10 - ui_text_w(&KF_LABEL, line), L.bar ? 26 : 24, line, THEME_STORE_SPACE);
    } else {
        draw_toast(&L, gfx_w - tw - NT * 12 - 16);
    }
    // the state of the store
    if (s_cstate != 1) {
        const char *t1 = s_cstate == 0 ? "LOADING THE STORE..." : "THE STORE IS NOT REACHABLE";
        int cx = gfx_w / 2, cy = gfx_h / 2;
        ui_text_c(&KF_BIG, cx, cy - 4, t1, THEME_STORE_STATE);
        if (s_cstate == -1) {
            ui_text_c(&KF_LABEL, cx, cy + 18, s_cerr[0] ? s_cerr : "CONNECT TO YOUR WIFI OR THE VPN",
                      THEME_STORE_STATE_DIM);
            box_t b = L.b1;
            if (!L.bar && !L.tall) {
                b = (box_t){gfx_w / 2 - 80, 186, 160, 46};  // (the Tab5: at L.b1, where the tap goes)
            }
            button(&b, "TRY AGAIN", true, true);
        } else {
            for (int i = 0; i < 8; i++) {
                float a = now / 160.0f + i * 0.785f;
                ui_circle(cx + (int)(18 * cosf(a)), cy + 34 + (int)(18 * sinf(a)), 3, THEME_STORE_ACCENT, 40 + i * 26);
            }
        }
        return;
    }
    if (!s_nview) {
        const char *t = s_tab == T_UPD    ? "ALL APPS ARE NEW"
                        : s_tab == T_INST ? "NO INSTALLED APPS YET"
                        : s_tab == T_FOR  ? "NOTHING NEW FOR YOU"
                                          : "NO APPS HERE";
        ui_text_c(&KF_BIG, gfx_w / 2, gfx_h / 2 + 6, t, THEME_STORE_EMPTY);
        ui_text_c(&KF_LABEL, gfx_w / 2, gfx_h / 2 + 30, "SWIPE UP OR DOWN FOR THE OTHER TABS", THEME_STORE_TEXT_FAINT);
    } else {
        // the row of icons: the far ones first, the selected one big with a light behind it
        int sel = s_sel[s_tab];
        int order[8], n = 0;
        for (int i = 0; i < s_nview && n < 8; i++) {
            if (fabsf(i - s_pos) < 3.2f) {
                order[n++] = i;
            }
        }
        for (int a = 1; a < n; a++) {
            int v = order[a], j = a - 1;
            while (j >= 0 && fabsf(order[j] - s_pos) < fabsf(v - s_pos)) {
                order[j + 1] = order[j];
                j--;
            }
            order[j + 1] = v;
        }
        ui_circle(L.row_cx, L.row_cy, L.big * 7 / 10, THEME_STORE_GLOW, 70);
        for (int k = 0; k < n; k++) {
            int i = order[k];
            float d = i - s_pos, ad = fabsf(d);
            int s = (int)(L.big - (L.big - L.small) * (ad < 1 ? ad : 1));
            int cx = L.row_cx + (int)(d * L.gap);
            int x = cx - s / 2, y = L.row_cy - s / 2;
            if (L.bar && x + s > L.panel.x - 6) {
                continue;
            }
            if (ad < 0.5f) {
                ui_rbox(x - 4, y - 4, s + 8, s + 8, s / 6 + 4, THEME_STORE_SEL, THEME_STORE_SEL_EDGE, 2);
            }
            draw_icon_of(&s_view[i], x, y, s);
            if (ad > 0.6f) {
                gfx_darken_rect(x, y, s, s, 1);
            }
            const tfn_entry_t *e = s_view[i].inst >= 0 ? tfn_entry(s_view[i].inst) : NULL;
            if (e) {
                ui_circle(x + s - 6, y + s - 6, 6,
                          e->place == TFN_CARD ? THEME_STORE_PLACE_CARD : THEME_STORE_PLACE_BOARD, 255);
            }
        }
        // the details of the selected item
        const vitem_t *v = &s_view[sel < s_nview ? sel : 0];
        const tfn_cat_t *c = v->cat >= 0 ? &s_cat[v->cat].c : NULL;
        const tfn_entry_t *e = v->inst >= 0 ? tfn_entry(v->inst) : NULL;
        if (L.bar) {
            ui_rbox(L.panel.x, L.panel.y, L.panel.w, L.panel.h, 14, THEME_STORE_PANEL_BG, THEME_STORE_PANEL_EDGE, 1);
        }
        const char *nm = name_of(v);
        static const kfont_t *const NF[] = {&KF_BIG, &KF_NAME, &KF_TEXT}, *const NFT[] = {&KF_TITLE, &KF_BIG, &KF_NAME};
        const kfont_t *nf =
                ui_text_fit(L.tall ? NFT : NF, 3, nm, L.bar ? L.panel.w - 46 : gfx_w - 64);  // (room for the mark i)
        if (L.bar) {
            ui_text(nf, L.name_x, L.name_y, nm, THEME_STORE_TEXT);
        } else {
            ui_text_c(nf, L.name_x, L.name_y, nm, THEME_STORE_TEXT);
        }
        facts_of(c, e, line, sizeof line);
        if (L.bar) {
            ui_text(&KF_LABEL, L.name_x, L.info_y, line, THEME_STORE_TEXT_DIM);
        } else {
            ui_text_c(L.tall ? &KF_NAME : &KF_LABEL, L.name_x, L.info_y, line, THEME_STORE_TEXT_DIM);
        }
        // the mark of the app page (a tap on the name or on the icon opens it)
        int mx = L.bar ? L.panel.x + L.panel.w - 18 : gfx_w - 18, my = L.bar ? L.panel.y + 17 : L.name_y - 6;
        ui_circle(mx, my, 10, THEME_STORE_MARK, 255);
        ui_text_c(&KF_NAME, mx, my + 6, "i", THEME_STORE_MARK_TEXT);
        draw_actions(&L, v, c, e);
        if (L.bar) {
            ui_text_c(&KF_LABEL, L.row_cx, L.sel_name_y, nm, THEME_STORE_SEL_NAME);
        }
    }
}

#include "../libs/tficon/tficon.h"
// the menu icon: an app tile drops into a shopping bag; the bag gives a small bounce and its star shines
static void icon(int x, int y, int s)
{
    tfi_begin(x, y, s);
    tfi_tile(x, y, s, tfi_hex(0xb46bff), tfi_hex(0x4a1aa8));
    float u = s / 100.0f, ph = tfi_ph(2);
    float fall = tfi_step(0.0f, 0.42f, ph), bo = ph > 0.42f && ph < 0.72f ? fsin((ph - 0.42f) / 0.3f * 3.14159f) : 0;
    int bw = (int)(56 * u), bh = (int)(46 * u * (1 - 0.07f * bo)), bx = x + (int)(22 * u), by = y + (int)(86 * u) - bh;
    // the tile (behind the front of the bag)
    if (ph < 0.46f) {
        float ty = y + (6 + fall * 38) * u, tz = 20 * u;
        tfi_rbox((int)(x + 50 * u - tz / 2), (int)ty, (int)tz, (int)tz, (int)(5 * u), tfi_hex(0x7dffb3),
                 tfi_hex(0x0fb45c), 256);
        tfi_rbox((int)(x + 50 * u - tz / 2 + 2 * u), (int)(ty + 2 * u), (int)(tz - 4 * u), (int)(6 * u), (int)(3 * u),
                 rgb(255, 255, 255), rgb(255, 255, 255), 90);
    }
    // the handle, the shadow, the body, the opening
    tfi_arc(x + 50 * u, by + 1 * u, 13 * u, 4.4f * u, 3.14159f, 6.2831f, tfi_hex(0xffe3a6), 256);
    tfi_drop(bx, by, bw, bh, (int)(8 * u), (int)(3 * u), 70);
    tfi_gloss_box(bx, by, bw, bh, (int)(8 * u), tfi_hex(0xffd36b), tfi_hex(0xff7d10));
    tfd_rect(bx + (int)(5 * u), by + (int)(4 * u), bw - (int)(10 * u), (int)(2.4f * u) > 1 ? (int)(2.4f * u) : 1,
             tfi_hex(0xa84800), 150);
    // the star of the bag shines after the drop
    float sh = ph > 0.42f ? 1 - tfi_step(0.5f, 1.0f, ph) : 0;
    float sx = x + 50 * u, sy = by + bh * 0.6f, st[20];
    for (int k = 0; k < 10; k++) {
        float a = -1.5708f + k * 0.62832f, rr = (k & 1 ? 4.6f : 11 * (1 + 0.18f * sh)) * u;
        st[k * 2] = sx + fcos(a) * rr;
        st[k * 2 + 1] = sy + fsin(a) * rr;
    }
    tfd_poly(st, 10, tfd_mix(tfi_hex(0xfff6dc), rgb(255, 255, 255), (int)(255 * sh)), 256);
    if (sh > 0.05f) {
        tfd_glow(sx, sy, 20 * u, tfi_hex(0xfff0b0), (int)(130 * sh));
    }
    tfi_end();
}

const app_t app_store = {
        .name = "STORE",
        .landscape = true,
        .enter = enter,
        .leave = leave,
        .input = input,
        .update = update,
        .render = render,
        .draw_icon = icon,
        .round_fit = !BOARD_ROUND,  // (a round panel: the own layout, APP_ROUND_HI)
        .round = BOARD_ROUND ? APP_ROUND_HI : 0,
};
