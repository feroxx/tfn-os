// TFN OS: the static store on the board (tfn_sstore.h): the setting of the source, the HTTPS requests, the catalog,
// the install and the icons. main/tfn_store.c calls it when the static store is the source of this board.
//
// The HTTPS requests run in a short task with its stack in PSRAM (the TLS handshake needs a big stack; the store
// worker and the console keep their own stacks). One task gets all files of one step on one connection; the caller
// waits, then checks the files and writes them (no flash write from a task with a PSRAM stack). All buffers and the
// state of this file are in PSRAM (the "psram" list of main/apps.json): a board that uses the manager store has the
// same internal RAM.
#include "tfn_app_priv.h"
#include "esp_http_client.h"
#include "esp_crt_bundle.h"  // (after esp_http_client.h: it needs the mbedTLS types)
#include "power.h"
#include "tfn_sstore.h"
#include "wifi.h"

static const char *TAG = "tfn_sstore";

#define SS_NS        "tfn"
#define SS_KEY_MODE  "ssrc"
#define SS_KEY_URL   "surl"
#define SS_STACK     10240              // the stack of the HTTPS task (PSRAM)
#define SS_FIRST_BUF (32 * 1024)        // the first size of a buffer that grows (index.json)
#define SS_TIMEOUT   10000              // the network timeout of one request, ms
#define SS_WAIT_MS   25                 // the step of the wait for the HTTPS task
#define SS_URL_MAX   (TFN_SS_URL + 64)  // a URL of a file: the store URL and apps/<id>/<kind>/<file>
#define SS_DL_PCT    95                 // the part of the progress for the download (the rest: the install)

// one GET into a buffer in PSRAM
typedef struct {
    const char *url;
    uint8_t *buf;
    size_t cap, max, got;
    bool grow, over;
    int code;
    esp_err_t err;
} ss_get_t;

typedef struct {
    ss_get_t *g;
    int n;
    volatile bool done;
} ss_job_t;

// (all in PSRAM: the "psram" list of main/apps.json)
static struct {
    bool loaded;
    uint8_t mode;
    char url[TFN_SS_URL];
    tfn_ss_pkg_t *pkg;  // PSRAM, TFN_CAT_MAX places: the files of the packages of the last catalog
    int npkg;
    SemaphoreHandle_t lk;               // made at the first use of the static store
    char u[TFN_SS_NFILES][SS_URL_MAX];  // the URLs of one step
    tfn_pub_list_t keys;                // a copy of the added keys for one check
} s_ss;

// ---------------------------------------------------------------- the setting
static void ss_load(void)
{
    if (s_ss.loaded) {
        return;
    }
    s_ss.mode = TFN_STORE_SOURCE_DEFAULT >= TFN_SS_AUTO && TFN_STORE_SOURCE_DEFAULT <= TFN_SS_STATIC
                        ? TFN_STORE_SOURCE_DEFAULT
                        : TFN_SS_AUTO;
    snprintf(s_ss.url, sizeof s_ss.url, "%s", TFN_STATIC_STORE_URL);
    nvs_handle_t h;
    if (nvs_open(SS_NS, NVS_READONLY, &h) == ESP_OK) {
        uint8_t m = 0;
        char u[TFN_SS_URL];
        size_t n = sizeof u;
        if (nvs_get_u8(h, SS_KEY_MODE, &m) == ESP_OK && m <= TFN_SS_STATIC) {
            s_ss.mode = m;
        }
        if (nvs_get_str(h, SS_KEY_URL, u, &n) == ESP_OK && tfn_ss_url_ok(u)) {
            snprintf(s_ss.url, sizeof s_ss.url, "%s", u);
        }
        nvs_close(h);
    }
    s_ss.loaded = true;
}

int tfn_sstore_mode(void)
{
    ss_load();
    return s_ss.mode;
}

const char *tfn_sstore_url(void)
{
    ss_load();
    return s_ss.url;
}

bool tfn_sstore_active(void)
{
    ss_load();
    return s_ss.mode == TFN_SS_STATIC || (s_ss.mode == TFN_SS_AUTO && !tfn_store_configured());
}

bool tfn_sstore_set(int mode, const char *url, char *msg, int len)
{
    ss_load();
    bool def = !url || !url[0];
    if (mode < TFN_SS_AUTO || mode > TFN_SS_STATIC) {
        snprintf(msg, len, "the source is auto, mgr or static");
        return false;
    }
    if (!def && !tfn_ss_url_ok(url)) {
        snprintf(msg, len, "the store URL starts with https:// (%d letters at most)", TFN_SS_URL - 2);
        return false;
    }
    nvs_handle_t h;
    if (nvs_open(SS_NS, NVS_READWRITE, &h) != ESP_OK) {
        snprintf(msg, len, "cannot write the setting");
        return false;
    }
    bool ok = nvs_set_u8(h, SS_KEY_MODE, (uint8_t)mode) == ESP_OK;
    if (def) {
        nvs_erase_key(h, SS_KEY_URL);
    } else {
        ok = ok && nvs_set_str(h, SS_KEY_URL, url) == ESP_OK;
    }
    ok = ok && nvs_commit(h) == ESP_OK;
    nvs_close(h);
    s_ss.mode = (uint8_t)mode;
    snprintf(s_ss.url, sizeof s_ss.url, "%s", def ? TFN_STATIC_STORE_URL : url);
    snprintf(msg, len, "%s", ok ? "saved" : "not saved");
    return ok;
}

// ---------------------------------------------------------------- the hash, the signature, the keys
static void ss_sha256(const void *d, size_t n, uint8_t out[32])
{
    size_t ol = 0;
    if (psa_hash_compute(PSA_ALG_SHA_256, d, n, out, 32, &ol) != PSA_SUCCESS) {
        memset(out, 0, 32);
    }
}

// a signature (r || s) of msg by the key pk (no cache: the index changes at each release)
static bool ss_verify(const uint8_t pk[TFN_PUB_PK], const uint8_t *msg, size_t n, const uint8_t sig[64])
{
    psa_key_attributes_t at = PSA_KEY_ATTRIBUTES_INIT;
    psa_set_key_type(&at, PSA_KEY_TYPE_ECC_PUBLIC_KEY(PSA_ECC_FAMILY_SECP_R1));
    psa_set_key_bits(&at, 256);
    psa_set_key_usage_flags(&at, PSA_KEY_USAGE_VERIFY_MESSAGE);
    psa_set_key_algorithm(&at, PSA_ALG_ECDSA(PSA_ALG_SHA_256));
    psa_key_id_t k = 0;
    if (psa_import_key(&at, pk, TFN_PUB_PK, &k) != PSA_SUCCESS) {
        return false;
    }
    power_idle1_hold(true);
    psa_status_t st = psa_verify_message(k, PSA_ALG_ECDSA(PSA_ALG_SHA_256), msg, n, sig, 64);
    power_idle1_hold(false);
    psa_destroy_key(k);
    return st == PSA_SUCCESS;
}

static void ss_ops(tfn_pub_ops_t *o)
{
    memset(o, 0, sizeof *o);
    o->sha256 = ss_sha256;
    o->verify = ss_verify;
    for (int i = 0; i < TFN_PUB_BUILTIN; i++) {
        o->builtin[i] = tfa_builtin_key(i);
    }
}

static void ss_lock(void)
{
    if (!s_ss.lk) {
        s_ss.lk = xSemaphoreCreateMutex();
    }
    if (s_ss.lk) {
        xSemaphoreTake(s_ss.lk, portMAX_DELAY);
    }
}

static void ss_unlock(void)
{
    if (s_ss.lk) {
        xSemaphoreGive(s_ss.lk);
    }
}

static void *ss_alloc(size_t n)
{
    return heap_caps_malloc(n, MALLOC_CAP_SPIRAM);
}

// ---------------------------------------------------------------- HTTPS
static esp_err_t ss_on_data(esp_http_client_event_t *ev)
{
    ss_get_t *g = ev->user_data;
    // (only the body of the last answer: a redirect has a body too)
    if (ev->event_id != HTTP_EVENT_ON_DATA || !g || esp_http_client_get_status_code(ev->client) != 200) {
        return ESP_OK;
    }
    size_t need = g->got + (size_t)ev->data_len;
    if (g->over || need > g->max) {
        g->over = true;
        return ESP_OK;
    }
    if (need > g->cap) {
        size_t cap = g->cap ? g->cap : SS_FIRST_BUF;
        while (cap < need) {
            cap *= 2;
        }
        cap = cap > g->max ? g->max : cap;
        uint8_t *b = g->grow ? heap_caps_realloc(g->buf, cap, MALLOC_CAP_SPIRAM) : NULL;
        if (!b) {
            g->over = true;
            return ESP_OK;
        }
        g->buf = b;
        g->cap = cap;
    }
    memcpy(g->buf + g->got, ev->data, (size_t)ev->data_len);
    g->got = need;
    return ESP_OK;
}

// the task: each GET of the job on one connection (a GET with no URL is not done)
static void ss_task(void *arg)
{
    ss_job_t *job = arg;
    int first = 0;
    while (first < job->n - 1 && !job->g[first].url) {
        first++;
    }
    esp_http_client_config_t c = {
            .url = job->g[first].url,
            .event_handler = ss_on_data,
            .user_data = &job->g[first],
            .timeout_ms = SS_TIMEOUT,
            .crt_bundle_attach = esp_crt_bundle_attach,
            .buffer_size = 4096,  // (2 KB or more: malloc puts them in the PSRAM)
            .buffer_size_tx = 2048,
            .keep_alive_enable = true,
            .user_agent = "TFN OS",
    };
    esp_http_client_handle_t h = c.url ? esp_http_client_init(&c) : NULL;
    for (int i = first; i < job->n; i++) {
        ss_get_t *g = &job->g[i];
        if (!g->url) {
            continue;
        }
        if (!h) {
            g->err = ESP_ERR_NO_MEM;
            continue;
        }
        if (i != first) {
            vTaskDelay(1);
            esp_http_client_set_url(h, g->url);
            esp_http_client_set_user_data(h, g);
        }
        g->err = esp_http_client_perform(h);
        g->code = esp_http_client_get_status_code(h);
    }
    if (h) {
        esp_http_client_cleanup(h);
    }
    job->done = true;
    vTaskDeleteWithCaps(NULL);  // (a task of xTaskCreatePinnedToCoreWithCaps: vTaskDelete would keep its stack)
}

// run the GETs of a job and wait for them; progress (can be NULL) gets 0 .. SS_DL_PCT of total bytes
static void ss_run(ss_get_t *g, int n, size_t total, void (*progress)(int))
{
    ss_job_t job = {.g = g, .n = n};
    power_idle1_hold(true);
    if (xTaskCreatePinnedToCoreWithCaps(ss_task, "sstore", SS_STACK, &job, 2, NULL, 1,
                                        MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT) != pdPASS) {
        power_idle1_hold(false);
        for (int i = 0; i < n; i++) {
            g[i].err = ESP_ERR_NO_MEM;
        }
        return;
    }
    while (!job.done) {
        vTaskDelay(pdMS_TO_TICKS(SS_WAIT_MS));
        size_t got = 0;
        for (int i = 0; i < n; i++) {
            got += g[i].got;
        }
        if (progress && total) {
            progress((int)((uint64_t)got * SS_DL_PCT / total));
        }
    }
    power_idle1_hold(false);
}

// the fault of one GET into msg; true = good (a GET with no URL is good)
static bool ss_got(const ss_get_t *g, char *msg, int len)
{
    if (!g->url) {
        return true;
    }
    if (g->err != ESP_OK) {
        snprintf(msg, len, "THE STORE IS NOT REACHABLE (%s)", esp_err_to_name(g->err));
    } else if (g->code != 200) {
        snprintf(msg, len, "THE STORE ANSWERS %d", g->code);
    } else if (g->over) {
        snprintf(msg, len, "A FILE OF THE STORE IS TOO BIG (OR NO MEMORY)");
    } else {
        return true;
    }
    ESP_LOGW(TAG, "%s: %s", g->url, msg);
    return false;
}

// ---------------------------------------------------------------- the catalog
static bool ss_index_key(const uint8_t *idx, size_t n, const ss_get_t *sig, uint8_t pk[TFN_PUB_PK], char *msg, int len)
{
    tfn_pub_ops_t o;
    char who[TFN_PUB_NAME], idt[20];
    uint8_t id[TFN_PUB_ID];
    ss_ops(&o);
    s_ss.keys.n = 0;
    for (int i = 0; i < tfn_pub_count() && s_ss.keys.n < TFN_PUB_MAX; i++) {
        s_ss.keys.n += tfn_pub_get(i, &s_ss.keys.e[s_ss.keys.n]);
    }
    int r = tfn_ss_index_key(&o, &s_ss.keys, idx, n, sig->buf, sig->got, pk, who);
    if (r == TFN_PUB_NONE) {
        snprintf(msg, len, "THE STORE INDEX HAS NO SIGNATURE OF A TRUSTED STORE KEY");
        return false;
    }
    tfn_pub_key_id(&o, pk, id);
    tfn_pub_id_text(id, idt);
    ESP_LOGI(TAG, "the index of %s: key %s (%s)", s_ss.url, idt, r == TFN_PUB_OK_BUILTIN ? "built-in" : who);
    return true;
}

static int ss_catalog_locked(tfn_cat_t *out, int max, char *msg, int len)
{
    ss_get_t g[2] = {{.url = s_ss.u[0], .max = TFN_SS_INDEX_MAX, .grow = true}, {.url = s_ss.u[1], .max = 64}};
    tfn_ss_opts_t op = {
            .kind = tfn_kind(), .abi = tfn_abi(), .rev = tfn_abi_rev(), .alloc = ss_alloc, .perms = tfn_perms_parse};
    uint8_t pk[TFN_PUB_PK];
    int n = -1;
    if (!tfn_ss_url_ok(s_ss.url) || !tfn_ss_join(s_ss.u[0], SS_URL_MAX, s_ss.url, "index.json") ||
        !tfn_ss_join(s_ss.u[1], SS_URL_MAX, s_ss.url, "index.sig")) {
        snprintf(msg, len, "THE STORE URL IS NOT GOOD");
        return -1;
    }
    g[1].buf = heap_caps_malloc(64, MALLOC_CAP_SPIRAM);
    g[1].cap = g[1].buf ? 64 : 0;
    tfn_ss_pkg_t *pkg = heap_caps_calloc(max > 0 ? max : 1, sizeof *pkg, MALLOC_CAP_SPIRAM);
    if (g[1].buf && pkg) {
        ss_run(g, 2, 0, NULL);
        if (ss_got(&g[0], msg, len) && ss_got(&g[1], msg, len) &&
            ss_index_key(g[0].buf, g[0].got, &g[1], pk, msg, len)) {
            n = tfn_ss_parse((char *)g[0].buf, g[0].got, &op, pk, out, pkg, max, msg, len);
        }
    } else {
        snprintf(msg, len, "no memory");
    }
    free(g[0].buf);
    free(g[1].buf);
    if (n < 0) {
        free(pkg);
        return -1;
    }
    free(s_ss.pkg);
    s_ss.pkg = pkg;
    s_ss.npkg = n;
    ESP_LOGI(TAG, "the static store: %d apps for %s %s", n, op.kind, msg);
    return n;
}

int tfn_sstore_catalog(tfn_cat_t *out, int max, char *msg, int len)
{
    msg[0] = 0;
    if (wifi_state() != WIFI_CONNECTED) {
        snprintf(msg, len, "NO WIFI");
        return -1;
    }
    ss_load();
    ss_lock();
    int n = ss_catalog_locked(out, max, msg, len);
    ss_unlock();
    return n;
}

// the files of a package of the last catalog (s_ss.lk held)
static bool ss_find(const char *id, tfn_ss_pkg_t *p)
{
    for (int i = 0; s_ss.pkg && i < s_ss.npkg; i++) {
        if (!strcmp(s_ss.pkg[i].id, id)) {
            *p = s_ss.pkg[i];
            return true;
        }
    }
    return false;
}

// ---------------------------------------------------------------- the install and the icons
// the files of the upload folder tmp; with the folder too when gone is true
static void ss_tmp_clear(const char *tmp, bool gone)
{
    static const char *const ALL[] = TFN_APP_FILES;
    char fn[72];
    for (int i = 0; i < TFN_APP_NFILES; i++) {
        snprintf(fn, sizeof fn, "%s/%s", tmp, ALL[i]);
        remove(fn);
    }
    if (gone) {
        rmdir(tmp);
    }
}

// the files of the package into the folder tmp (empty first); false = a fault (msg), and the folder is gone
static bool ss_write(const char *tmp, const ss_get_t *g, const tfn_ss_pkg_t *p, bool card, char *msg, int len)
{
    char fn[72];
    ss_tmp_clear(tmp, false);  // (the files of an install that did not end)
    for (int i = 0; i < TFN_SS_NFILES; i++) {
        if (!p->f[i].size) {
            continue;
        }
        snprintf(fn, sizeof fn, "%s/%s", tmp, tfn_ss_file_name(i));
        FILE *f = fopen(fn, "wb");
        bool ok = f && fwrite(g[i].buf, 1, g[i].got, f) == g[i].got;
        if (f && fclose(f)) {
            ok = false;
        }
        if (!ok) {
            snprintf(msg, len, "cannot write %s (full?)", card ? "the card" : "the board");
            ss_tmp_clear(tmp, true);  // (the files of an install that did not end would take the free space)
            return false;
        }
    }
    return true;
}

// get the files of a package (the buffers in g) and check each one against the index
static bool ss_fetch_pkg(const tfn_ss_pkg_t *p, ss_get_t *g, void (*progress)(int), char *msg, int len)
{
    tfn_pub_ops_t o;
    size_t total = 0;
    ss_ops(&o);
    for (int i = 0; i < TFN_SS_NFILES; i++) {
        char rel[72];
        if (!p->f[i].size) {
            continue;
        }
        snprintf(rel, sizeof rel, "apps/%s/%s/%s", p->id, tfn_kind(), tfn_ss_file_name(i));
        g[i].buf = heap_caps_malloc(p->f[i].size, MALLOC_CAP_SPIRAM);
        if (!g[i].buf || !tfn_ss_join(s_ss.u[i], SS_URL_MAX, s_ss.url, rel)) {
            snprintf(msg, len, "no memory");
            return false;
        }
        g[i].url = s_ss.u[i];
        g[i].cap = g[i].max = p->f[i].size;
        total += p->f[i].size;
    }
    ss_run(g, TFN_SS_NFILES, total, progress);
    for (int i = 0; i < TFN_SS_NFILES; i++) {
        if (!ss_got(&g[i], msg, len)) {
            return false;
        }
    }
    for (int i = 0; i < TFN_SS_NFILES; i++) {
        if (p->f[i].size && !tfn_ss_file_ok(&o, &p->f[i], g[i].buf, g[i].got)) {
            snprintf(msg, len, "%s OF %s IS NOT THE FILE OF THE STORE INDEX", tfn_ss_file_name(i), p->id);
            return false;
        }
    }
    return true;
}

// the package of id from the last catalog, or from a new catalog
static bool ss_pkg_of(const char *id, tfn_ss_pkg_t *p, char *msg, int len)
{
    if (ss_find(id, p)) {
        return true;
    }
    tfn_cat_t *cat = heap_caps_calloc(TFN_CAT_MAX, sizeof *cat, MALLOC_CAP_SPIRAM);
    int n = cat ? ss_catalog_locked(cat, TFN_CAT_MAX, msg, len) : -1;
    if (n > 0) {
        tfn_store_cat_free(cat, n);
    }
    free(cat);
    if (n < 0) {
        return false;
    }
    if (!ss_find(id, p)) {
        snprintf(msg, len, "%s is not in the store for this board", id);
        return false;
    }
    return true;
}

bool tfn_sstore_install(const char *id, int place, void (*progress)(int pct), char *msg, int len)
{
    const char *root = place == TFN_CARD ? TFN_CARD_DIR : TFN_DATA_DIR;
    ss_get_t g[TFN_SS_NFILES];
    tfn_ss_pkg_t p;
    char tmp[48];
    bool ok = false;
    msg[0] = 0;
    memset(g, 0, sizeof g);
    if (wifi_state() != WIFI_CONNECTED) {
        snprintf(msg, len, "NO WIFI");
        return false;
    }
    ss_load();
    ss_lock();
    if (ss_pkg_of(id, &p, msg, len) && ss_fetch_pkg(&p, g, progress, msg, len)) {
        mkdir(root, 0777);
        snprintf(tmp, sizeof tmp, "%s/" TFN_TMP_STORE "%s", root, id);
        mkdir(tmp, 0777);
        ok = ss_write(tmp, g, &p, place == TFN_CARD, msg, len);
    }
    ss_unlock();
    for (int i = 0; i < TFN_SS_NFILES; i++) {
        free(g[i].buf);
    }
    if (!ok) {
        return false;
    }
    if (progress) {
        progress(SS_DL_PCT);
    }
    ok = tfn_install(tmp, place, msg, len);
    if (!ok) {
        tfn_tmp_drop(tmp);  // (a download that the install refused takes no space)
    }
    return ok;
}

bool tfn_sstore_get(const char *rel, uint8_t **buf, size_t *n, size_t max, char *msg, int len)
{
    msg[0] = 0;
    *buf = NULL;
    *n = 0;
    if (wifi_state() != WIFI_CONNECTED) {
        snprintf(msg, len, "NO WIFI");
        return false;
    }
    ss_load();
    ss_lock();
    ss_get_t g = {.url = s_ss.u[0], .max = max, .grow = true};
    bool ok = tfn_ss_url_ok(s_ss.url) && tfn_ss_join(s_ss.u[0], SS_URL_MAX, s_ss.url, rel);
    if (ok) {
        ss_run(&g, 1, 0, NULL);
        ok = ss_got(&g, msg, len);
    } else {
        snprintf(msg, len, "NO STORE URL");
    }
    ss_unlock();
    if (!ok) {
        free(g.buf);
        return false;
    }
    *buf = g.buf;
    *n = g.got;
    return true;
}

bool tfn_sstore_store_signed(const uint8_t *m, size_t n, const uint8_t *sig, size_t sl, char *msg, int len)
{
    ss_lock();
    ss_get_t g = {.buf = (uint8_t *)sig, .got = sl};
    uint8_t pk[TFN_PUB_PK];
    const bool ok = ss_index_key(m, n, &g, pk, msg, len);
    ss_unlock();
    return ok;
}

uint8_t *tfn_sstore_icon(const char *id, size_t *len)
{
    tfn_pub_ops_t o;
    tfn_ss_pkg_t p;
    ss_get_t g = {0};
    char msg[96] = "", rel[72];
    ss_ops(&o);
    ss_load();
    ss_lock();
    bool ok = ss_find(id, &p) && p.f[TFN_SS_F_ICON].size;
    if (ok) {
        snprintf(rel, sizeof rel, "apps/%s/%s/icon.bin", p.id, tfn_kind());
        g.buf = heap_caps_malloc(p.f[TFN_SS_F_ICON].size, MALLOC_CAP_SPIRAM);
        g.cap = g.max = p.f[TFN_SS_F_ICON].size;
        g.url = s_ss.u[0];
        ok = g.buf && tfn_ss_join(s_ss.u[0], SS_URL_MAX, s_ss.url, rel);
    }
    if (ok) {
        ss_run(&g, 1, 0, NULL);
        ok = ss_got(&g, msg, sizeof msg) && tfn_ss_file_ok(&o, &p.f[TFN_SS_F_ICON], g.buf, g.got) &&
             tfn_icon_ok(g.buf, g.got);
    }
    ss_unlock();
    if (!ok) {
        free(g.buf);
        return NULL;
    }
    *len = g.got;
    return g.buf;
}
