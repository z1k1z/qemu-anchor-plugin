#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <glib.h>
#include <qemu-plugin.h>

enum {
    MAX_ANCHORS         = 32,
    MAX_SIG_LEN         = 128,
    MAX_VCPUS           = 128,
    MAX_EXPR_DEPTH      = 64,
    MAX_PEB_MODULES     = 256,
    STACK_TB_INSNS      = 256,
    SOCK_TIMEOUT_MS     = 50,
    CHUNK_SIZE          = (1 << 20),
    SUBCHUNK_SIZE       = (1 << 16),
    PAGE_SIZE_FALLBACK  = 4096,
    MAX_ZERO_HOLE_LEN   = (16 << 20),
    MAX_PE_IMAGE_SIZE   = (512 << 20),
    MAX_RECORDED_HOLES  = 16,
    MAX_WRITER_QUEUE    = 4,
    DEFAULT_PEB_TTL_US  = 1000000
};

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

typedef enum {
    MODE_RAW = 0,
    MODE_PE  = 1
} DumpMode;

typedef struct {
    struct qemu_plugin_register *handle;
    char *name;
    bool skip_in_dump;
} RegEntry;

typedef struct {
    size_t off;
    size_t len;
} ZeroHoleDesc;

typedef struct {
    size_t dumped_len;
    size_t holes_count;
    size_t holes_bytes;
    ZeroHoleDesc holes[MAX_RECORDED_HOLES];
    uint64_t xxh64;
    char *sha256;
    char *dedup_of;
    double entropy;
    bool queued_or_written;
} DumpResult;

typedef struct {
    char *filepath;
    uint8_t *data;
    size_t len;
    bool do_fsync;
    bool is_stop_sentinel;
} WriteJob;

typedef struct {
    int id;
    bool active;

    bool use_sig;
    uint8_t sig[MAX_SIG_LEN];
    uint8_t mask[MAX_SIG_LEN];
    size_t sig_len;

    bool use_va;
    uint64_t target_va;

    bool user_only;

    DumpMode mode;
    char *dumpva_expr;
    char *dumplen_expr;
    char *cond_expr;
    bool dump_regs;
    bool pause_on_hit;
    bool exit_on_hit;

    uint64_t max_count;
    uint64_t every_n;
    bool every_per_vcpu;
    double after_sec;

    uint64_t match_attempt;
    uint64_t vcpu_attempt[MAX_VCPUS];
    uint64_t fire_count;
    uint64_t cond_eval_errors;
} AnchorConfig;

typedef struct {
    uint32_t anchor_id;
    uint64_t insn_vaddr;
    uint64_t tb_vaddr;
    char *disas;
    char *symbol;
} CallsiteData;

typedef struct {
    bool enabled;
    int guest_bits;
    gint64 ttl_us;
    uint64_t teb_peb_off;
    uint64_t peb_ldr_off;
    uint64_t ldr_list_off;
    uint64_t ldr_base_off;
    uint64_t ldr_size_off;
    uint64_t ldr_name_off;
} PebWalkConfig;

typedef struct {
    uint64_t base;
    uint32_t size;
    char *name;
} PebModuleEntry;

static AnchorConfig anchors[MAX_ANCHORS];
static int num_anchors = 0;

static PebWalkConfig peb_cfg = {
    .enabled      = true,
    .guest_bits   = 64,
    .ttl_us       = DEFAULT_PEB_TTL_US,
    .teb_peb_off  = 0x60,
    .peb_ldr_off  = 0x18,
    .ldr_list_off = 0x10,
    .ldr_base_off = 0x30,
    .ldr_size_off = 0x40,
    .ldr_name_off = 0x58
};

static char *dump_dir = NULL;
static char *log_path = NULL;
static char *notify_sock_path = NULL;
static FILE *log_fp = NULL;
static GMutex log_mutex;
static GTimer *run_timer = NULL;
static gint sock_err_logged = 0;

static bool dedup_enabled = true;
static bool opt_entropy = false;
static bool opt_sha256 = false;
static bool opt_fsync_every = false;
static bool opt_async_write = true;

static GMutex reg_init_mutex;
static gint regs_initialized = 0;
static GPtrArray *reg_list = NULL;
static GPtrArray *dump_reg_list = NULL;
static GHashTable *reg_by_name = NULL;

static GMutex callsite_mutex;
static GHashTable *callsite_pool = NULL;

static GMutex dedup_mutex;
static GHashTable *seen_dumps = NULL;

static GMutex peb_cache_mutex;
static uint64_t peb_cached_cr3 = UINT64_MAX;
static gint64 peb_cached_ts_us = 0;
static GPtrArray *peb_cached_modules = NULL;
static uint64_t peb_walk_total = 0;

static GMutex writer_mutex;
static GCond writer_cond;
static GCond writer_done_cond;
static GQueue writer_queue = G_QUEUE_INIT;
static GThread *writer_thread = NULL;
static gint writer_running = 0;
static gint writer_inflight = 0;

static inline uint64_t rotl64(uint64_t x, int r)
{
    unsigned int ur = (unsigned int)r;
    return (x << ur) | (x >> (~ur + 65U));
}

static inline uint64_t xxh64_round(uint64_t acc, uint64_t input)
{
    acc += input * 0xC2B2AE3D27D4EB4FULL;
    acc = rotl64(acc, 31);
    acc *= 0x9E3779B185EBCA87ULL;
    return acc;
}

static inline uint64_t xxh64_merge_round(uint64_t acc, uint64_t val)
{
    val = xxh64_round(0, val);
    acc ^= val;
    acc = acc * 0x9E3779B185EBCA87ULL + 0x85EBCA77C2B2AE63ULL;
    return acc;
}

static uint64_t calc_xxh64(const uint8_t data[], size_t len, uint64_t seed)
{
    const uint64_t p1 = 0x9E3779B185EBCA87ULL;
    const uint64_t p2 = 0xC2B2AE3D27D4EB4FULL;
    const uint64_t p3 = 0x165667B19E3779F9ULL;
    const uint64_t p4 = 0x85EBCA77C2B2AE63ULL;
    const uint64_t p5 = 0x27D4EB2F165667C5ULL;

    size_t pos = 0;
    uint64_t h64 = 0;

    if (len >= 32) {
        size_t limit = len - 32;
        uint64_t v1 = seed + p1 + p2;
        uint64_t v2 = seed + p2;
        uint64_t v3 = seed + 0;
        uint64_t v4 = seed - p1;
        do {
            uint64_t k1, k2, k3, k4;
            memcpy(&k1, data + pos, 8); v1 = xxh64_round(v1, k1); pos += 8;
            memcpy(&k2, data + pos, 8); v2 = xxh64_round(v2, k2); pos += 8;
            memcpy(&k3, data + pos, 8); v3 = xxh64_round(v3, k3); pos += 8;
            memcpy(&k4, data + pos, 8); v4 = xxh64_round(v4, k4); pos += 8;
        } while (pos <= limit);

        h64 = rotl64(v1, 1) + rotl64(v2, 7) + rotl64(v3, 12) + rotl64(v4, 18);
        h64 = xxh64_merge_round(h64, v1);
        h64 = xxh64_merge_round(h64, v2);
        h64 = xxh64_merge_round(h64, v3);
        h64 = xxh64_merge_round(h64, v4);
    } else {
        h64 = seed + p5;
    }

    h64 += (uint64_t)len;

    while (pos + 8 <= len) {
        uint64_t k1;
        memcpy(&k1, data + pos, 8);
        k1 *= p2;
        k1 = rotl64(k1, 31);
        k1 *= p1;
        h64 ^= k1;
        h64 = rotl64(h64, 27) * p1 + p4;
        pos += 8;
    }

    if (pos + 4 <= len) {
        uint32_t k1;
        memcpy(&k1, data + pos, 4);
        h64 ^= (uint64_t)k1 * p1;
        h64 = rotl64(h64, 23) * p2 + p3;
        pos += 4;
    }

    while (pos < len) {
        uint64_t byte_val = data[pos];
        h64 ^= byte_val * p5;
        h64 = rotl64(h64, 11) * p1;
        pos++;
    }

    h64 ^= h64 >> 33;
    h64 *= p2;
    h64 ^= h64 >> 29;
    h64 *= p3;
    h64 ^= h64 >> 32;
    return h64;
}

static void append_json_escaped(GString *str, const char *s)
{
    if (!s) return;
    g_autofree char *fixed = g_utf8_validate(s, -1, NULL) ? NULL : g_utf8_make_valid(s, -1);
    if (fixed) s = fixed;
    for (size_t i = 0; s[i] != '\0'; i++) {
        unsigned char c = (unsigned char)s[i];
        if (c == '"' || c == '\\') {
            g_string_append_c(str, '\\');
            g_string_append_c(str, (char)c);
        } else if (c == '\n') {
            g_string_append(str, "\\n");
        } else if (c == '\r') {
            g_string_append(str, "\\r");
        } else if (c == '\t') {
            g_string_append(str, "\\t");
        } else if (c < 0x20 || c == 0x7f) {
            g_string_append_printf(str, "\\u%04x", c);
        } else {
            g_string_append_c(str, (char)c);
        }
    }
}

static void log_json_line(const char *json_str)
{
    g_mutex_lock(&log_mutex);
    if (log_fp) {
        fputs(json_str, log_fp);
        fputc('\n', log_fp);
        fflush(log_fp);
    } else {
        qemu_plugin_outs(json_str);
        qemu_plugin_outs("\n");
    }
    g_mutex_unlock(&log_mutex);
}

static bool write_buffer_to_file(
    const char *filepath,
    const uint8_t data[],
    size_t len,
    bool do_fsync)
{
    FILE *fp = fopen(filepath, "wb");
    if (!fp) {
        return false;
    }
    bool ok = (fwrite(data, 1, len, fp) == len) && (fflush(fp) == 0);
    if (ok && do_fsync) {
        ok = (fsync(fileno(fp)) == 0);
    }
    fclose(fp);
    if (!ok) {
        unlink(filepath);
    }
    return ok;
}

static gpointer writer_thread_func(gpointer data)
{
    (void)data;
    for (;;) {
        g_mutex_lock(&writer_mutex);
        while (g_queue_is_empty(&writer_queue)) {
            g_cond_wait(&writer_cond, &writer_mutex);
        }
        WriteJob *job = g_queue_pop_head(&writer_queue);
        g_mutex_unlock(&writer_mutex);

        if (!job) continue;
        if (job->is_stop_sentinel) {
            g_free(job);
            break;
        }

        (void)write_buffer_to_file(job->filepath, job->data, job->len, job->do_fsync);
        g_free(job->filepath);
        g_free(job->data);
        g_free(job);

        g_mutex_lock(&writer_mutex);
        writer_inflight--;
        if (writer_inflight == 0 && g_queue_is_empty(&writer_queue)) {
            g_cond_broadcast(&writer_done_cond);
        }
        g_mutex_unlock(&writer_mutex);
    }
    return NULL;
}

static void flush_writer_queue(void)
{
    if (!g_atomic_int_get(&writer_running)) return;
    g_mutex_lock(&writer_mutex);
    while (writer_inflight > 0 || !g_queue_is_empty(&writer_queue)) {
        g_cond_wait(&writer_done_cond, &writer_mutex);
    }
    g_mutex_unlock(&writer_mutex);
}

static bool submit_dump_write(
    const char *filepath,
    uint8_t *data,
    size_t len,
    bool force_sync)
{
    if (!opt_async_write || !g_atomic_int_get(&writer_running) || force_sync) {
        bool ok = write_buffer_to_file(filepath, data, len, force_sync || opt_fsync_every);
        g_free(data);
        return ok;
    }

    g_mutex_lock(&writer_mutex);
    if (writer_inflight >= MAX_WRITER_QUEUE) {
        g_mutex_unlock(&writer_mutex);
        bool ok = write_buffer_to_file(filepath, data, len, opt_fsync_every);
        g_free(data);
        return ok;
    }

    WriteJob *job = g_new0(WriteJob, 1);
    job->filepath = g_strdup(filepath);
    job->data     = data;
    job->len      = len;
    job->do_fsync = opt_fsync_every;
    job->is_stop_sentinel = false;

    writer_inflight++;
    g_queue_push_tail(&writer_queue, job);
    g_cond_signal(&writer_cond);
    g_mutex_unlock(&writer_mutex);
    return true;
}

static bool wait_fd_writable(int fd, int timeout_ms)
{
    struct pollfd pfd = { .fd = fd, .events = POLLOUT, .revents = 0 };
    int ret;
    do {
        ret = poll(&pfd, 1, timeout_ms);
    } while (ret < 0 && errno == EINTR);
    if (ret <= 0 || (pfd.revents & (POLLERR | POLLHUP | POLLNVAL))) {
        return false;
    }
    return (pfd.revents & POLLOUT) != 0;
}

static bool wait_fd_readable_or_hup(int fd, int timeout_ms)
{
    struct pollfd pfd = { .fd = fd, .events = POLLIN, .revents = 0 };
    int ret;
    do {
        ret = poll(&pfd, 1, timeout_ms);
    } while (ret < 0 && errno == EINTR);
    if (ret <= 0 || (pfd.revents & (POLLERR | POLLNVAL))) {
        return false;
    }
    return (pfd.revents & (POLLIN | POLLHUP)) != 0;
}

static bool send_all_nonblock(int fd, const char *buf, size_t len, int timeout_ms)
{
    size_t sent = 0;
    while (sent < len) {
        ssize_t n = send(fd, buf + sent, len - sent, MSG_NOSIGNAL);
        if (n > 0) {
            sent += (size_t)n;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            if (!wait_fd_writable(fd, timeout_ms)) {
                return false;
            }
        } else {
            return false;
        }
    }
    return true;
}

static void notify_external_orchestrator(const char *json_str)
{
    if (!notify_sock_path || notify_sock_path[0] == '\0') {
        return;
    }
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) {
        return;
    }

    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) {
        (void)fcntl(fd, F_SETFL, flags | O_NONBLOCK);
    }

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, notify_sock_path, strlen(notify_sock_path));

    bool ok = false;
    int res = connect(fd, (struct sockaddr *)&addr, sizeof(addr));
    if (res == 0) {
        ok = true;
    } else if (res < 0 && errno == EINPROGRESS) {
        if (wait_fd_writable(fd, SOCK_TIMEOUT_MS)) {
            int so_err = 0;
            socklen_t slen = sizeof(so_err);
            if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &so_err, &slen) == 0 && so_err == 0) {
                ok = true;
            }
        }
    }

    if (ok) {
        ok = send_all_nonblock(fd, json_str, strlen(json_str), SOCK_TIMEOUT_MS) &&
             send_all_nonblock(fd, "\n", 1, SOCK_TIMEOUT_MS);
        if (ok && wait_fd_readable_or_hup(fd, SOCK_TIMEOUT_MS)) {
            char ack_buf[16];
            (void)recv(fd, ack_buf, sizeof(ack_buf), 0);
        }
    }

    if (!ok && g_atomic_int_compare_and_exchange(&sock_err_logged, 0, 1)) {
        fprintf(stderr, "[anchor] warn: orchestrator socket %s unreachable\n",
                notify_sock_path);
    }

    close(fd);
}

static bool parse_sig_hex(
    const char *hex,
    uint8_t sig[],
    uint8_t mask[],
    size_t out_len[1])
{
    size_t len = strlen(hex);
    if (len == 0 || (len % 2) != 0 || (len / 2) > MAX_SIG_LEN) {
        fprintf(stderr, "[anchor] sig must be non-empty even-length hex (max %d bytes)\n",
                MAX_SIG_LEN);
        return false;
    }
    size_t bytes = len / 2;
    for (size_t i = 0; i < bytes; i++) {
        char c1 = hex[i * 2];
        char c2 = hex[i * 2 + 1];
        if (c1 == '?' && c2 == '?') {
            sig[i] = 0x00;
            mask[i] = 0x00;
        } else if (c1 == '?' || c2 == '?') {
            fprintf(stderr,
                    "[anchor] wildcard masks in sig=%s must be specified as byte pairs '?" "?'\n",
                    hex);
            return false;
        } else if (isxdigit((unsigned char)c1) && isxdigit((unsigned char)c2)) {
            char buf[3] = { c1, c2, '\0' };
            sig[i] = (uint8_t)strtoul(buf, NULL, 16);
            mask[i] = 0xFF;
        } else {
            return false;
        }
    }
    out_len[0] = bytes;
    return true;
}

static bool should_skip_reg_in_dump(const char *name)
{
    if (g_str_has_prefix(name, "xmm") ||
        g_str_has_prefix(name, "ymm") ||
        g_str_has_prefix(name, "zmm") ||
        g_str_has_prefix(name, "st")  ||
        g_str_has_prefix(name, "mm")) {
        return true;
    }
    const char *skip_exact[] = {
        "rip", "eip", "fctrl", "fstat", "ftag",
        "fiseg", "fioff", "foseg", "fooff", "fop", "mxcsr"
    };
    for (size_t i = 0; i < G_N_ELEMENTS(skip_exact); i++) {
        if (g_strcmp0(name, skip_exact[i]) == 0) {
            return true;
        }
    }
    return false;
}

static void free_reg_entry(gpointer data)
{
    RegEntry *re = (RegEntry *)data;
    if (!re) return;
    g_free(re->name);
    g_free(re);
}

static void vcpu_init_cb(unsigned int vcpu_index, void *userdata)
{
    (void)vcpu_index;
    (void)userdata;

    if (g_atomic_int_get(&regs_initialized)) {
        return;
    }

    g_mutex_lock(&reg_init_mutex);
    if (!g_atomic_int_get(&regs_initialized)) {
        reg_list = g_ptr_array_new_with_free_func(free_reg_entry);
        dump_reg_list = g_ptr_array_new();
        reg_by_name = g_hash_table_new(g_str_hash, g_str_equal);

        g_autoptr(GArray) regs = qemu_plugin_get_registers();
        if (regs) {
            for (guint i = 0; i < regs->len; i++) {
                qemu_plugin_reg_descriptor *desc =
                    &g_array_index(regs, qemu_plugin_reg_descriptor, i);
                RegEntry *re = g_new0(RegEntry, 1);
                re->handle = desc->handle;
                re->name = g_ascii_strdown(desc->name, -1);
                re->skip_in_dump = should_skip_reg_in_dump(re->name);
                g_ptr_array_add(reg_list, re);
                if (!re->skip_in_dump) {
                    g_ptr_array_add(dump_reg_list, re);
                }
                g_hash_table_insert(reg_by_name, re->name, re);
            }
        }
        g_atomic_int_set(&regs_initialized, 1);
    }
    g_mutex_unlock(&reg_init_mutex);
}

typedef struct {
    const char *alias;
    const char *parent;
    uint64_t mask;
    int shift;
} SubRegMap;

static const SubRegMap x86_subreg_table[] = {
    { "eax",  "rax", 0xFFFFFFFFULL, 0 }, { "ebx",  "rbx", 0xFFFFFFFFULL, 0 },
    { "ecx",  "rcx", 0xFFFFFFFFULL, 0 }, { "edx",  "rdx", 0xFFFFFFFFULL, 0 },
    { "esi",  "rsi", 0xFFFFFFFFULL, 0 }, { "edi",  "rdi", 0xFFFFFFFFULL, 0 },
    { "ebp",  "rbp", 0xFFFFFFFFULL, 0 }, { "esp",  "rsp", 0xFFFFFFFFULL, 0 },
    { "r8d",  "r8",  0xFFFFFFFFULL, 0 }, { "r9d",  "r9",  0xFFFFFFFFULL, 0 },
    { "r10d", "r10", 0xFFFFFFFFULL, 0 }, { "r11d", "r11", 0xFFFFFFFFULL, 0 },
    { "r12d", "r12", 0xFFFFFFFFULL, 0 }, { "r13d", "r13", 0xFFFFFFFFULL, 0 },
    { "r14d", "r14", 0xFFFFFFFFULL, 0 }, { "r15d", "r15", 0xFFFFFFFFULL, 0 },
    { "ax",   "rax", 0xFFFFULL, 0 },     { "bx",   "rbx", 0xFFFFULL, 0 },
    { "cx",   "rcx", 0xFFFFULL, 0 },     { "dx",   "rdx", 0xFFFFULL, 0 },
    { "si",   "rsi", 0xFFFFULL, 0 },     { "di",   "rdi", 0xFFFFULL, 0 },
    { "bp",   "rbp", 0xFFFFULL, 0 },     { "sp",   "rsp", 0xFFFFULL, 0 },
    { "r8w",  "r8",  0xFFFFULL, 0 },     { "r9w",  "r9",  0xFFFFULL, 0 },
    { "r10w", "r10", 0xFFFFULL, 0 },     { "r11w", "r11", 0xFFFFULL, 0 },
    { "r12w", "r12", 0xFFFFULL, 0 },     { "r13w", "r13", 0xFFFFULL, 0 },
    { "r14w", "r14", 0xFFFFULL, 0 },     { "r15w", "r15", 0xFFFFULL, 0 },
    { "al",   "rax", 0xFFULL, 0 },       { "bl",   "rbx", 0xFFULL, 0 },
    { "cl",   "rcx", 0xFFULL, 0 },       { "dl",   "rdx", 0xFFULL, 0 },
    { "sil",  "rsi", 0xFFULL, 0 },       { "dil",  "rdi", 0xFFULL, 0 },
    { "bpl",  "rbp", 0xFFULL, 0 },       { "spl",  "rsp", 0xFFULL, 0 },
    { "r8b",  "r8",  0xFFULL, 0 },       { "r9b",  "r9",  0xFFULL, 0 },
    { "r10b", "r10", 0xFFULL, 0 },       { "r11b", "r11", 0xFFULL, 0 },
    { "r12b", "r12", 0xFFULL, 0 },       { "r13b", "r13", 0xFFULL, 0 },
    { "r14b", "r14", 0xFFULL, 0 },       { "r15b", "r15", 0xFFULL, 0 },
    { "ah",   "rax", 0xFFULL, 8 },       { "bh",   "rbx", 0xFFULL, 8 },
    { "ch",   "rcx", 0xFFULL, 8 },       { "dh",   "rdx", 0xFFULL, 8 },
    { "rflags", "eflags", UINT64_MAX, 0 }
};

static const char *known_full_regs[] = {
    "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp",
    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
    "rip", "eip", "ip", "eflags", "rflags",
    "cs", "ds", "es", "fs", "gs", "ss",
    "fs_base", "gs_base", "k_gs_base",
    "es_base", "cs_base", "ss_base", "ds_base",
    "gdtr_base", "gdtr_limit", "idtr_base", "idtr_limit",
    "ldtr", "ldtr_base", "ldtr_limit", "tr", "tr_base", "tr_limit",
    "cr0", "cr2", "cr3", "cr4", "cr8", "efer",
    "dr0", "dr1", "dr2", "dr3", "dr6", "dr7", "pkru"
};

static const char *map_x86_subreg(
    const char *name,
    uint64_t mask_out[1],
    int shift_out[1])
{
    mask_out[0] = UINT64_MAX;
    shift_out[0] = 0;
    for (size_t i = 0; i < G_N_ELEMENTS(x86_subreg_table); i++) {
        if (g_strcmp0(name, x86_subreg_table[i].alias) == 0) {
            mask_out[0]  = x86_subreg_table[i].mask;
            shift_out[0] = x86_subreg_table[i].shift;
            return x86_subreg_table[i].parent;
        }
    }
    return name;
}

static bool is_known_x86_reg_name(const char *name)
{
    g_autofree char *low = g_ascii_strdown(name, -1);
    for (size_t i = 0; i < G_N_ELEMENTS(known_full_regs); i++) {
        if (g_strcmp0(low, known_full_regs[i]) == 0) {
            return true;
        }
    }
    for (size_t i = 0; i < G_N_ELEMENTS(x86_subreg_table); i++) {
        if (g_strcmp0(low, x86_subreg_table[i].alias) == 0) {
            return true;
        }
    }
    if (g_atomic_int_get(&regs_initialized) && reg_by_name) {
        if (g_hash_table_contains(reg_by_name, low)) {
            return true;
        }
    }
    return false;
}

static bool read_reg_entry_u64(RegEntry *re, uint64_t val_out[1])
{
    g_autoptr(GByteArray) buf = g_byte_array_new();
    int ret = qemu_plugin_read_register(re->handle, buf);
    if (ret <= 0 || buf->len == 0 || buf->len > sizeof(uint64_t)) {
        return false;
    }
    uint64_t v = 0;
    memcpy(&v, buf->data, buf->len);
    val_out[0] = v;
    return true;
}

static bool read_reg_u64(const char *name, uint64_t val_out[1])
{
    if (!g_atomic_int_get(&regs_initialized)) {
        vcpu_init_cb(0, NULL);
    }
    if (!reg_by_name) {
        return false;
    }
    uint64_t mask = UINT64_MAX;
    int shift = 0;
    const char *lookup_name = map_x86_subreg(name, &mask, &shift);
    RegEntry *re = g_hash_table_lookup(reg_by_name, lookup_name);
    if (!re && (mask != UINT64_MAX || shift != 0)) {
        re = g_hash_table_lookup(reg_by_name, name);
        mask = UINT64_MAX;
        shift = 0;
    }
    if (!re) {
        return false;
    }
    uint64_t v = 0;
    if (!read_reg_entry_u64(re, &v)) {
        return false;
    }
    val_out[0] = (v >> shift) & mask;
    return true;
}

static bool eval_expr_depth(
    const char *expr,
    uint64_t cur_rip,
    uint64_t out_val[1],
    int depth);

static bool validate_expr_syntax(
    const char *expr,
    int depth,
    bool warn_mixed_ops[1],
    char *err_msg[1]);

static bool is_wrapped_in_brackets(const char *s, size_t len, char open_c, char close_c)
{
    if (len < 2 || s[0] != open_c || s[len - 1] != close_c) {
        return false;
    }
    int depth = 0;
    for (size_t i = 0; i < len - 1; i++) {
        if (s[i] == open_c) depth++;
        else if (s[i] == close_c) {
            depth--;
            if (depth == 0) return false;
        }
    }
    return depth == 1;
}

static bool has_balanced_brackets(const char *s, size_t len)
{
    int paren = 0, bracket = 0;
    for (size_t i = 0; i < len; i++) {
        if (s[i] == '(') paren++;
        else if (s[i] == ')') { if (--paren < 0) return false; }
        else if (s[i] == '[') bracket++;
        else if (s[i] == ']') { if (--bracket < 0) return false; }
    }
    return paren == 0 && bracket == 0;
}

static size_t match_deref_func_prefix(const char *token, size_t len, size_t deref_size_out[1])
{
    deref_size_out[0] = 0;
    size_t pfx_len = 0;
    if (g_str_has_prefix(token, "u8(")) {
        deref_size_out[0] = 1;
        pfx_len = 2;
    } else if (g_str_has_prefix(token, "u16(")) {
        deref_size_out[0] = 2;
        pfx_len = 3;
    } else if (g_str_has_prefix(token, "u32(")) {
        deref_size_out[0] = 4;
        pfx_len = 3;
    } else if (g_str_has_prefix(token, "u64(")) {
        deref_size_out[0] = 8;
        pfx_len = 3;
    }
    if (pfx_len > 0 && is_wrapped_in_brackets(token + pfx_len, len - pfx_len, '(', ')')) {
        return pfx_len + 1;
    }
    deref_size_out[0] = 0;
    return 0;
}

static bool validate_term_syntax(
    const char *s,
    size_t len,
    int depth,
    bool warn_mixed_ops[1],
    char *err_msg[1])
{
    if (depth > MAX_EXPR_DEPTH) {
        err_msg[0] = g_strdup("expression exceeds maximum recursion depth");
        return false;
    }
    while (len > 0 && isspace((unsigned char)s[0])) {
        s++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)s[len - 1])) {
        len--;
    }
    if (len == 0) {
        err_msg[0] = g_strdup("empty operand in expression");
        return false;
    }

    if (is_wrapped_in_brackets(s, len, '(', ')') ||
        is_wrapped_in_brackets(s, len, '[', ']')) {
        g_autofree char *inner = g_strndup(s + 1, len - 2);
        return validate_expr_syntax(inner, depth + 1, warn_mixed_ops, err_msg);
    }

    if (s[0] == '-' || s[0] == '~') {
        return validate_term_syntax(s + 1, len - 1, depth + 1, warn_mixed_ops, err_msg);
    }

    g_autofree char *token = g_strndup(s, len);

    size_t deref_sz = 0;
    size_t body_off = match_deref_func_prefix(token, len, &deref_sz);
    if (body_off > 0) {
        if (len <= body_off + 1) {
            err_msg[0] = g_strdup_printf("empty address expression in '%s'", token);
            return false;
        }
        g_autofree char *sub = g_strndup(token + body_off, len - body_off - 1);
        return validate_expr_syntax(sub, depth + 1, warn_mixed_ops, err_msg);
    }

    if (isdigit((unsigned char)token[0])) {
        char *endptr = NULL;
        errno = 0;
        (void)g_ascii_strtoull(token, &endptr, 0);
        if (errno == 0 && endptr && endptr[0] == '\0') {
            return true;
        }
        err_msg[0] = g_strdup_printf("invalid numeric literal '%s'", token);
        return false;
    }

    if (is_known_x86_reg_name(token)) {
        return true;
    }

    err_msg[0] = g_strdup_printf("unknown register or invalid token '%s'", token);
    return false;
}

static bool validate_expr_syntax(
    const char *expr,
    int depth,
    bool warn_mixed_ops[1],
    char *err_msg[1])
{
    if (!expr || expr[0] == '\0') {
        err_msg[0] = g_strdup("empty expression");
        return false;
    }
    if (depth > MAX_EXPR_DEPTH) {
        err_msg[0] = g_strdup("expression exceeds maximum recursion depth");
        return false;
    }

    size_t len = strlen(expr);
    while (len > 0 && isspace((unsigned char)expr[0])) {
        expr++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)expr[len - 1])) {
        len--;
    }
    if (len == 0) {
        err_msg[0] = g_strdup("empty expression");
        return false;
    }
    if (!has_balanced_brackets(expr, len)) {
        err_msg[0] = g_strdup_printf("unbalanced brackets in '%s'", expr);
        return false;
    }

    bool has_top_bitwise = false;
    bool has_top_additive = false;
    {
        int p = 0, b = 0;
        for (size_t i = 0; i < len; i++) {
            char c = expr[i];
            if (c == '(') p++;
            else if (c == ')') p--;
            else if (c == '[') b++;
            else if (c == ']') b--;
            else if (p == 0 && b == 0) {
                if (c == '&' || c == '|' || c == '^') has_top_bitwise = true;
                else if (c == '+' || c == '-') {
                    if (c == '-') {
                        ssize_t j = (ssize_t)i - 1;
                        while (j >= 0 && isspace((unsigned char)expr[j])) j--;
                        if (j < 0 || strchr("+-&|^([~", expr[j]) != NULL) continue;
                    }
                    has_top_additive = true;
                }
            }
        }
        if (has_top_bitwise && has_top_additive && warn_mixed_ops) {
            warn_mixed_ops[0] = true;
        }
    }

    for (int pass = 0; pass < 4; pass++) {
        int paren = 0, bracket = 0;
        for (ssize_t i = (ssize_t)len - 1; i >= 0; i--) {
            char c = expr[i];
            if (c == ')') paren++;
            else if (c == '(') paren--;
            else if (c == ']') bracket++;
            else if (c == '[') bracket--;
            else if (paren == 0 && bracket == 0) {
                bool match_op = false;
                if (pass == 0 && c == '|') match_op = true;
                else if (pass == 1 && c == '^') match_op = true;
                else if (pass == 2 && c == '&') match_op = true;
                else if (pass == 3 && (c == '+' || c == '-')) match_op = true;
                if (!match_op) continue;

                if (c == '-') {
                    ssize_t j = i - 1;
                    while (j >= 0 && isspace((unsigned char)expr[j])) j--;
                    if (j < 0 || strchr("+-&|^([~", expr[j]) != NULL) {
                        continue;
                    }
                }

                g_autofree char *left_s = g_strndup(expr, (size_t)i);
                g_autofree char *right_s = g_strndup(expr + i + 1, len - (size_t)i - 1);
                return validate_expr_syntax(left_s, depth + 1, warn_mixed_ops, err_msg) &&
                       validate_expr_syntax(right_s, depth + 1, warn_mixed_ops, err_msg);
            }
        }
    }

    return validate_term_syntax(expr, len, depth, warn_mixed_ops, err_msg);
}

static bool is_negative_literal_str(const char *s)
{
    while (s[0] != '\0' && isspace((unsigned char)s[0])) s++;
    if (s[0] != '-') return false;
    s++;
    while (s[0] != '\0' && isspace((unsigned char)s[0])) s++;
    return isdigit((unsigned char)s[0]) != 0;
}

static bool validate_cond_syntax(
    const char *cond,
    int depth,
    bool warn_neg_cmp[1],
    bool warn_mixed_ops[1],
    char *err_msg[1])
{
    if (!cond || depth > MAX_EXPR_DEPTH) {
        err_msg[0] = g_strdup("condition exceeds maximum recursion depth");
        return false;
    }

    size_t len = strlen(cond);
    while (len > 0 && isspace((unsigned char)cond[0])) {
        cond++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)cond[len - 1])) {
        len--;
    }
    if (len == 0) {
        err_msg[0] = g_strdup("empty condition");
        return false;
    }
    if (!has_balanced_brackets(cond, len)) {
        err_msg[0] = g_strdup_printf("unbalanced brackets in condition '%s'", cond);
        return false;
    }

    for (int pass = 0; pass < 2; pass++) {
        const char *tok = (pass == 0) ? "||" : "&&";
        int paren = 0, bracket = 0;
        for (size_t i = 0; i + 1 < len; i++) {
            char c = cond[i];
            if (c == '(') paren++;
            else if (c == ')') paren--;
            else if (c == '[') bracket++;
            else if (c == ']') bracket--;
            else if (paren == 0 && bracket == 0 &&
                     cond[i] == tok[0] && cond[i + 1] == tok[1]) {
                g_autofree char *lhs = g_strndup(cond, i);
                g_autofree char *rhs = g_strndup(cond + i + 2, len - i - 2);
                return validate_cond_syntax(lhs, depth + 1, warn_neg_cmp, warn_mixed_ops, err_msg) &&
                       validate_cond_syntax(rhs, depth + 1, warn_neg_cmp, warn_mixed_ops, err_msg);
            }
        }
    }

    if (is_wrapped_in_brackets(cond, len, '(', ')')) {
        g_autofree char *inner = g_strndup(cond + 1, len - 2);
        return validate_cond_syntax(inner, depth + 1, warn_neg_cmp, warn_mixed_ops, err_msg);
    }

    if (cond[0] == '!' && cond[1] != '=') {
        g_autofree char *sub = g_strndup(cond + 1, len - 1);
        return validate_cond_syntax(sub, depth + 1, warn_neg_cmp, warn_mixed_ops, err_msg);
    }

    const char *ops[] = { "==", "!=", "<=", ">=", "<", ">" };
    for (size_t o = 0; o < G_N_ELEMENTS(ops); o++) {
        size_t op_len = strlen(ops[o]);
        int paren = 0, bracket = 0;
        for (size_t i = 0; i + op_len <= len; i++) {
            char c = cond[i];
            if (c == '(') paren++;
            else if (c == ')') paren--;
            else if (c == '[') bracket++;
            else if (c == ']') bracket--;
            else if (paren == 0 && bracket == 0 &&
                     strncmp(cond + i, ops[o], op_len) == 0) {
                g_autofree char *lhs_s = g_strndup(cond, i);
                g_autofree char *rhs_s = g_strndup(cond + i + op_len, len - i - op_len);
                if (warn_neg_cmp && (is_negative_literal_str(lhs_s) || is_negative_literal_str(rhs_s))) {
                    warn_neg_cmp[0] = true;
                }
                return validate_expr_syntax(lhs_s, depth + 1, warn_mixed_ops, err_msg) &&
                       validate_expr_syntax(rhs_s, depth + 1, warn_mixed_ops, err_msg);
            }
        }
    }

    return validate_expr_syntax(cond, depth + 1, warn_mixed_ops, err_msg);
}

static bool eval_term_depth(
    const char *s,
    size_t len,
    uint64_t cur_rip,
    uint64_t out_val[1],
    int depth)
{
    if (depth > MAX_EXPR_DEPTH) {
        return false;
    }
    while (len > 0 && isspace((unsigned char)s[0])) {
        s++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)s[len - 1])) {
        len--;
    }
    if (len == 0) return false;

    if (is_wrapped_in_brackets(s, len, '(', ')') ||
        is_wrapped_in_brackets(s, len, '[', ']')) {
        g_autofree char *inner_expr = g_strndup(s + 1, len - 2);
        return eval_expr_depth(inner_expr, cur_rip, out_val, depth + 1);
    }

    if (s[0] == '-' || s[0] == '~') {
        char op = s[0];
        uint64_t v = 0;
        if (eval_term_depth(s + 1, len - 1, cur_rip, &v, depth + 1)) {
            out_val[0] = (op == '-') ? (uint64_t)(-(int64_t)v) : ~v;
            return true;
        }
        return false;
    }

    g_autofree char *token = g_strndup(s, len);

    size_t deref_size = 0;
    size_t body_off = match_deref_func_prefix(token, len, &deref_size);
    if (body_off > 0) {
        if (len <= body_off + 1) {
            return false;
        }
        g_autofree char *sub = g_strndup(token + body_off, len - body_off - 1);
        uint64_t addr = 0;
        if (!eval_expr_depth(sub, cur_rip, &addr, depth + 1)) {
            return false;
        }
        g_autoptr(GByteArray) mem = g_byte_array_new();
        if (!qemu_plugin_read_memory_vaddr(addr, mem, deref_size)) {
            return false;
        }
        uint64_t v = 0;
        memcpy(&v, mem->data, deref_size);
        out_val[0] = v;
        return true;
    }

    if (isdigit((unsigned char)token[0])) {
        char *endptr = NULL;
        errno = 0;
        uint64_t v = g_ascii_strtoull(token, &endptr, 0);
        if (errno == 0 && endptr && endptr[0] == '\0') {
            out_val[0] = v;
            return true;
        }
        return false;
    }

    char *low = g_ascii_strdown(token, -1);
    bool reg_ok = false;
    if (g_strcmp0(low, "rip") == 0 || g_strcmp0(low, "eip") == 0) {
        out_val[0] = cur_rip;
        reg_ok = true;
    } else if (g_strcmp0(low, "ip") == 0) {
        out_val[0] = cur_rip & 0xFFFFULL;
        reg_ok = true;
    } else {
        reg_ok = read_reg_u64(low, out_val);
    }
    g_free(low);
    return reg_ok;
}

static bool eval_expr_depth(
    const char *expr,
    uint64_t cur_rip,
    uint64_t out_val[1],
    int depth)
{
    if (!expr || expr[0] == '\0' || depth > MAX_EXPR_DEPTH) {
        return false;
    }

    size_t len = strlen(expr);
    while (len > 0 && isspace((unsigned char)expr[0])) {
        expr++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)expr[len - 1])) {
        len--;
    }
    if (len == 0) return false;

    for (int pass = 0; pass < 4; pass++) {
        int paren = 0;
        int bracket = 0;
        for (ssize_t i = (ssize_t)len - 1; i >= 0; i--) {
            char c = expr[i];
            if (c == ')') paren++;
            else if (c == '(') paren--;
            else if (c == ']') bracket++;
            else if (c == '[') bracket--;
            else if (paren == 0 && bracket == 0) {
                bool match_op = false;
                if (pass == 0 && c == '|') match_op = true;
                else if (pass == 1 && c == '^') match_op = true;
                else if (pass == 2 && c == '&') match_op = true;
                else if (pass == 3 && (c == '+' || c == '-')) match_op = true;
                if (!match_op) continue;

                if (c == '-') {
                    ssize_t j = i - 1;
                    while (j >= 0 && isspace((unsigned char)expr[j])) j--;
                    if (j < 0 || strchr("+-&|^([~", expr[j]) != NULL) {
                        continue;
                    }
                }

                g_autofree char *left_s = g_strndup(expr, (size_t)i);
                g_autofree char *right_s = g_strndup(expr + i + 1, len - (size_t)i - 1);
                uint64_t lval = 0, rval = 0;
                if (!eval_expr_depth(left_s, cur_rip, &lval, depth + 1) ||
                    !eval_expr_depth(right_s, cur_rip, &rval, depth + 1)) {
                    return false;
                }
                if (c == '+') out_val[0] = lval + rval;
                else if (c == '-') out_val[0] = lval - rval;
                else if (c == '&') out_val[0] = lval & rval;
                else if (c == '|') out_val[0] = lval | rval;
                else if (c == '^') out_val[0] = lval ^ rval;
                return true;
            }
        }
    }

    return eval_term_depth(expr, len, cur_rip, out_val, depth);
}

static bool eval_expr(const char *expr, uint64_t cur_rip, uint64_t out_val[1])
{
    return eval_expr_depth(expr, cur_rip, out_val, 0);
}

static bool eval_condition_depth(
    const char *cond,
    uint64_t cur_rip,
    int depth,
    bool eval_ok[1])
{
    if (!cond || depth > MAX_EXPR_DEPTH) {
        eval_ok[0] = false;
        return false;
    }

    size_t len = strlen(cond);
    while (len > 0 && isspace((unsigned char)cond[0])) {
        cond++;
        len--;
    }
    while (len > 0 && isspace((unsigned char)cond[len - 1])) {
        len--;
    }
    if (len == 0) return true;

    for (int pass = 0; pass < 2; pass++) {
        const char *tok = (pass == 0) ? "||" : "&&";
        int paren = 0, bracket = 0;
        for (size_t i = 0; i + 1 < len; i++) {
            char c = cond[i];
            if (c == '(') paren++;
            else if (c == ')') paren--;
            else if (c == '[') bracket++;
            else if (c == ']') bracket--;
            else if (paren == 0 && bracket == 0 &&
                     cond[i] == tok[0] && cond[i + 1] == tok[1]) {
                g_autofree char *lhs = g_strndup(cond, i);
                g_autofree char *rhs = g_strndup(cond + i + 2, len - i - 2);
                if (pass == 0) {
                    bool l_ok = true, r_ok = true;
                    bool l_res = eval_condition_depth(lhs, cur_rip, depth + 1, &l_ok);
                    if (l_ok && l_res) {
                        eval_ok[0] = true;
                        return true;
                    }
                    bool r_res = eval_condition_depth(rhs, cur_rip, depth + 1, &r_ok);
                    if (r_ok && r_res) {
                        eval_ok[0] = true;
                        return true;
                    }
                    eval_ok[0] = (l_ok && r_ok);
                    return false;
                } else {
                    bool l_ok = true;
                    bool l_res = eval_condition_depth(lhs, cur_rip, depth + 1, &l_ok);
                    if (!l_ok) {
                        eval_ok[0] = false;
                        return false;
                    }
                    if (!l_res) {
                        eval_ok[0] = true;
                        return false;
                    }
                    return eval_condition_depth(rhs, cur_rip, depth + 1, eval_ok);
                }
            }
        }
    }

    if (is_wrapped_in_brackets(cond, len, '(', ')')) {
        g_autofree char *inner = g_strndup(cond + 1, len - 2);
        return eval_condition_depth(inner, cur_rip, depth + 1, eval_ok);
    }

    if (cond[0] == '!' && cond[1] != '=') {
        g_autofree char *sub = g_strndup(cond + 1, len - 1);
        bool sub_ok = true;
        bool res = eval_condition_depth(sub, cur_rip, depth + 1, &sub_ok);
        if (!sub_ok) {
            eval_ok[0] = false;
            return false;
        }
        return !res;
    }

    const char *ops[] = { "==", "!=", "<=", ">=", "<", ">" };
    for (size_t o = 0; o < G_N_ELEMENTS(ops); o++) {
        size_t op_len = strlen(ops[o]);
        int paren = 0, bracket = 0;
        for (size_t i = 0; i + op_len <= len; i++) {
            char c = cond[i];
            if (c == '(') paren++;
            else if (c == ')') paren--;
            else if (c == '[') bracket++;
            else if (c == ']') bracket--;
            else if (paren == 0 && bracket == 0 &&
                     strncmp(cond + i, ops[o], op_len) == 0) {
                g_autofree char *lhs_s = g_strndup(cond, i);
                g_autofree char *rhs_s = g_strndup(cond + i + op_len, len - i - op_len);
                uint64_t l = 0, r = 0;
                if (!eval_expr_depth(lhs_s, cur_rip, &l, depth + 1) ||
                    !eval_expr_depth(rhs_s, cur_rip, &r, depth + 1)) {
                    eval_ok[0] = false;
                    return false;
                }
                if (strcmp(ops[o], "==") == 0) return l == r;
                if (strcmp(ops[o], "!=") == 0) return l != r;
                if (strcmp(ops[o], "<=") == 0) return l <= r;
                if (strcmp(ops[o], ">=") == 0) return l >= r;
                if (strcmp(ops[o], "<") == 0)  return l < r;
                if (strcmp(ops[o], ">") == 0)  return l > r;
            }
        }
    }

    uint64_t v = 0;
    if (!eval_expr_depth(cond, cur_rip, &v, depth + 1)) {
        eval_ok[0] = false;
        return false;
    }
    return v != 0;
}

static bool eval_condition(const char *cond, uint64_t cur_rip, bool eval_ok[1])
{
    eval_ok[0] = true;
    return eval_condition_depth(cond, cur_rip, 0, eval_ok);
}

static void free_peb_module_entry(gpointer data)
{
    PebModuleEntry *m = (PebModuleEntry *)data;
    if (!m) return;
    g_free(m->name);
    g_free(m);
}

static bool is_user_space_code_va(uint64_t addr)
{
    if (addr < 0x1000ULL) {
        return false;
    }
    if (peb_cfg.guest_bits == 32) {
        return addr < 0x80000000ULL;
    }
    return (addr >> 47) == 0;
}

static bool is_valid_peb_ptr_bits(uint64_t addr, int bits)
{
    if (addr < 0x1000ULL) {
        return false;
    }
    if (bits == 32) {
        return addr < 0xFFFF0000ULL;
    }
    return (addr >> 47) == 0;
}

static bool read_guest_ptr_bits(uint64_t addr, int bits, uint64_t out_ptr[1])
{
    size_t ptr_sz = (bits == 32) ? 4 : 8;
    g_autoptr(GByteArray) buf = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(addr, buf, ptr_sz)) {
        return false;
    }
    uint64_t v = 0;
    memcpy(&v, buf->data, ptr_sz);
    out_ptr[0] = v;
    return true;
}

static bool read_guest_u32(uint64_t addr, uint32_t out_val[1])
{
    g_autoptr(GByteArray) buf = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(addr, buf, 4)) {
        return false;
    }
    memcpy(out_val, buf->data, 4);
    return true;
}

static bool read_guest_u16(uint64_t addr, uint16_t out_val[1])
{
    g_autoptr(GByteArray) buf = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(addr, buf, 2)) {
        return false;
    }
    memcpy(out_val, buf->data, 2);
    return true;
}

static const PebModuleEntry *lookup_module_in_array(GPtrArray *mods, uint64_t va)
{
    if (!mods) return NULL;
    for (guint i = 0; i < mods->len; i++) {
        const PebModuleEntry *m = g_ptr_array_index(mods, i);
        if (va >= m->base && va < (m->base + m->size)) {
            return m;
        }
    }
    return NULL;
}

static void walk_peb_from_teb_into(uint64_t teb, int bits, GPtrArray *mods)
{
    if (!is_valid_peb_ptr_bits(teb, bits)) {
        return;
    }

    bool same_bits = (bits == peb_cfg.guest_bits);
    uint64_t teb_peb_off  = same_bits ? peb_cfg.teb_peb_off  : 0x30;
    uint64_t peb_ldr_off  = same_bits ? peb_cfg.peb_ldr_off  : 0x0c;
    uint64_t ldr_list_off = same_bits ? peb_cfg.ldr_list_off : 0x0c;
    uint64_t ldr_base_off = same_bits ? peb_cfg.ldr_base_off : 0x18;
    uint64_t ldr_size_off = same_bits ? peb_cfg.ldr_size_off : 0x20;
    uint64_t ldr_name_off = same_bits ? peb_cfg.ldr_name_off : 0x2c;

    uint64_t peb = 0, ldr = 0;
    if (!read_guest_ptr_bits(teb + teb_peb_off, bits, &peb) || !is_valid_peb_ptr_bits(peb, bits)) {
        return;
    }
    if (!read_guest_ptr_bits(peb + peb_ldr_off, bits, &ldr) || !is_valid_peb_ptr_bits(ldr, bits)) {
        return;
    }

    uint64_t list_head = ldr + ldr_list_off;
    uint64_t flink = 0;
    if (!read_guest_ptr_bits(list_head, bits, &flink) || !is_valid_peb_ptr_bits(flink, bits)) {
        return;
    }

    for (int i = 0; i < MAX_PEB_MODULES && flink != list_head; i++) {
        if (!is_valid_peb_ptr_bits(flink, bits)) {
            break;
        }
        uint64_t entry = flink;
        uint64_t dll_base = 0;
        uint32_t size_of_image = 0;

        if (!read_guest_ptr_bits(entry + ldr_base_off, bits, &dll_base) ||
            !read_guest_u32(entry + ldr_size_off, &size_of_image)) {
            break;
        }

        if (is_valid_peb_ptr_bits(dll_base, bits) &&
            size_of_image > 0 && size_of_image <= (uint32_t)MAX_PE_IMAGE_SIZE &&
            !lookup_module_in_array(mods, dll_base)) {

            uint16_t name_len = 0, max_len = 0;
            uint64_t name_buf_ptr = 0;
            size_t buf_ptr_off = (bits == 32) ? 4 : 8;

            if (read_guest_u16(entry + ldr_name_off, &name_len) &&
                read_guest_u16(entry + ldr_name_off + 2, &max_len) &&
                name_len > 0 && (name_len % 2) == 0 &&
                max_len >= name_len && name_len <= 512 &&
                read_guest_ptr_bits(entry + ldr_name_off + buf_ptr_off, bits, &name_buf_ptr) &&
                is_valid_peb_ptr_bits(name_buf_ptr, bits)) {

                g_autoptr(GByteArray) u16_buf = g_byte_array_new();
                if (qemu_plugin_read_memory_vaddr(name_buf_ptr, u16_buf, name_len)) {
                    char *utf8 = g_utf16_to_utf8(
                        (const gunichar2 *)u16_buf->data,
                        (glong)(name_len / 2),
                        NULL, NULL, NULL);
                    if (utf8 && utf8[0] != '\0') {
                        PebModuleEntry *m = g_new0(PebModuleEntry, 1);
                        m->base = dll_base;
                        m->size = size_of_image;
                        m->name = utf8;
                        g_ptr_array_add(mods, m);
                    } else {
                        g_free(utf8);
                    }
                }
            }
        }

        uint64_t next_flink = 0;
        if (!read_guest_ptr_bits(flink, bits, &next_flink) || next_flink == flink) {
            break;
        }
        flink = next_flink;
    }
}

static char *resolve_va_via_peb(
    uint64_t target_va,
    uint64_t cr3,
    uint64_t out_base[1],
    uint64_t out_rva[1],
    uint64_t out_walks[1])
{
    if (!peb_cfg.enabled || !is_valid_peb_ptr_bits(target_va, peb_cfg.guest_bits)) {
        return NULL;
    }

    uint64_t cr3_key = cr3 & 0x7FFFFFFFFFFFF000ULL;
    gint64 now_us = g_get_real_time();

    g_mutex_lock(&peb_cache_mutex);

    if (cr3_key != peb_cached_cr3) {
        if (peb_cached_modules) {
            g_ptr_array_free(peb_cached_modules, TRUE);
            peb_cached_modules = NULL;
        }
        peb_cached_cr3 = cr3_key;
        peb_cached_ts_us = 0;
    } else if (cr3_key != 0) {
        if (peb_cached_modules) {
            const PebModuleEntry *hit = lookup_module_in_array(peb_cached_modules, target_va);
            if (hit) {
                if (out_base)  out_base[0]  = hit->base;
                if (out_rva)   out_rva[0]   = target_va - hit->base;
                if (out_walks) out_walks[0] = peb_walk_total;
                char *res = g_strdup(hit->name);
                g_mutex_unlock(&peb_cache_mutex);
                return res;
            }
        }
        if (peb_cached_ts_us > 0 && (now_us - peb_cached_ts_us) < peb_cfg.ttl_us) {
            if (out_walks) out_walks[0] = peb_walk_total;
            g_mutex_unlock(&peb_cache_mutex);
            return NULL;
        }
    }

    peb_walk_total++;
    if (out_walks) out_walks[0] = peb_walk_total;

    GPtrArray *mods = g_ptr_array_new_with_free_func(free_peb_module_entry);
    if (peb_cfg.guest_bits == 64) {
        uint64_t gs = 0, kgs = 0, fs = 0;
        if (read_reg_u64("gs_base", &gs)) {
            walk_peb_from_teb_into(gs, 64, mods);
        }
        if (mods->len == 0 && read_reg_u64("k_gs_base", &kgs) && kgs != gs) {
            walk_peb_from_teb_into(kgs, 64, mods);
        }
        if (read_reg_u64("fs_base", &fs) && is_valid_peb_ptr_bits(fs, 32)) {
            walk_peb_from_teb_into(fs, 32, mods);
        }
    } else {
        uint64_t fs = 0;
        if (read_reg_u64("fs_base", &fs)) {
            walk_peb_from_teb_into(fs, 32, mods);
        }
    }

    peb_cached_ts_us = now_us;

    char *result_name = NULL;
    if (mods->len > 0) {
        if (peb_cached_modules) {
            g_ptr_array_free(peb_cached_modules, TRUE);
        }
        peb_cached_modules = mods;

        const PebModuleEntry *hit = lookup_module_in_array(peb_cached_modules, target_va);
        if (hit) {
            if (out_base) out_base[0] = hit->base;
            if (out_rva)  out_rva[0]  = target_va - hit->base;
            result_name = g_strdup(hit->name);
        }
    } else {
        g_ptr_array_free(mods, TRUE);
    }

    g_mutex_unlock(&peb_cache_mutex);
    return result_name;
}

static bool inspect_pe_header(
    uint64_t base_va,
    uint32_t size_of_image[1],
    uint16_t magic[1],
    uint16_t machine[1],
    uint16_t num_sections[1],
    uint16_t subsystem[1])
{
    g_autoptr(GByteArray) dos = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(base_va, dos, 0x40)) {
        return false;
    }
    if (dos->data[0] != 'M' || dos->data[1] != 'Z') {
        return false;
    }
    uint32_t e_lfanew = 0;
    memcpy(&e_lfanew, dos->data + 0x3c, sizeof(uint32_t));
    if (e_lfanew == 0 || e_lfanew > 0x100000) {
        return false;
    }

    g_autoptr(GByteArray) nth = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(base_va + e_lfanew, nth, 0xF8)) {
        if (!qemu_plugin_read_memory_vaddr(base_va + e_lfanew, nth, 0x60)) {
            return false;
        }
    }
    if (memcmp(nth->data, "PE\0\0", 4) != 0) {
        return false;
    }

    uint16_t opt_magic = 0;
    memcpy(&opt_magic, nth->data + 0x18, sizeof(uint16_t));
    if (opt_magic != 0x010b && opt_magic != 0x020b) {
        return false;
    }

    magic[0] = opt_magic;
    memcpy(machine, nth->data + 4, sizeof(uint16_t));
    memcpy(num_sections, nth->data + 6, sizeof(uint16_t));
    memcpy(size_of_image, nth->data + 0x50, sizeof(uint32_t));
    memcpy(subsystem, nth->data + 0x5c, sizeof(uint16_t));
    return (size_of_image[0] > 0 && size_of_image[0] <= (uint32_t)MAX_PE_IMAGE_SIZE);
}

static double calc_buffer_entropy(const uint8_t data[], size_t len)
{
    if (len == 0) return 0.0;
    uint64_t hist[256] = { 0 };
    for (size_t i = 0; i < len; i++) {
        hist[data[i]]++;
    }
    double ent = 0.0;
    double inv_total = 1.0 / (double)len;
    for (int i = 0; i < 256; i++) {
        if (hist[i] > 0) {
            double p = (double)hist[i] * inv_total;
            ent -= p * log2(p);
        }
    }
    return ent;
}

static void record_zero_hole(DumpResult *res, size_t hole_off, size_t hole_len)
{
    if (res->holes_count < MAX_RECORDED_HOLES) {
        res->holes[res->holes_count].off = hole_off;
        res->holes[res->holes_count].len = hole_len;
    }
    res->holes_count++;
    res->holes_bytes += hole_len;
}

static void capture_guest_memory(
    uint32_t anchor_id,
    uint64_t va,
    size_t total_len,
    const char *filepath,
    bool force_sync,
    DumpResult *res)
{
    memset(res, 0, sizeof(*res));

    g_autoptr(GByteArray) buf = g_byte_array_new();
    size_t page_rem = (size_t)PAGE_SIZE_FALLBACK -
                      (size_t)(va & ((uint64_t)PAGE_SIZE_FALLBACK - 1));
    size_t first_probe = total_len < page_rem ? total_len : page_rem;
    if (!qemu_plugin_read_memory_vaddr(va, buf, first_probe)) {
        return;
    }

    uint8_t *raw = g_try_malloc(total_len);
    if (!raw) {
        return;
    }

    size_t scan_pos = 0;
    size_t dumped_len = 0;
    size_t pending_zero_hole = 0;
    size_t hole_start_off = 0;

    while (scan_pos < total_len) {
        size_t rem = total_len - scan_pos;
        size_t req = rem > (size_t)CHUNK_SIZE ? (size_t)CHUNK_SIZE : rem;

        if (qemu_plugin_read_memory_vaddr(va + scan_pos, buf, req)) {
            if (pending_zero_hole > 0 && dumped_len > 0) {
                memset(raw + hole_start_off, 0, pending_zero_hole);
                record_zero_hole(res, hole_start_off, pending_zero_hole);
                pending_zero_hole = 0;
            }
            memcpy(raw + scan_pos, buf->data, req);
            scan_pos += req;
            dumped_len = scan_pos;
        } else {
            size_t sub_pos = 0;
            bool abort_scan = false;
            while (sub_pos < req && !abort_scan) {
                size_t sub_rem = req - sub_pos;
                size_t sub_req = sub_rem > (size_t)SUBCHUNK_SIZE
                                 ? (size_t)SUBCHUNK_SIZE : sub_rem;
                size_t sub_base = scan_pos + sub_pos;

                if (sub_req > (size_t)PAGE_SIZE_FALLBACK &&
                    qemu_plugin_read_memory_vaddr(va + sub_base, buf, sub_req)) {
                    if (pending_zero_hole > 0 && dumped_len > 0) {
                        memset(raw + hole_start_off, 0, pending_zero_hole);
                        record_zero_hole(res, hole_start_off, pending_zero_hole);
                        pending_zero_hole = 0;
                    }
                    memcpy(raw + sub_base, buf->data, sub_req);
                    sub_pos += sub_req;
                    dumped_len = scan_pos + sub_pos;
                    continue;
                }

                size_t page_pos = 0;
                while (page_pos < sub_req) {
                    size_t cur_off = sub_base + page_pos;
                    size_t page_rem_step = (size_t)PAGE_SIZE_FALLBACK -
                        (size_t)((va + cur_off) & ((uint64_t)PAGE_SIZE_FALLBACK - 1));
                    size_t rem_in_sub = sub_req - page_pos;
                    size_t step = rem_in_sub > page_rem_step ? page_rem_step : rem_in_sub;

                    if (qemu_plugin_read_memory_vaddr(va + cur_off, buf, step)) {
                        if (pending_zero_hole > 0 && dumped_len > 0) {
                            memset(raw + hole_start_off, 0, pending_zero_hole);
                            record_zero_hole(res, hole_start_off, pending_zero_hole);
                            pending_zero_hole = 0;
                        } else if (pending_zero_hole > 0 && dumped_len == 0) {
                            abort_scan = true;
                            break;
                        }
                        memcpy(raw + cur_off, buf->data, step);
                        dumped_len = cur_off + step;
                    } else {
                        if (dumped_len == 0) {
                            abort_scan = true;
                            break;
                        }
                        if (pending_zero_hole == 0) {
                            hole_start_off = cur_off;
                        }
                        pending_zero_hole += step;
                        if (pending_zero_hole >= (size_t)MAX_ZERO_HOLE_LEN) {
                            abort_scan = true;
                            break;
                        }
                    }
                    page_pos += step;
                }
                sub_pos += page_pos;
            }
            scan_pos += sub_pos;
            if (abort_scan) {
                break;
            }
        }
    }

    if (dumped_len == 0) {
        g_free(raw);
        return;
    }

    res->dumped_len = dumped_len;
    res->xxh64 = calc_xxh64(raw, dumped_len, 0);

    if (opt_sha256) {
        GChecksum *csum = g_checksum_new(G_CHECKSUM_SHA256);
        g_checksum_update(csum, raw, (gssize)dumped_len);
        res->sha256 = g_strdup(g_checksum_get_string(csum));
        g_checksum_free(csum);
    }
    if (opt_entropy) {
        res->entropy = calc_buffer_entropy(raw, dumped_len);
    }

    g_autofree char *dedup_key = g_strdup_printf("%u:%016llx",
        anchor_id, (unsigned long long)res->xxh64);

    if (dedup_enabled && seen_dumps) {
        g_mutex_lock(&dedup_mutex);
        const char *existing = g_hash_table_lookup(seen_dumps, dedup_key);
        if (existing) {
            res->dedup_of = g_strdup(existing);
            g_mutex_unlock(&dedup_mutex);
            g_free(raw);
            return;
        }
        g_mutex_unlock(&dedup_mutex);
    }

    if (submit_dump_write(filepath, raw, dumped_len, force_sync)) {
        res->queued_or_written = true;
        if (dedup_enabled && seen_dumps) {
            g_mutex_lock(&dedup_mutex);
            if (!g_hash_table_lookup(seen_dumps, dedup_key)) {
                g_hash_table_insert(seen_dumps,
                                    g_strdup(dedup_key),
                                    g_path_get_basename(filepath));
            }
            g_mutex_unlock(&dedup_mutex);
        }
    }
}

static void on_anchor_exec(unsigned int vcpu_index, void *udata)
{
    CallsiteData *cs = (CallsiteData *)udata;
    if (!cs || cs->anchor_id >= (uint32_t)num_anchors) {
        return;
    }
    AnchorConfig *ac = &anchors[cs->anchor_id];

    if (!__atomic_load_n(&ac->active, __ATOMIC_ACQUIRE)) {
        return;
    }

    if (ac->max_count > 0 &&
        __atomic_load_n(&ac->fire_count, __ATOMIC_RELAXED) >= ac->max_count) {
        return;
    }

    const uint64_t rip = cs->insn_vaddr;

    if (ac->user_only && !is_user_space_code_va(rip)) {
        return;
    }

    if (ac->after_sec > 0.0 && run_timer) {
        if (g_timer_elapsed(run_timer, NULL) < ac->after_sec) {
            return;
        }
    }

    if (ac->cond_expr) {
        bool eval_ok = true;
        bool cond_matched = eval_condition(ac->cond_expr, rip, &eval_ok);
        if (!eval_ok) {
            __atomic_add_fetch(&ac->cond_eval_errors, 1, __ATOMIC_RELAXED);
            return;
        }
        if (!cond_matched) {
            return;
        }
    }

    uint64_t attempt = 0;
    if (ac->every_per_vcpu && vcpu_index < (unsigned int)MAX_VCPUS) {
        attempt = __atomic_add_fetch(&ac->vcpu_attempt[vcpu_index], 1, __ATOMIC_SEQ_CST);
    } else {
        attempt = __atomic_add_fetch(&ac->match_attempt, 1, __ATOMIC_SEQ_CST);
    }
    if (ac->every_n > 1 && ((attempt - 1) % ac->every_n) != 0) {
        return;
    }

    uint64_t hit_no = __atomic_add_fetch(&ac->fire_count, 1, __ATOMIC_SEQ_CST);
    if (ac->max_count > 0 && hit_no > ac->max_count) {
        return;
    }

    uint64_t rsp = 0, cr3 = 0;
    read_reg_u64("rsp", &rsp);
    read_reg_u64("cr3", &cr3);

    gint64 ts_us = g_get_real_time();
    g_autoptr(GString) json = g_string_new("{");
    g_string_append_printf(json,
        "\"ts\":%lld,\"event\":\"anchor_hit\",\"anchor\":%u,\"hit\":%llu,\"vcpu\":%u,"
        "\"rip\":\"0x%llx\",\"tb_vaddr\":\"0x%llx\",\"rsp\":\"0x%llx\",\"cr3\":\"0x%llx\"",
        (long long)ts_us, cs->anchor_id, (unsigned long long)hit_no, vcpu_index,
        (unsigned long long)rip, (unsigned long long)cs->tb_vaddr,
        (unsigned long long)rsp, (unsigned long long)cr3);

    if (cs->disas) {
        g_string_append(json, ",\"disas\":\"");
        append_json_escaped(json, cs->disas);
        g_string_append_c(json, '"');
    }
    if (cs->symbol) {
        g_string_append(json, ",\"symbol\":\"");
        append_json_escaped(json, cs->symbol);
        g_string_append_c(json, '"');
    }

    uint64_t mod_base = 0, mod_rva = 0, peb_walks = 0;
    g_autofree char *mod_name = resolve_va_via_peb(rip, cr3, &mod_base, &mod_rva, &peb_walks);
    if (mod_name) {
        g_string_append(json, ",\"module\":\"");
        append_json_escaped(json, mod_name);
        g_string_append_printf(json,
            "\",\"module_base\":\"0x%llx\",\"rva\":\"0x%llx\","
            "\"module_source\":\"peb_walk\",\"peb_walks\":%llu",
            (unsigned long long)mod_base, (unsigned long long)mod_rva,
            (unsigned long long)peb_walks);
    }

    if (ac->pause_on_hit) {
        g_string_append(json, ",\"pause_requested\":true");
    }

    if (ac->dump_regs && g_atomic_int_get(&regs_initialized) && dump_reg_list) {
        g_string_append_printf(json, ",\"regs\":{\"rip\":\"0x%llx\"", (unsigned long long)rip);
        for (guint i = 0; i < dump_reg_list->len; i++) {
            RegEntry *re = g_ptr_array_index(dump_reg_list, i);
            uint64_t val = 0;
            if (read_reg_entry_u64(re, &val)) {
                g_string_append_printf(json, ",\"%s\":\"0x%llx\"",
                    re->name, (unsigned long long)val);
            }
        }
        g_string_append(json, "}");
    }

    if (ac->dumpva_expr) {
        uint64_t dump_va = 0;
        if (!eval_expr(ac->dumpva_expr, rip, &dump_va)) {
            g_string_append(json, ",\"dump_error\":\"failed_eval_dumpva\"");
        } else {
            uint64_t dump_len = 0;
            bool pe_ok = true;
            uint16_t magic = 0, machine = 0, sections = 0, subsys = 0;

            if (ac->mode == MODE_PE) {
                uint32_t img_size = 0;
                if (inspect_pe_header(dump_va, &img_size, &magic, &machine, &sections, &subsys)) {
                    dump_len = img_size;
                } else {
                    pe_ok = false;
                    g_string_append(json, ",\"dump_error\":\"invalid_pe_header\"");
                }
            } else if (ac->dumplen_expr) {
                if (!eval_expr(ac->dumplen_expr, rip, &dump_len)) {
                    pe_ok = false;
                    g_string_append(json, ",\"dump_error\":\"failed_eval_dumplen\"");
                } else if (dump_len == 0 || dump_len > (uint64_t)MAX_PE_IMAGE_SIZE) {
                    pe_ok = false;
                    g_string_append(json, ",\"dump_error\":\"invalid_dumplen\"");
                }
            }

            if (pe_ok && dump_len > 0) {
                const char *dir = dump_dir ? dump_dir : ".";
                g_autofree char *fname = g_strdup_printf(
                    "%s/anchor%u-%04llu-vcpu%u-0x%llx-%lld.bin",
                    dir, cs->anchor_id, (unsigned long long)hit_no,
                    vcpu_index, (unsigned long long)dump_va, (long long)ts_us);

                bool force_sync = ac->pause_on_hit || ac->exit_on_hit || opt_fsync_every;
                DumpResult dres;
                capture_guest_memory(cs->anchor_id, dump_va, (size_t)dump_len, fname, force_sync, &dres);

                if (ac->mode == MODE_PE && dres.dumped_len > 0) {
                    g_string_append_printf(json,
                        ",\"pe\":{\"magic\":\"0x%x\",\"machine\":\"0x%x\","
                        "\"sections\":%u,\"subsystem\":%u,\"size_of_image\":%u",
                        magic, machine, sections, subsys, (uint32_t)dump_len);
                    if (opt_entropy) {
                        char ent_buf[32];
                        g_ascii_formatd(ent_buf, sizeof(ent_buf), "%.4f", dres.entropy);
                        g_string_append_printf(json, ",\"entropy\":%s", ent_buf);
                    }
                    g_string_append_c(json, '}');
                }

                if (dres.holes_count > 0) {
                    g_string_append_printf(json,
                        ",\"zero_holes_count\":%zu,\"zero_holes_bytes\":%zu",
                        dres.holes_count, dres.holes_bytes);
                    if (dres.holes_count > MAX_RECORDED_HOLES) {
                        g_string_append(json, ",\"zero_holes_truncated\":true");
                    }
                    g_string_append(json, ",\"zero_holes\":[");
                    size_t n_rep = dres.holes_count < MAX_RECORDED_HOLES
                                   ? dres.holes_count : MAX_RECORDED_HOLES;
                    for (size_t h = 0; h < n_rep; h++) {
                        g_string_append_printf(json, "%s{\"off\":%zu,\"len\":%zu}",
                            h == 0 ? "" : ",", dres.holes[h].off, dres.holes[h].len);
                    }
                    g_string_append_c(json, ']');
                }

                if (dres.dumped_len == 0) {
                    g_string_append_printf(json,
                        ",\"dump_va\":\"0x%llx\",\"req_len\":%llu,\"dumped_len\":0,"
                        "\"stored\":false,\"dump_error\":\"read_memory_failed\"",
                        (unsigned long long)dump_va, (unsigned long long)dump_len);
                } else if (!dres.dedup_of && !dres.queued_or_written) {
                    g_string_append_printf(json,
                        ",\"dump_va\":\"0x%llx\",\"req_len\":%llu,\"dumped_len\":0,"
                        "\"stored\":false,\"dump_error\":\"write_file_failed\"",
                        (unsigned long long)dump_va, (unsigned long long)dump_len);
                } else if (dres.dedup_of) {
                    g_string_append_printf(json,
                        ",\"dump_va\":\"0x%llx\",\"req_len\":%llu,\"dumped_len\":0,"
                        "\"stored\":false,\"xxh64\":\"0x%016llx\"",
                        (unsigned long long)dump_va, (unsigned long long)dump_len,
                        (unsigned long long)dres.xxh64);
                    if (dres.sha256) {
                        g_string_append_printf(json, ",\"sha256\":\"%s\"", dres.sha256);
                    }
                    g_string_append(json, ",\"dedup_skipped\":true,\"dedup_of\":\"");
                    append_json_escaped(json, dres.dedup_of);
                    g_string_append_c(json, '"');
                } else {
                    g_string_append_printf(json,
                        ",\"dump_va\":\"0x%llx\",\"req_len\":%llu,\"dumped_len\":%zu,"
                        "\"stored\":true,\"xxh64\":\"0x%016llx\"",
                        (unsigned long long)dump_va, (unsigned long long)dump_len,
                        dres.dumped_len, (unsigned long long)dres.xxh64);
                    if (dres.sha256) {
                        g_string_append_printf(json, ",\"sha256\":\"%s\"", dres.sha256);
                    }
                    g_string_append(json, ",\"dump_path\":\"");
                    append_json_escaped(json, fname);
                    g_string_append_c(json, '"');
                }

                g_free(dres.sha256);
                g_free(dres.dedup_of);
            }
        }
    }

    g_string_append(json, "}");

    if (ac->pause_on_hit || ac->exit_on_hit) {
        flush_writer_queue();
    }

    log_json_line(json->str);

    if (ac->pause_on_hit) {
        notify_external_orchestrator(json->str);
    }

    if (ac->exit_on_hit) {
        g_mutex_lock(&log_mutex);
        if (log_fp) {
            fflush(log_fp);
            fsync(fileno(log_fp));
        }
        g_mutex_unlock(&log_mutex);
        _exit(0);
    }
}

static CallsiteData *get_or_create_callsite(
    uint32_t anchor_id,
    struct qemu_plugin_insn *insn,
    uint64_t insn_vaddr,
    uint64_t tb_vaddr)
{
    g_autofree char *key = g_strdup_printf("%u:%llx:%llx",
        anchor_id, (unsigned long long)insn_vaddr, (unsigned long long)tb_vaddr);

    g_mutex_lock(&callsite_mutex);
    CallsiteData *cs = g_hash_table_lookup(callsite_pool, key);
    if (!cs) {
        cs = g_new0(CallsiteData, 1);
        cs->anchor_id  = anchor_id;
        cs->insn_vaddr = insn_vaddr;
        cs->tb_vaddr   = tb_vaddr;
        cs->disas      = qemu_plugin_insn_disas(insn);
        const char *sym = qemu_plugin_insn_symbol(insn);
        cs->symbol     = sym ? g_strdup(sym) : NULL;
        g_hash_table_insert(callsite_pool, g_strdup(key), cs);
    }
    g_mutex_unlock(&callsite_mutex);
    return cs;
}

static void free_callsite_data(gpointer data)
{
    CallsiteData *cs = (CallsiteData *)data;
    if (!cs) return;
    g_free(cs->disas);
    g_free(cs->symbol);
    g_free(cs);
}

static bool match_masked(
    const uint8_t buf[],
    const uint8_t sig[],
    const uint8_t mask[],
    size_t len)
{
    for (size_t i = 0; i < len; i++) {
        if ((buf[i] & mask[i]) != (sig[i] & mask[i])) {
            return false;
        }
    }
    return true;
}

static void vcpu_tb_trans_cb(struct qemu_plugin_tb *tb, void *userdata)
{
    (void)userdata;
    size_t n_insns = qemu_plugin_tb_n_insns(tb);
    if (n_insns == 0) return;

    uint64_t tb_vaddr = qemu_plugin_tb_vaddr(tb);

    size_t stack_offsets[STACK_TB_INSNS];
    uint64_t stack_vaddrs[STACK_TB_INSNS];
    uint8_t stack_bytes[STACK_TB_INSNS << 4];

    size_t *insn_offsets = (n_insns <= (size_t)STACK_TB_INSNS) ? stack_offsets : g_new(size_t, n_insns);
    uint64_t *insn_vaddrs = (n_insns <= (size_t)STACK_TB_INSNS) ? stack_vaddrs : g_new(uint64_t, n_insns);
    size_t bytes_cap = (n_insns <= (size_t)STACK_TB_INSNS) ? sizeof(stack_bytes) : (n_insns << 4);
    uint8_t *tb_bytes = (n_insns <= (size_t)STACK_TB_INSNS) ? stack_bytes : g_malloc(bytes_cap);
    size_t tb_bytes_len = 0;

    for (size_t i = 0; i < n_insns; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        insn_offsets[i] = tb_bytes_len;
        insn_vaddrs[i]  = qemu_plugin_insn_vaddr(insn);

        uint8_t ibuf[32];
        size_t sz = qemu_plugin_insn_data(insn, ibuf, sizeof(ibuf));
        if (sz > 0 && (tb_bytes_len + sz) <= bytes_cap) {
            memcpy(tb_bytes + tb_bytes_len, ibuf, sz);
            tb_bytes_len += sz;
        }
    }

    for (size_t i = 0; i < n_insns; i++) {
        size_t off   = insn_offsets[i];
        size_t avail = tb_bytes_len - off;
        uint64_t ivaddr = insn_vaddrs[i];

        for (int a = 0; a < num_anchors; a++) {
            AnchorConfig *ac = &anchors[a];
            if (!__atomic_load_n(&ac->active, __ATOMIC_ACQUIRE)) continue;

            if (ac->user_only && !is_user_space_code_va(ivaddr)) {
                continue;
            }

            bool matched = false;
            if (ac->use_va && ivaddr == ac->target_va) {
                matched = true;
            } else if (ac->use_sig && ac->sig_len > 0 && avail >= ac->sig_len) {
                if (((tb_bytes[off] & ac->mask[0]) == (ac->sig[0] & ac->mask[0])) &&
                    match_masked(tb_bytes + off, ac->sig, ac->mask, ac->sig_len)) {
                    matched = true;
                }
            }

            if (matched) {
                struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
                CallsiteData *cs = get_or_create_callsite((uint32_t)a, insn, ivaddr, tb_vaddr);
                qemu_plugin_register_vcpu_insn_exec_cb(
                    insn, on_anchor_exec, QEMU_PLUGIN_CB_R_REGS, cs);
            }
        }
    }

    if (n_insns > (size_t)STACK_TB_INSNS) {
        g_free(insn_offsets);
        g_free(insn_vaddrs);
        g_free(tb_bytes);
    }
}

static void plugin_atexit_cb(void *userdata)
{
    (void)userdata;

    for (int a = 0; a < num_anchors; a++) {
        __atomic_store_n(&anchors[a].active, false, __ATOMIC_RELEASE);
    }
    __atomic_thread_fence(__ATOMIC_SEQ_CST);

    if (g_atomic_int_get(&writer_running)) {
        flush_writer_queue();
        WriteJob *stop_job = g_new0(WriteJob, 1);
        stop_job->is_stop_sentinel = true;
        g_mutex_lock(&writer_mutex);
        g_queue_push_tail(&writer_queue, stop_job);
        g_cond_signal(&writer_cond);
        g_mutex_unlock(&writer_mutex);
        g_thread_join(writer_thread);
        writer_thread = NULL;
        g_atomic_int_set(&writer_running, 0);
    }

    g_autoptr(GString) exit_json = g_string_new("{\"event\":\"plugin_exit\",\"status\":\"graceful\"");
    g_string_append_printf(exit_json, ",\"peb_walks\":%llu,\"anchors\":[",
                           (unsigned long long)peb_walk_total);
    for (int a = 0; a < num_anchors; a++) {
        AnchorConfig *ac = &anchors[a];
        uint64_t fires = __atomic_load_n(&ac->fire_count, __ATOMIC_RELAXED);
        uint64_t cerrs = __atomic_load_n(&ac->cond_eval_errors, __ATOMIC_RELAXED);
        g_string_append_printf(exit_json, "%s{\"id\":%d,\"hits\":%llu,\"cond_eval_errors\":%llu}",
                               a == 0 ? "" : ",", a,
                               (unsigned long long)fires, (unsigned long long)cerrs);
        g_free(ac->dumpva_expr);
        ac->dumpva_expr = NULL;
        g_free(ac->dumplen_expr);
        ac->dumplen_expr = NULL;
        g_free(ac->cond_expr);
        ac->cond_expr = NULL;
    }
    g_string_append(exit_json, "]}");
    log_json_line(exit_json->str);

    g_mutex_lock(&log_mutex);
    if (log_fp) {
        fflush(log_fp);
        fsync(fileno(log_fp));
        fclose(log_fp);
        log_fp = NULL;
    }
    g_mutex_unlock(&log_mutex);

    if (callsite_pool) {
        g_hash_table_destroy(callsite_pool);
        callsite_pool = NULL;
    }
    if (seen_dumps) {
        g_hash_table_destroy(seen_dumps);
        seen_dumps = NULL;
    }
    g_mutex_lock(&peb_cache_mutex);
    if (peb_cached_modules) {
        g_ptr_array_free(peb_cached_modules, TRUE);
        peb_cached_modules = NULL;
    }
    g_mutex_unlock(&peb_cache_mutex);

    g_mutex_lock(&reg_init_mutex);
    g_atomic_int_set(&regs_initialized, 0);
    if (reg_by_name) {
        g_hash_table_destroy(reg_by_name);
        reg_by_name = NULL;
    }
    if (dump_reg_list) {
        g_ptr_array_free(dump_reg_list, TRUE);
        dump_reg_list = NULL;
    }
    if (reg_list) {
        g_ptr_array_free(reg_list, TRUE);
        reg_list = NULL;
    }
    g_mutex_unlock(&reg_init_mutex);

    if (run_timer) {
        g_timer_destroy(run_timer);
        run_timer = NULL;
    }
    g_free(dump_dir);
    dump_dir = NULL;
    g_free(log_path);
    log_path = NULL;
    g_free(notify_sock_path);
    notify_sock_path = NULL;
}

static bool parse_bool_opt(const char *val, bool out[1])
{
    if (!val) return false;
    if (g_strcmp0(val, "1") == 0 || g_ascii_strcasecmp(val, "on") == 0 ||
        g_ascii_strcasecmp(val, "true") == 0 || g_ascii_strcasecmp(val, "yes") == 0) {
        out[0] = true;
        return true;
    }
    if (g_strcmp0(val, "0") == 0 || g_ascii_strcasecmp(val, "off") == 0 ||
        g_ascii_strcasecmp(val, "false") == 0 || g_ascii_strcasecmp(val, "no") == 0) {
        out[0] = false;
        return true;
    }
    return false;
}

static bool parse_u64_opt(const char *val, uint64_t out[1])
{
    if (!val || val[0] == '\0') return false;
    char *endptr = NULL;
    errno = 0;
    uint64_t v = g_ascii_strtoull(val, &endptr, 0);
    if (errno != 0 || !endptr || endptr[0] != '\0') {
        return false;
    }
    out[0] = v;
    return true;
}

static bool parse_double_opt(const char *val, double out[1])
{
    if (!val || val[0] == '\0') return false;
    char *endptr = NULL;
    errno = 0;
    double v = g_ascii_strtod(val, &endptr);
    if (errno != 0 || !endptr || endptr == val || !isfinite(v) || v < 0.0) {
        return false;
    }
    if (endptr[0] == '\0' || g_ascii_strcasecmp(endptr, "s") == 0 ||
        g_ascii_strcasecmp(endptr, "sec") == 0) {
        out[0] = v;
        return true;
    }
    if (g_ascii_strcasecmp(endptr, "ms") == 0) {
        out[0] = v / 1000.0;
        return true;
    }
    if (g_ascii_strcasecmp(endptr, "m") == 0 || g_ascii_strcasecmp(endptr, "min") == 0) {
        out[0] = v * 60.0;
        return true;
    }
    if (g_ascii_strcasecmp(endptr, "h") == 0) {
        out[0] = v * 3600.0;
        return true;
    }
    return false;
}

static AnchorConfig *alloc_new_anchor(void)
{
    if (num_anchors >= MAX_ANCHORS) {
        return NULL;
    }
    AnchorConfig *ac = &anchors[num_anchors];
    memset(ac, 0, sizeof(*ac));
    ac->id        = num_anchors++;
    ac->active    = true;
    ac->dump_regs = true;
    ac->max_count = 1;
    ac->every_n   = 1;
    return ac;
}

static AnchorConfig *current_or_new_anchor(bool is_trigger_key)
{
    if (num_anchors == 0) {
        return alloc_new_anchor();
    }
    AnchorConfig *cur = &anchors[num_anchors - 1];
    if (is_trigger_key && (cur->use_sig || cur->use_va)) {
        return alloc_new_anchor();
    }
    return cur;
}

static void apply_guest_bits_preset(int bits)
{
    if (bits == 32) {
        peb_cfg.guest_bits   = 32;
        peb_cfg.teb_peb_off  = 0x30;
        peb_cfg.peb_ldr_off  = 0x0c;
        peb_cfg.ldr_list_off = 0x0c;
        peb_cfg.ldr_base_off = 0x18;
        peb_cfg.ldr_size_off = 0x20;
        peb_cfg.ldr_name_off = 0x2c;
    } else {
        peb_cfg.guest_bits   = 64;
        peb_cfg.teb_peb_off  = 0x60;
        peb_cfg.peb_ldr_off  = 0x18;
        peb_cfg.ldr_list_off = 0x10;
        peb_cfg.ldr_base_off = 0x30;
        peb_cfg.ldr_size_off = 0x40;
        peb_cfg.ldr_name_off = 0x58;
    }
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(
    qemu_plugin_id_t id,
    const qemu_info_t *info,
    int argc,
    char **argv)
{
    (void)info;
    run_timer     = g_timer_new();
    callsite_pool = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, free_callsite_data);
    seen_dumps    = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, g_free);

    for (int i = 0; i < argc; i++) {
        char *opt = argv[i];
        char *eq = strchr(opt, '=');
        if (!eq) {
            fprintf(stderr, "[anchor] Invalid option without '=': %s\n", opt);
            return -1;
        }

        g_autofree char *key = g_strndup(opt, (size_t)(eq - opt));
        const char *val = eq + 1;

        if (g_strcmp0(key, "dumpdir") == 0) {
            g_free(dump_dir);
            dump_dir = g_strdup(val);
            g_mkdir_with_parents(dump_dir, 0755);
        } else if (g_strcmp0(key, "out") == 0) {
            g_free(log_path);
            log_path = g_strdup(val);
        } else if (g_strcmp0(key, "sock") == 0) {
            struct sockaddr_un tmp_un;
            if (strlen(val) >= sizeof(tmp_un.sun_path)) {
                fprintf(stderr, "[anchor] sock path too long (max %zu bytes): %s\n",
                        sizeof(tmp_un.sun_path) - 1, val);
                return -1;
            }
            g_free(notify_sock_path);
            notify_sock_path = g_strdup(val);
        } else if (g_strcmp0(key, "dedup") == 0) {
            if (!parse_bool_opt(val, &dedup_enabled)) {
                fprintf(stderr, "[anchor] Invalid boolean for dedup=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "entropy") == 0) {
            if (!parse_bool_opt(val, &opt_entropy)) {
                fprintf(stderr, "[anchor] Invalid boolean for entropy=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "sha256") == 0) {
            if (!parse_bool_opt(val, &opt_sha256)) {
                fprintf(stderr, "[anchor] Invalid boolean for sha256=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "fsync_every") == 0) {
            if (!parse_bool_opt(val, &opt_fsync_every)) {
                fprintf(stderr, "[anchor] Invalid boolean for fsync_every=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "async_write") == 0) {
            if (!parse_bool_opt(val, &opt_async_write)) {
                fprintf(stderr, "[anchor] Invalid boolean for async_write=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "peb_walk") == 0) {
            if (!parse_bool_opt(val, &peb_cfg.enabled)) {
                fprintf(stderr, "[anchor] Invalid boolean for peb_walk=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "peb_ttl") == 0) {
            double ttl_s = 0.0;
            if (!parse_double_opt(val, &ttl_s)) {
                fprintf(stderr,
                        "[anchor] Invalid peb_ttl=%s (allowed suffixes: ms, s, sec, m, min, h)\n",
                        val);
                return -1;
            }
            peb_cfg.ttl_us = (gint64)(ttl_s * 1000000.0);
        } else if (g_strcmp0(key, "guest_bits") == 0) {
            uint64_t bits = 0;
            if (!parse_u64_opt(val, &bits) || (bits != 32 && bits != 64)) {
                fprintf(stderr, "[anchor] guest_bits must be 32 or 64, got %s\n", val);
                return -1;
            }
            apply_guest_bits_preset((int)bits);
        } else if (g_strcmp0(key, "teb_peb_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.teb_peb_off)) return -1;
        } else if (g_strcmp0(key, "peb_ldr_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.peb_ldr_off)) return -1;
        } else if (g_strcmp0(key, "ldr_list_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.ldr_list_off)) return -1;
        } else if (g_strcmp0(key, "ldr_base_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.ldr_base_off)) return -1;
        } else if (g_strcmp0(key, "ldr_size_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.ldr_size_off)) return -1;
        } else if (g_strcmp0(key, "ldr_name_off") == 0) {
            if (!parse_u64_opt(val, &peb_cfg.ldr_name_off)) return -1;
        } else if (g_strcmp0(key, "anchor") == 0) {
            if (g_strcmp0(val, "new") != 0) {
                fprintf(stderr, "[anchor] Expected anchor=new, got anchor=%s\n", val);
                return -1;
            }
            if (num_anchors == 1 && !anchors[0].use_sig && !anchors[0].use_va &&
                !anchors[0].dumpva_expr && !anchors[0].cond_expr) {
                continue;
            }
            if (!alloc_new_anchor()) {
                fprintf(stderr, "[anchor] Exceeded MAX_ANCHORS (%d)\n", MAX_ANCHORS);
                return -1;
            }
        } else if (g_strcmp0(key, "sig") == 0) {
            AnchorConfig *ac = current_or_new_anchor(true);
            if (!ac || !parse_sig_hex(val, ac->sig, ac->mask, &ac->sig_len)) {
                fprintf(stderr, "[anchor] Invalid sig=%s\n", val);
                return -1;
            }
            ac->use_sig = true;
            if (ac->sig_len > 15) {
                fprintf(stderr,
                        "[anchor] warn: anchor #%d sig is %zuB (>15B), matches only inside one TB\n",
                        ac->id, ac->sig_len);
            }
        } else if (g_strcmp0(key, "va") == 0) {
            AnchorConfig *ac = current_or_new_anchor(true);
            if (!ac || !parse_u64_opt(val, &ac->target_va)) {
                fprintf(stderr, "[anchor] Invalid va=%s\n", val);
                return -1;
            }
            ac->use_va = true;
        } else if (g_strcmp0(key, "user_only") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_bool_opt(val, &ac->user_only)) {
                fprintf(stderr, "[anchor] Invalid boolean for user_only=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "mode") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (g_strcmp0(val, "pe") == 0) ac->mode = MODE_PE;
            else if (g_strcmp0(val, "raw") == 0) ac->mode = MODE_RAW;
            else {
                fprintf(stderr, "[anchor] Unknown mode=%s (expected raw or pe)\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "dumpva") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            g_free(ac->dumpva_expr);
            ac->dumpva_expr = g_strdup(val);
        } else if (g_strcmp0(key, "dumplen") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            g_free(ac->dumplen_expr);
            ac->dumplen_expr = g_strdup(val);
        } else if (g_strcmp0(key, "cond") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            g_free(ac->cond_expr);
            ac->cond_expr = g_strdup(val);
        } else if (g_strcmp0(key, "regs") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_bool_opt(val, &ac->dump_regs)) {
                fprintf(stderr, "[anchor] Invalid boolean for regs=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "once") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            bool once_flag = false;
            if (!parse_bool_opt(val, &once_flag)) {
                fprintf(stderr, "[anchor] Invalid boolean for once=%s\n", val);
                return -1;
            }
            ac->max_count = once_flag ? 1 : 0;
        } else if (g_strcmp0(key, "count") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_u64_opt(val, &ac->max_count)) {
                fprintf(stderr, "[anchor] Invalid count=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "every") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_u64_opt(val, &ac->every_n)) {
                fprintf(stderr, "[anchor] Invalid every=%s\n", val);
                return -1;
            }
            if (ac->every_n == 0) ac->every_n = 1;
        } else if (g_strcmp0(key, "every_per_vcpu") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_bool_opt(val, &ac->every_per_vcpu)) {
                fprintf(stderr, "[anchor] Invalid boolean for every_per_vcpu=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "after") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_double_opt(val, &ac->after_sec)) {
                fprintf(stderr,
                        "[anchor] Invalid after=%s (allowed suffixes: ms, s, sec, m, min, h)\n",
                        val);
                return -1;
            }
        } else if (g_strcmp0(key, "pause") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_bool_opt(val, &ac->pause_on_hit)) {
                fprintf(stderr, "[anchor] Invalid boolean for pause=%s\n", val);
                return -1;
            }
        } else if (g_strcmp0(key, "exit") == 0) {
            AnchorConfig *ac = current_or_new_anchor(false);
            if (!parse_bool_opt(val, &ac->exit_on_hit)) {
                fprintf(stderr, "[anchor] Invalid boolean for exit=%s\n", val);
                return -1;
            }
            if (ac->exit_on_hit) {
                fprintf(stderr,
                        "[anchor] warn: exit=1 cuts drcov/cflow/uftrace output, try pause=1\n");
            }
        } else {
            fprintf(stderr, "[anchor] Unknown parameter: %s\n", opt);
            return -1;
        }
    }

    if (num_anchors == 0) {
        fprintf(stderr, "[anchor] No anchors configured (specify sig= or va=)\n");
        return -1;
    }

    for (int a = 0; a < num_anchors; a++) {
        AnchorConfig *ac = &anchors[a];
        if (!ac->active) continue;
        if (!ac->use_sig && !ac->use_va) {
            fprintf(stderr, "[anchor] Anchor #%d has no trigger (sig= or va= required)\n", a);
            return -1;
        }
        if (ac->dumpva_expr && !ac->dumplen_expr && ac->mode != MODE_PE) {
            fprintf(stderr, "[anchor] Anchor #%d has dumpva=%s but neither dumplen= nor mode=pe is set\n",
                    a, ac->dumpva_expr);
            return -1;
        }
        if ((ac->dumplen_expr || ac->mode == MODE_PE) && !ac->dumpva_expr) {
            fprintf(stderr, "[anchor] Anchor #%d specifies dump mode/length without dumpva=\n", a);
            return -1;
        }

        if (ac->dumpva_expr) {
            char *err = NULL;
            bool warn_mix = false;
            if (!validate_expr_syntax(ac->dumpva_expr, 0, &warn_mix, &err)) {
                fprintf(stderr, "[anchor] Anchor #%d invalid dumpva='%s': %s\n",
                        a, ac->dumpva_expr, err ? err : "syntax error");
                g_free(err);
                return -1;
            }
            if (warn_mix) {
                fprintf(stderr,
                        "[anchor] warn: anchor #%d dumpva='%s': +/- bind tighter than &|^, add parens\n",
                        a, ac->dumpva_expr);
            }
        }

        if (ac->dumplen_expr) {
            char *err = NULL;
            bool warn_mix = false;
            if (!validate_expr_syntax(ac->dumplen_expr, 0, &warn_mix, &err)) {
                fprintf(stderr, "[anchor] Anchor #%d invalid dumplen='%s': %s\n",
                        a, ac->dumplen_expr, err ? err : "syntax error");
                g_free(err);
                return -1;
            }
            if (warn_mix) {
                fprintf(stderr,
                        "[anchor] warn: anchor #%d dumplen='%s': +/- bind tighter than &|^, add parens\n",
                        a, ac->dumplen_expr);
            }
        }

        if (ac->cond_expr) {
            char *err = NULL;
            bool warn_neg = false, warn_mix = false;
            if (!validate_cond_syntax(ac->cond_expr, 0, &warn_neg, &warn_mix, &err)) {
                fprintf(stderr, "[anchor] Anchor #%d invalid cond='%s': %s\n",
                        a, ac->cond_expr, err ? err : "syntax error");
                g_free(err);
                return -1;
            }
            if (warn_neg) {
                fprintf(stderr,
                        "[anchor] warn: anchor #%d cond='%s': negative literal, compare is unsigned u64\n",
                        a, ac->cond_expr);
            }
            if (warn_mix) {
                fprintf(stderr,
                        "[anchor] warn: anchor #%d cond='%s': +/- bind tighter than &|^, add parens\n",
                        a, ac->cond_expr);
            }
        }
    }

    if (log_path) {
        g_autofree char *parent = g_path_get_dirname(log_path);
        if (parent && g_strcmp0(parent, ".") != 0) {
            g_mkdir_with_parents(parent, 0755);
        }
        log_fp = fopen(log_path, "w");
        if (!log_fp) {
            fprintf(stderr, "[anchor] Cannot open log file %s: %s\n", log_path, strerror(errno));
            return -1;
        }
    }

    if (opt_async_write) {
        g_atomic_int_set(&writer_running, 1);
        writer_thread = g_thread_new("anchor-writer", writer_thread_func, NULL);
    }

    g_autofree char *start_msg = g_strdup_printf(
        "{\"ts\":%lld,\"pid\":%d,\"event\":\"plugin_start\",\"status\":\"running\","
        "\"async_write\":%s,\"entropy\":%s,\"sha256\":%s}",
        (long long)g_get_real_time(), (int)getpid(),
        opt_async_write ? "true" : "false",
        opt_entropy ? "true" : "false",
        opt_sha256 ? "true" : "false");
    log_json_line(start_msg);

    qemu_plugin_register_vcpu_init_cb(id, vcpu_init_cb, NULL);
    qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans_cb, NULL);
    qemu_plugin_register_atexit_cb(id, plugin_atexit_cb, NULL);

    return 0;
}
