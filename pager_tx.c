/*
 * pager_tx.c — POCSAG / FLEX 寻呼发射机 (USRP/B210, UHD)
 *
 * 支持汉字消息: UTF-8 输入自动转 GB2312, 按 7bit 字母数字格式发送
 * (GB 字节剥掉最高位, 寻呼机收到后自行补回)。
 *
 * FLEX 部分协议实现参照 multimon-ng (demod_flex.c / bch.c) 逆向整理,
 * BCH(31,21) 编码表移植自 multimon-ng bch.c (public domain / unlicense)。
 *
 * 编译: make (有 libuhd-dev 时自动启用射频发射, 否则只能 -o 输出基带文件)
 */
#include <complex.h>
#include <errno.h>
#include <getopt.h>
#include <iconv.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#ifdef WITH_UHD
#include <uhd.h>
#endif

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

/* ================= POCSAG ================= */

#define SYNC_WORD     0x7CD215D8u
#define IDLE_WORD     0x7A89C197u
#define PREAMBLE_BITS 576
#define POCSAG_FDEV   4500.0   /* POCSAG 频偏 ±4.5 kHz */
#define ETX           0x03

typedef struct {
    uint8_t *bits;   /* 每字节存 1 bit */
    size_t nbits, cap;
} bitvec;

static void bv_put(bitvec *bv, int bit)
{
    if (bv->nbits == bv->cap) {
        bv->cap = bv->cap ? bv->cap * 2 : 4096;
        bv->bits = realloc(bv->bits, bv->cap);
        if (!bv->bits) { perror("realloc"); exit(1); }
    }
    bv->bits[bv->nbits++] = bit ? 1 : 0;
}

static void bv_put_word(bitvec *bv, uint32_t w)   /* MSB first */
{
    for (int i = 31; i >= 0; i--)
        bv_put(bv, (w >> i) & 1);
}

/* BCH(31,21) + 偶校验, 输入 21 数据位, 输出完整 32bit 码字 */
static uint32_t bch_encode(uint32_t data21)
{
    const uint32_t G = 0x769;   /* x^10+x^9+x^8+x^6+x^5+x^3+1 */
    uint32_t rem = (data21 & 0x1FFFFFu) << 10;
    for (int i = 30; i >= 10; i--)
        if (rem & (1u << i))
            rem ^= G << (i - 10);
    uint32_t cw = ((data21 & 0x1FFFFFu) << 11) | ((rem & 0x3FFu) << 1);
    uint32_t p = cw;
    p ^= p >> 16; p ^= p >> 8; p ^= p >> 4; p ^= p >> 2; p ^= p >> 1;
    return cw | (p & 1u);       /* bit0 = 偶校验位 */
}

static uint32_t address_codeword(uint32_t ric, int func)
{
    uint32_t addr18 = (ric >> 3) & 0x3FFFFu;
    return bch_encode((addr18 << 2) | (uint32_t)(func & 3));  /* bit31=0 */
}

static uint32_t message_codeword(uint32_t data20)
{
    return bch_encode((1u << 20) | (data20 & 0xFFFFFu));      /* bit31=1 */
}

/* 追加一个 7bit 字符, POCSAG 规定 LSB 先发 */
static void append_char7(bitvec *msg, uint8_t c)
{
    c &= 0x7F;
    for (int i = 0; i < 7; i++)
        bv_put(msg, (c >> i) & 1);
}

/* GB2312 字节流 -> 消息比特流; 汉字字节剥最高位, 末尾填充:
 * 全角模式用全角空格(0xA1A1->0x21 0x21, 显示为空白), 否则按惯例用 ETX */
static void build_message_bits(const uint8_t *gb, size_t len, bitvec *msg,
                               int fullwidth)
{
    for (size_t i = 0; i < len; i++)
        append_char7(msg, gb[i] & 0x7F);
    if (fullwidth) {
        while (msg->nbits % 20) {
            append_char7(msg, 0x21);
            append_char7(msg, 0x21);
        }
    } else {
        append_char7(msg, ETX);
        while (msg->nbits % 20)
            append_char7(msg, ETX);
    }
}

/* 组帧: 前导码 + [同步字 + 16 码字]*N 批次, 地址码放在 RIC%8 对应的帧 */
static void build_frame_bits(bitvec *out, uint32_t ric, int func, const bitvec *msg)
{
    size_t n_msg = msg->nbits / 20;
    int frame = ric & 7;
    size_t first_cap = 15 - 2 * (size_t)frame;   /* 首批地址码之后可容纳的消息码字数 */
    size_t pos = 0;
    int first = 1;

    for (int i = 0; i < PREAMBLE_BITS; i++)      /* 1010... */
        bv_put(out, (i & 1) ^ 1);

    while (first || pos < n_msg) {
        bv_put_word(out, SYNC_WORD);
        if (first) {
            for (int i = 0; i < 2 * frame; i++)
                bv_put_word(out, IDLE_WORD);
            bv_put_word(out, address_codeword(ric, func));
        }
        size_t cap = first ? first_cap : 16, k = 0;
        while (k < cap && pos < n_msg) {
            uint32_t d = 0;
            for (int j = 0; j < 20; j++)
                d = (d << 1) | msg->bits[pos * 20 + j];
            bv_put_word(out, message_codeword(d));
            k++; pos++;
        }
        size_t used = first ? (size_t)(2 * frame + 1) + k : k;
        for (size_t i = used; i < 16; i++)
            bv_put_word(out, IDLE_WORD);
        first = 0;
    }
}

/* ================= FLEX (1600bps 2FSK) ================= */

#define FLEX_SYNC_CODE    0x870C       /* 1600/2FSK 同步码 */
#define FLEX_MARKER       0xA6C6AAAAu  /* 同步标记 */
#define FLEX_DOTTING      16           /* 同步字与 FIW 之间的点频比特数 */
#define FLEX_SYNC2_BITS   40           /* 25ms @1600 */
#define FLEX_DATA_BITS    2816         /* 1760ms @1600 = 88 码字 */
#define FLEX_PHASE_WORDS  88
#define FLEX_FRAME_SYMS   3000         /* 1.875s @1600 */
#define FLEX_FDEV         4800.0       /* FLEX 2FSK 频偏 ±4.8 kHz */
#define FLEX_BAUD         1600.0
#define FLEX_MAX_CHARS    251          /* 单帧最大 7bit 字符数 */

/* ---- FLEX BCH(31,21,2), 移植自 multimon-ng bch.c (public domain) ---- */

static uint8_t flex_gf_exp[32], flex_gf_log[32];
static uint16_t flex_par_tbl[21];
static int flex_bch_ready = 0;

static uint8_t flex_gf_mult(uint8_t a, uint8_t b)
{
    if (!a || !b) return 0;
    return flex_gf_exp[(flex_gf_log[a] + flex_gf_log[b]) % 31];
}

static void flex_bch_init(void)
{
    if (flex_bch_ready) return;
    unsigned int elem = 1;              /* GF(2^5), 本原多项式 x^5+x^2+1 (0x25) */
    for (int i = 0; i < 31; i++) {
        flex_gf_exp[i] = (uint8_t)elem;
        flex_gf_log[elem] = (uint8_t)i;
        elem <<= 1;
        if (elem & 0x20) elem ^= 0x25;
    }
    flex_gf_log[0] = 0;
    /* 生成多项式: 根 alpha^1..alpha^4 及其共轭 */
    int seen[32] = {0}, roots[10], nr = 0;
    for (int r = 1; r <= 4; r++) {
        int v = r;
        while (!seen[v]) { seen[v] = 1; roots[nr++] = v; v = (v * 2) % 31; }
    }
    uint8_t gen[11] = {0};
    gen[0] = 1;
    int deg = 0;
    for (int r = 0; r < nr; r++) {
        uint8_t ar = flex_gf_exp[roots[r]];
        for (int j = deg + 1; j > 0; j--)
            gen[j] = gen[j - 1] ^ flex_gf_mult(gen[j], ar);
        gen[0] = flex_gf_mult(gen[0], ar);
        deg++;
    }
    /*  parity 表: 单个数据位经 LFSR 编码的结果 */
    for (int db = 0; db < 21; db++) {
        uint8_t bb[10] = {0};
        for (int i = 20; i >= 0; i--) {
            int fb = ((i == 20 - db) ? 1 : 0) ^ bb[9];
            if (fb) {
                for (int j = 9; j > 0; j--)
                    bb[j] = gen[j] ? (bb[j - 1] ^ 1) : bb[j - 1];
                bb[0] = gen[0] ? 1 : 0;
            } else {
                for (int j = 9; j > 0; j--) bb[j] = bb[j - 1];
                bb[0] = 0;
            }
        }
        uint16_t p = 0;
        for (int i = 0; i < 10; i++)
            if (bb[i]) p |= (uint16_t)(1 << (9 - i));
        flex_par_tbl[db] = p;
    }
    flex_bch_ready = 1;
}

/* FLEX 32bit 码字: bit0-20 数据, bit21-30 BCH 校验, bit31 偶校验 */
static uint32_t flex_bch_encode(uint32_t data21)
{
    flex_bch_init();
    uint32_t par = 0, d = data21 & 0x1FFFFFu;
    for (int b = 0; b < 21; b++)
        if (d & (1u << b)) par ^= flex_par_tbl[b];
    uint32_t w = d | (par << 21);
    uint32_t p = w;
    p ^= p >> 16; p ^= p >> 8; p ^= p >> 4; p ^= p >> 2; p ^= p >> 1;
    return w | ((p & 1u) << 31);
}

/* 写 nbits 个符号; msb_first 控制位序; inv=1 用于同步段 (极性与数据段相反) */
static void put_syms(int8_t *s, int *pos, uint32_t v, int nbits,
                     int msb_first, int inv)
{
    for (int i = 0; i < nbits; i++) {
        int bit = msb_first ? (v >> (nbits - 1 - i)) & 1 : (v >> i) & 1;
        if (inv) bit ^= 1;
        s[(*pos)++] = bit ? 1 : -1;     /* +1 = +频偏 */
    }
}

/*
 * 组一个 FLEX 帧 (3000 符号 = 1.875s):
 * [S(16)][marker(32)][~S(16)][点频(16)][FIW(32)][SYNC2空位(40)][数据(2816)][填充(32)]
 * 同步段符号 1 -> -频偏; 数据段(含FIW) 1 -> +频偏 (参照 multimon-ng)。
 */
static void flex_build_frame(int8_t *s, uint32_t capcode,
                             const uint8_t *chars, int nchars,
                             int cycle, int frame, uint8_t pad)
{
    const uint16_t S = FLEX_SYNC_CODE;
    int p = 0;
    put_syms(s, &p, S, 16, 1, 1);
    put_syms(s, &p, FLEX_MARKER, 32, 1, 1);
    put_syms(s, &p, (~S) & 0xFFFF, 16, 1, 1);
    for (int i = 0; i < FLEX_DOTTING; i++)      /* 点频, 内容被解码器跳过 */
        s[p++] = (i & 1) ? 1 : -1;

    /* FIW: bit0-3 校验和, bit4-7 cycle, bit8-14 frame, bit15-20 fix3(=0) */
    uint32_t cks = (15u - ((uint32_t)cycle + (frame & 0xF) + (frame >> 4))) & 0xF;
    uint32_t fiw = flex_bch_encode(cks | ((uint32_t)cycle << 4) | ((uint32_t)frame << 8));
    put_syms(s, &p, fiw, 32, 0, 0);             /* LSB 先发 */
    for (int i = 0; i < FLEX_SYNC2_BITS; i++)   /* SYNC2 空位 */
        s[p++] = (i & 1) ? 1 : -1;

    /* 逻辑码字: 0=BIW, 1=地址, 2=向量, 3=消息头, 4..=消息 */
    uint32_t lw[FLEX_PHASE_WORDS] = {0};
    int nwords = (nchars + 1 + 2) / 3;          /* 消息数据字数(首字第1字符槽被跳过) */
    int len = nwords + 1;                       /* 含消息头 */
    lw[0] = flex_bch_encode(2u << 10);          /* BIW: aoffset=1, voffset=2 */
    lw[1] = flex_bch_encode(capcode + 0x8000u); /* 短地址 */
    lw[2] = flex_bch_encode(((uint32_t)len << 14) | (3u << 7) | (5u << 4)); /* mw1=3, ALN */
    lw[3] = flex_bch_encode(3u << 11);          /* 消息头: frag=3(完整), cont=0 */
    int ci = 0;
    for (int w = 0; w < nwords; w++) {
        uint32_t d = ETX;                       /* 首字第1字符槽: 解码器跳过 */
        if (w > 0) d = ci < nchars ? chars[ci++] : pad;
        d |= (uint32_t)(ci < nchars ? chars[ci++] : pad) << 7;
        d |= (uint32_t)(ci < nchars ? chars[ci++] : pad) << 14;
        lw[4 + w] = flex_bch_encode(d);
    }

    /* 8 块交织: 逻辑字 L 的第 k 位 -> 线位 (L&~7)+(k>>2) 字内 (L&7)+((k&3)<<3) */
    int base = p;                               /* == 152 */
    for (int L = 0; L < FLEX_PHASE_WORDS; L++)
        for (int k = 0; k < 32; k++) {
            int pos = base + ((L & ~7) + (k >> 2)) * 32 + (L & 7) + ((k & 3) << 3);
            s[pos] = (lw[L] >> k) & 1 ? 1 : -1;
        }
    p = base + FLEX_DATA_BITS;
    while (p < FLEX_FRAME_SYMS) { s[p] = (p & 1) ? 1 : -1; p++; }   /* 填满 1.875s */
}

/* ================= 公共: 编码/调制 ================= */

static uint8_t *to_gb2312(const char *utf8, size_t *out_len)
{
    size_t il = strlen(utf8), cap = il * 2 + 16, ol = cap;
    uint8_t *out = malloc(cap);
    char *ip = (char *)utf8, *op = (char *)out;
    /* 先严格转换, 有无法表示的字符(emoji/生僻字等)则警告后跳过 */
    iconv_t cd = iconv_open("GB2312", "UTF-8");
    if (cd != (iconv_t)-1) {
        if (iconv(cd, &ip, &il, &op, &ol) != (size_t)-1) {
            iconv_close(cd);
            *out_len = (size_t)(op - (char *)out);
            return out;
        }
        iconv_close(cd);
        fprintf(stderr, "警告: 消息含 GB2312 无法表示的字符, 将被跳过\n");
    }
    ip = (char *)utf8; op = (char *)out;
    il = strlen(utf8); ol = cap;
    cd = iconv_open("GB2312//IGNORE", "UTF-8");
    if (cd != (iconv_t)-1) {
        if (iconv(cd, &ip, &il, &op, &ol) != (size_t)-1) {
            iconv_close(cd);
            *out_len = (size_t)(op - (char *)out);
            return out;
        }
        iconv_close(cd);
        fprintf(stderr, "警告: UTF-8->GB2312 转换失败, 按原始字节发送\n");
    }
    memcpy(out, utf8, il);
    *out_len = il;
    return out;
}

/* POCSAG: 0 -> +4.5kHz, 1 -> -4.5kHz (-i 反转) */
static float _Complex *modulate(const bitvec *bv, double srate, double baud,
                                int invert, size_t *out_n)
{
    size_t n = (size_t)(bv->nbits * srate / baud) + (size_t)(srate * 0.005);
    float _Complex *buf = calloc(n, sizeof *buf);
    if (!buf) { perror("calloc"); exit(1); }
    double phase = 0.0, bitpos = 0.0, inc = baud / srate;
    for (size_t i = 0; i < n; i++) {
        size_t b = (size_t)bitpos;
        int bit = (b < bv->nbits) ? bv->bits[b] : 1;
        int hi = invert ? bit : !bit;
        phase += 2.0 * M_PI * (hi ? POCSAG_FDEV : -POCSAG_FDEV) / srate;
        buf[i] = 0.7f * (cosf((float)phase) + sinf((float)phase) * I);
        bitpos += inc;
    }
    *out_n = n;
    return buf;
}

/* FLEX: 符号 +1 -> +4.8kHz, -1 -> -4.8kHz */
static float _Complex *flex_modulate(const int8_t *syms, int nsyms,
                                     double srate, size_t *out_n)
{
    size_t n = (size_t)(nsyms * srate / FLEX_BAUD);   /* 帧与帧之间严格 1.875s */
    float _Complex *buf = calloc(n, sizeof *buf);
    if (!buf) { perror("calloc"); exit(1); }
    double phase = 0.0, sympos = 0.0, inc = FLEX_BAUD / srate;
    for (size_t i = 0; i < n; i++) {
        size_t k = (size_t)sympos;
        int sym = (k < (size_t)nsyms) ? syms[k] : 1;
        phase += 2.0 * M_PI * sym * FLEX_FDEV / srate;
        buf[i] = 0.7f * (cosf((float)phase) + sinf((float)phase) * I);
        sympos += inc;
    }
    *out_n = n;
    return buf;
}

/* ================= UHD 发射 ================= */

#ifdef WITH_UHD
typedef struct {
    uhd_usrp_handle usrp;
    uhd_tx_streamer_handle tx;
    size_t maxn;
} uhd_ctx;

static void uhd_err(const char *what)
{
    char s[512];
    uhd_get_last_error(s, sizeof s);
    fprintf(stderr, "%s: %s\n", what, s);
}

static int uhd_open(uhd_ctx *c, const char *dev_args,
                    double freq, double srate, double gain)
{
    if (uhd_usrp_make(&c->usrp, dev_args) != UHD_ERROR_NONE) {
        uhd_err("uhd_usrp_make");
        return 1;
    }
    uhd_usrp_set_tx_rate(c->usrp, srate, 0);
    uhd_tune_request_t tr = {
        .target_freq = freq,
        .rf_freq_policy = UHD_TUNE_REQUEST_POLICY_AUTO,
        .dsp_freq_policy = UHD_TUNE_REQUEST_POLICY_AUTO,
    };
    uhd_tune_result_t tres;
    uhd_usrp_set_tx_freq(c->usrp, &tr, 0, &tres);
    fprintf(stderr, "实际发射频率: %.6f MHz, 采样率 %.0f sps\n",
            tres.actual_rf_freq / 1e6, srate);
    uhd_usrp_set_tx_gain(c->usrp, gain, 0, "");
    usleep(200000);   /* 等本振稳定 */

    size_t chan = 0;
    uhd_stream_args_t sa = {
        .cpu_format = "fc32", .otw_format = "sc16",
        .args = "", .channel_list = &chan, .n_channels = 1,
    };
    uhd_tx_streamer_make(&c->tx);
    if (uhd_usrp_get_tx_stream(c->usrp, &sa, c->tx) != UHD_ERROR_NONE) {
        uhd_err("get_tx_stream");
        return 1;
    }
    uhd_tx_streamer_max_num_samps(c->tx, &c->maxn);
    return 0;
}

static int uhd_send(uhd_ctx *c, const float _Complex *buf, size_t n,
                    int sob, int eob)
{
    uhd_tx_metadata_handle md;
    uhd_tx_metadata_make(&md, false, 0, 0, sob, false);
    size_t off = 0;
    while (off < n) {
        size_t chunk = n - off > c->maxn ? c->maxn : n - off;
        const void *ptrs[1] = { buf + off };
        size_t sent = 0;
        if (uhd_tx_streamer_send(c->tx, ptrs, chunk, &md, 1.0, &sent)
                != UHD_ERROR_NONE) {
            uhd_err("send");
            uhd_tx_metadata_free(&md);
            return 1;
        }
        off += sent;
    }
    uhd_tx_metadata_free(&md);
    if (eob) {
        uhd_tx_metadata_make(&md, false, 0, 0, false, true);
        const void *ptrs[1] = { buf };
        size_t sent;
        uhd_tx_streamer_send(c->tx, ptrs, 0, &md, 1.0, &sent);
        uhd_tx_metadata_free(&md);
    }
    return 0;
}

static void uhd_close(uhd_ctx *c)
{
    usleep(200000);
    uhd_tx_streamer_free(&c->tx);
    uhd_usrp_free(&c->usrp);
}
#endif /* WITH_UHD */

/* ================= main ================= */

static void usage(const char *p)
{
    fprintf(stderr,
        "用法: %s [-p 协议] -f 频率 -r 速率 -a 地址码 -m 消息 [选项]\n"
        "  -p PROTO  pocsag (默认) 或 flex (1600bps 2FSK)\n"
        "  -f FREQ   发射频率 Hz, 如 155400000 或 155.4e6\n"
        "  -r RATE   速率: POCSAG 512/1200/2400, FLEX 1600\n"
        "  -a RIC    地址码 (POCSAG 0..2097151, FLEX 0..1933310)\n"
        "  -m MSG    消息文本 (UTF-8, 中文自动转 GB2312)\n"
        "  -F FUNC   POCSAG 功能位 0-3 (默认 3 = 字母数字/中文)\n"
        "  -g GAIN   发射增益 dB (默认 40)\n"
        "  -s SRATE  基带采样率 (默认 1000000)\n"
        "  -n N      POCSAG: 重复次数(默认1); FLEX: 连续帧数(默认16=30s)\n"
        "  -i        反转 FSK 极性 (仅 POCSAG, 收不到时试试)\n"
        "  -o FILE   不发射, 把基带 fc32 写入文件\n"
        "  -A ARGS   UHD 设备参数, 如 \"serial=xxxx\"\n"
        "  -W        关闭 ASCII 转全角(默认开启; 纯英文寻呼机用)\n"
        "  -h        帮助\n", p);
}

int main(int argc, char **argv)
{
    double freq = 0, srate = 1e6, gain = 40;
    long rate = 0, ric = -1;
    int func = 3, invert = 0, repeats = 0, proto_flex = 0, fullwidth = 1;
    const char *msg = NULL, *ofile = NULL, *dev_args = "";
    int c;

    while ((c = getopt(argc, argv, "p:f:r:a:m:F:g:s:n:io:A:Wh")) != -1) {
        switch (c) {
        case 'p': proto_flex = !strcmp(optarg, "flex"); break;
        case 'f': freq = strtod(optarg, NULL); break;
        case 'r': rate = atol(optarg); break;
        case 'a': ric = atol(optarg); break;
        case 'm': msg = optarg; break;
        case 'F': func = atoi(optarg); break;
        case 'g': gain = strtod(optarg, NULL); break;
        case 's': srate = strtod(optarg, NULL); break;
        case 'n': repeats = atoi(optarg); break;
        case 'i': invert = 1; break;
        case 'o': ofile = optarg; break;
        case 'A': dev_args = optarg; break;
        case 'W': fullwidth = 0; break;
        default: usage(argv[0]); return 1;
        }
    }
    if (repeats == 0) repeats = proto_flex ? 16 : 1;

    size_t gb_len = 0;
    uint8_t *gb = NULL;
    if (msg) gb = to_gb2312(msg, &gb_len);

    /* ASCII 可打印字符转 GB2312 全角: 汉字机把 GB 区间的字节对都拼成汉字,
     * 半角 "11" 会被拼成 0xB1B1=北; 全角 １=0xA3B1 无歧义(-W 关闭) */
    if (fullwidth && gb) {
        uint8_t *fw = malloc(gb_len * 2 + 1);
        size_t n = 0;
        for (size_t i = 0; i < gb_len; i++) {
            uint8_t b = gb[i];
            if (b == 0x20) { fw[n++] = 0xA1; fw[n++] = 0xA1; }
            else if (b > 0x20 && b < 0x7F) { fw[n++] = 0xA3; fw[n++] = 0xA1 + (b - 0x21); }
            else fw[n++] = b;   /* 汉字双字节(>=0xA1)和控制符原样保留 */
        }
        free(gb); gb = fw; gb_len = n;
    }

    if (!proto_flex) {
        /* ---------------- POCSAG ---------------- */
        if (freq <= 0 || (rate != 512 && rate != 1200 && rate != 2400) ||
            ric < 0 || ric > 0x1FFFFF || !msg) {
            usage(argv[0]);
            return 1;
        }
        bitvec mbits = {0}, fbits = {0};
        build_message_bits(gb, gb_len, &mbits, fullwidth);
        build_frame_bits(&fbits, (uint32_t)ric, func, &mbits);
        fprintf(stderr,
            "POCSAG 地址码 %ld (帧 %ld), 功能位 %d, 速率 %ld bps\n"
            "消息 %zu 字节(GB2312), %zu 个消息码字; 共 %zu bit, 空中时长 %.2f s\n",
            ric, ric & 7, func, rate,
            gb_len, mbits.nbits / 20, fbits.nbits, (double)fbits.nbits / rate);

        size_t nsamps;
        float _Complex *buf = modulate(&fbits, srate, (double)rate, invert, &nsamps);
        int rc = 0;
        if (ofile) {
            FILE *f = fopen(ofile, "wb");
            if (!f) { fprintf(stderr, "%s: %s\n", ofile, strerror(errno)); return 1; }
            for (int r = 0; r < repeats; r++)
                fwrite(buf, sizeof *buf, nsamps, f);
            fclose(f);
            fprintf(stderr, "基带已写入 %s (fc32, %zu 样点 x %d)\n", ofile, nsamps, repeats);
        } else {
#ifdef WITH_UHD
            uhd_ctx u;
            if (uhd_open(&u, dev_args, freq, srate, gain)) return 1;
            for (int r = 0; r < repeats && !rc; r++) {
                rc = uhd_send(&u, buf, nsamps, 1, r + 1 == repeats);
                if (r + 1 < repeats) usleep(300000);
            }
            uhd_close(&u);
#else
            fprintf(stderr, "本程序编译时未包含 UHD, 只能用 -o 输出文件。\n"
                            "安装 libuhd-dev 后重新 make 即可发射。\n");
            rc = 1;
#endif
        }
        free(mbits.bits); free(fbits.bits); free(buf); free(gb);
        return rc;
    }

    /* ---------------- FLEX 1600/2FSK ---------------- */
    if (freq <= 0 || rate != 1600 || ric < 0 || ric > 1933310 || !msg || gb_len == 0) {
        usage(argv[0]);
        return 1;
    }
    int nchars = (int)gb_len;
    if (nchars > FLEX_MAX_CHARS) {
        fprintf(stderr, "警告: 消息过长, 截断为 %d 个 7bit 字符\n", FLEX_MAX_CHARS);
        nchars = FLEX_MAX_CHARS;
    }
    uint8_t *chars = malloc(nchars);
    for (int i = 0; i < nchars; i++) chars[i] = gb[i] & 0x7F;

    /* 以当前 UTC 时间推算 cycle/frame, 连续编号发送 */
    time_t now = time(NULL);
    struct tm *tm = gmtime(&now);
    int sih = tm->tm_min * 60 + tm->tm_sec;
    int cycle = sih / 240, frame = (int)((sih % 240) / 1.875);
    fprintf(stderr,
        "FLEX 1600/2FSK capcode %ld, 消息 %d 个 7bit 字符; "
        "从 cycle %d frame %d 起连续发送 %d 帧 (每帧 1.875s)\n",
        ric, nchars, cycle, frame, repeats);

    int8_t *syms = malloc(FLEX_FRAME_SYMS);
    FILE *of = NULL;
    if (ofile) {
        of = fopen(ofile, "wb");
        if (!of) { fprintf(stderr, "%s: %s\n", ofile, strerror(errno)); return 1; }
    }
#ifdef WITH_UHD
    uhd_ctx u;
    int use_uhd = !ofile;
    if (use_uhd && uhd_open(&u, dev_args, freq, srate, gain)) return 1;
#endif
    int rc = 0;
    for (int r = 0; r < repeats && !rc; r++) {
        flex_build_frame(syms, (uint32_t)ric, chars, nchars, cycle, frame,
                         fullwidth ? 0x21 : ETX);   /* 全角模式用全角空格填充 */
        size_t nsamps;
        float _Complex *buf = flex_modulate(syms, FLEX_FRAME_SYMS, srate, &nsamps);
        if (of) {
            fwrite(buf, sizeof *buf, nsamps, of);
        }
#ifdef WITH_UHD
        else {
            rc = uhd_send(&u, buf, nsamps, r == 0, r + 1 == repeats);
        }
#endif
        free(buf);
        if (++frame == 128) { frame = 0; cycle = (cycle + 1) % 16; }
    }
    if (of) {
        fclose(of);
        fprintf(stderr, "基带已写入 %s (fc32, %d 帧)\n", ofile, repeats);
    }
#ifdef WITH_UHD
    if (use_uhd) uhd_close(&u);
#endif
#ifndef WITH_UHD
    if (!ofile) {
        fprintf(stderr, "本程序编译时未包含 UHD, 只能用 -o 输出文件。\n");
        rc = 1;
    }
#endif
    free(syms); free(chars); free(gb);
    return rc;
}
