"""Python reference models for the optimised verifier's data representations.

Not part of any proof; used to unit-test generated kernels.
"""
from __future__ import annotations

M64 = (1 << 64) - 1
M256 = (1 << 256) - 1
Q = 8380417

RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
ROT = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
       41, 45, 15, 21, 8, 18, 2, 61, 56, 14]


def rotl64(x, n):
    return ((x << n) | (x >> (64 - n))) & M64 if n else x


def keccak_f(a):
    a = list(a)
    for rnd in range(24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ rotl64(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl64(a[x + 5 * y], ROT[x + 5 * y])
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)]) for i in range(25)]
        a = [v & M64 for v in a]
        a[0] ^= RC[rnd]
    return a


# ── 4-way bit interleaving: bit b of slot k at position 4b + k ──────────────

def spread(x):
    r = 0
    for b in range(64):
        if (x >> b) & 1:
            r |= 1 << (4 * b)
    return r


def interleave(lanes4):
    return spread(lanes4[0]) | spread(lanes4[1]) << 1 | spread(lanes4[2]) << 2 | spread(lanes4[3]) << 3


def compress(w):
    r = 0
    for b in range(64):
        if (w >> (4 * b)) & 1:
            r |= 1 << b
    return r


def deinterleave(w):
    return [compress(w >> k) for k in range(4)]


def packed(lanes4):
    """Arithmetic packing: lane k at bits [64k, 64k + 64)."""
    return sum((v & M64) << (64 * k) for k, v in enumerate(lanes4))


def unpacked(w):
    return [(w >> (64 * k)) & M64 for k in range(4)]


def bytes_to_lanes(b):
    assert len(b) % 8 == 0
    return [int.from_bytes(b[i:i + 8], "little") for i in range(0, len(b), 8)]


def lanes_to_bytes(lanes):
    return b"".join(v.to_bytes(8, "little") for v in lanes)


# ── FIPS 204 verification model (for intermediate-value debugging) ──────────
import hashlib

PARAMS = {
    44: dict(k=4, l=4, eta=2, tau=39, lam=128, g1bits=17, g2=(Q - 1) // 88, omega=80),
    65: dict(k=6, l=5, eta=4, tau=49, lam=192, g1bits=19, g2=(Q - 1) // 32, omega=55),
    87: dict(k=8, l=7, eta=2, tau=60, lam=256, g1bits=19, g2=(Q - 1) // 32, omega=75),
}


def derived(nn):
    p = dict(PARAMS[nn])
    p["beta"] = p["tau"] * p["eta"]
    p["g1"] = 1 << p["g1bits"]
    p["zbits"] = p["g1bits"] + 1
    p["zbytes"] = 32 * p["zbits"]
    p["ctb"] = p["lam"] // 4
    p["m"] = (Q - 1) // (2 * p["g2"])
    p["w1bits"] = (p["m"] - 1).bit_length()
    p["pklen"] = 32 + 320 * p["k"]
    p["siglen"] = p["ctb"] + p["l"] * p["zbytes"] + p["omega"] + p["k"]
    return p


def brv8(i):
    return int(f"{i:08b}"[::-1], 2)


ZETAS = [pow(1753, brv8(i), Q) for i in range(256)]


def ntt(w):
    w = list(w)
    m = 0
    ln = 128
    while ln >= 1:
        for start in range(0, 256, 2 * ln):
            m += 1
            z = ZETAS[m]
            for j in range(start, start + ln):
                t = z * w[j + ln] % Q
                w[j + ln] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
        ln //= 2
    return w


def intt(w):
    w = list(w)
    m = 256
    ln = 1
    while ln < 256:
        for start in range(0, 256, 2 * ln):
            m -= 1
            z = Q - ZETAS[m]
            for j in range(start, start + ln):
                t = w[j]
                w[j] = (t + w[j + ln]) % Q
                w[j + ln] = z * (t - w[j + ln]) % Q
        ln *= 2
    return [x * 8347681 % Q for x in w]


def bits_le(b):
    return int.from_bytes(b, "little")


def rej_ntt_poly(seed):
    out = hashlib.shake_128(seed).digest(1008)
    a = []
    for t in range(336):
        if len(a) == 256:
            break
        v = out[3 * t] | out[3 * t + 1] << 8 | (out[3 * t + 2] & 0x7F) << 16
        if v < Q:
            a.append(v)
    return a if len(a) == 256 else None


def sample_in_ball(seed, tau):
    out = hashlib.shake_256(seed).digest(272)
    signs = int.from_bytes(out[:8], "little")
    c = [0] * 256
    p = 8
    for i in range(256 - tau, 256):
        while True:
            if p >= 272:
                return None
            j = out[p]
            p += 1
            if j <= i:
                break
        c[i] = c[j]
        c[j] = Q - 1 if (signs >> (i + tau - 256)) & 1 else 1
    return c


def use_hint(h, r, g2):
    m = (Q - 1) // (2 * g2)
    rp = r % Q
    r0 = rp % (2 * g2)
    if r0 > g2:
        r0 -= 2 * g2
    if rp - r0 == Q - 1:
        r1, r0 = 0, r0 - 1
    else:
        r1 = (rp - r0) // (2 * g2)
    if h == 1 and r0 > 0:
        return (r1 + 1) % m
    if h == 1 and r0 <= 0:
        return (r1 - 1) % m
    return r1


def verify_model(nn, cd):
    """Returns (verdict, dict of intermediates). Exact FIPS 204 Verify, ctx = ""."""
    p = derived(nn)
    k, l = p["k"], p["l"]
    if len(cd) < p["pklen"] + p["siglen"]:
        return 0, {}
    pk, sig, msg = cd[:p["pklen"]], cd[p["pklen"]:p["pklen"] + p["siglen"]], cd[p["pklen"] + p["siglen"]:]
    rho = pk[:32]
    t1 = []
    for i in range(k):
        v = bits_le(pk[32 + 320 * i:32 + 320 * (i + 1)])
        t1.append([(v >> (10 * j)) & 1023 for j in range(256)])
    ct = sig[:p["ctb"]]
    z = []
    ok_norm = True
    for i in range(l):
        off = p["ctb"] + p["zbytes"] * i
        v = bits_le(sig[off:off + p["zbytes"]])
        raw = [(v >> (p["zbits"] * j)) & ((1 << p["zbits"]) - 1) for j in range(256)]
        zi = [(p["g1"] - r) % Q for r in raw]
        for r in raw:
            zz = p["g1"] - r
            if abs(zz) >= p["g1"] - p["beta"]:
                ok_norm = False
        z.append(zi)
    hb = sig[p["ctb"] + l * p["zbytes"]:]
    h = [[0] * 256 for _ in range(k)]
    ok_hint = True
    idx = 0
    omega = p["omega"]
    for i in range(k):
        bound = hb[omega + i]
        if bound < idx or bound > omega:
            ok_hint = False
            break
        first = idx
        while idx < bound:
            if idx > first and hb[idx - 1] >= hb[idx]:
                ok_hint = False
            h[i][hb[idx]] = 1
            idx += 1
    if ok_hint:
        for j in range(idx, omega):
            if hb[j] != 0:
                ok_hint = False
    tr = hashlib.shake_256(pk).digest(64)
    mu = hashlib.shake_256(tr + b"\0\0" + msg).digest(64)
    c = sample_in_ball(ct, p["tau"])
    inter = dict(tr=tr, mu=mu, z=z, t1=t1, h=h, c=c, ok_norm=ok_norm, ok_hint=ok_hint)
    if c is None:
        return 0, inter
    A = [[rej_ntt_poly(rho + bytes([s, r])) for s in range(l)] for r in range(k)]
    if any(a is None for row in A for a in row):
        return 0, inter
    zh = [ntt(zi) for zi in z]
    ch = ntt(c)
    th = [ntt([x << 13 for x in t]) for t in t1]
    wh = [[(sum(A[r][s][j] * zh[s][j] for s in range(l)) - ch[j] * th[r][j]) % Q for j in range(256)]
          for r in range(k)]
    w = [intt(x) for x in wh]
    w1 = [[use_hint(h[r][j], w[r][j], p["g2"]) for j in range(256)] for r in range(k)]
    enc = b""
    for r in range(k):
        v = 0
        for j in range(256):
            v |= w1[r][j] << (p["w1bits"] * j)
        enc += v.to_bytes(32 * p["w1bits"], "little")
    ct2 = hashlib.shake_256(mu + enc).digest(p["ctb"])
    inter.update(A=A, zh=zh, ch=ch, th=th, wh=wh, w=w, w1=w1, enc=enc, ct2=ct2)
    return int(ok_norm and ok_hint and ct2 == ct), inter
