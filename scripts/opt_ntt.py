"""4-lane SIMD NTT / inverse NTT kernels (FIPS 204 Algorithms 41 and 42).

A polynomial array is 256 words at P (coefficient t in word P + 32 t); each
word packs four independent polynomials in 64-bit lanes (lane k = bits
[64k, 64k + 64)). Every butterfly is a word operation with a scalar zeta.

Multiplication by a zeta is lane-wise Montgomery with R = 2^32:
    t = b * z'                      (z' = zeta * R mod q, per lane t < 2^64)
    m = ((t & M32) * QINV) & M32    (QINV = -q^-1 mod 2^32)
    u = (t + m q) >> 32             (low 32 bits of every lane are zero, so
                                     the shift needs no mask)
u == b * zeta (mod q) and u < t / 2^32 + q.

Forward (Cooley-Tukey), layers merged 3 + 3 + 2 with the operand words on the
stack:  a' = a + u,  b' = a + 2q - u.
  Bounds: inputs < 2^25. Each layer adds < 2q to a lane, so after layer L
  lanes are < 2^25 + 2Lq < 2^27.2. Montgomery input t < 2^27.2 * 2^23 = 2^50.2,
  so u < 2^18.2 + q < 2q (the subtraction never borrows). Outputs < 2^27.2.
Inverse (Gentleman-Sande), merged 2 + 3 + 3:  a' = a + b,
  b' = mont((b + C_L - a) * zeta_m) (= -zeta_m (a - b), Alg 42).
  Bounds: inputs < 2^27 (with `premont`, inputs < 2^58 are first
  Montgomery-reduced at load: x / 2^32 + q < 2^27, adding a factor R^-1);
  a-values at most double per layer, so before layer L
  lanes are < 2^(26+L) =: B; C_L = q * ceil(B / q) >= any a; Montgomery input
  < 2^(27+L) * 2^23 <= 2^58, u < 2^26 + q < 2^27. The 256^-1 * factor scaling
  is folded into layer 8: the zeta of its b-outputs is pre-multiplied and its
  a-outputs get one extra Montgomery multiplication. Outputs < 2^27.

Zeta source: pass A (layers 1-3 / 6-8) uses PUSH immediates; passes B and C
read per-block records from a table in memory written once by `gen_init`:
TB = 8 records x 7 words (layers 4-6 of block b), TC = 64 records x 3 words
(layers 7-8 of block b). The inverse walks the same records backwards.
"""
from __future__ import annotations

from opt_asm import Asm, Stack
from opt_ref import Q, ZETAS

R32 = 1 << 32
QINV = (-pow(Q, -1, R32)) % R32
LANES = lambda v: v | v << 64 | v << 128 | v << 192
M32X4 = LANES(R32 - 1)


def zm(m, factor=1):
    """Montgomery form of zeta_m (times factor)."""
    return ZETAS[m] * factor % Q * R32 % Q


def mont_top(a: Asm):
    a.op("DUP1")
    a.push(M32X4)
    a.op("AND")
    a.push(QINV)
    a.op("MUL")
    a.push(M32X4)
    a.op("AND")
    a.push(Q)
    a.op("MUL")
    a.op("ADD")
    a.push(32)
    a.op("SHR")


class Kernel:
    def __init__(self, a: Asm, table: int):
        self.a = a
        self.TB = table
        self.TC = table + 56 * 32
        self.size = (56 + 192) * 32

    # ── table ───────────────────────────────────────────────────────────
    def records(self):
        rec = []
        for b in range(8):
            rec += [zm(8 + b), zm(16 + 2 * b), zm(17 + 2 * b)] + [zm(32 + 4 * b + u) for u in range(4)]
        for b in range(64):
            rec += [zm(64 + b), zm(128 + 2 * b), zm(129 + 2 * b)]
        return rec

    def gen_init(self):
        a = self.a
        for i, v in enumerate(self.records()):
            a.push(v)
            a.push(self.TB + 32 * i)
            a.op("MSTORE")

    # ── butterflies ─────────────────────────────────────────────────────
    def zeta(self, st, z):
        """Push zeta: int immediate, or (pointer name, byte offset)."""
        if isinstance(z, int):
            st.push(z, "z")
        else:
            ptr, off = z
            st.dup(ptr, "z")
            if off:
                st.push(off, "c")
                st.op("ADD", 2, "z")
            st.op("MLOAD", 1, "z")

    def mont(self, st, x):
        """Montgomery-reduce stack value x (on top) in place; needs "M" on the stack."""
        st.dup(x, "m")
        st.dup("M", "mm")
        st.op("AND", 2, "m")
        st.push(QINV, "qi")
        st.op("MUL", 2, "m")
        st.dup("M", "mm")
        st.op("AND", 2, "m")
        st.push(Q, "q")
        st.op("MUL", 2, "m")
        st.op("ADD", 2, x)
        st.push(32, "s")
        st.op("SHR", 2, x)

    # v4 (`biased`): the inputs carry a bias of 8q (added by the z decoder),
    # which keeps every lane non-negative through the 8 layers without the
    # per-butterfly +2q: b' = a - u. Immediate zetas (pass A) use Shoup
    # multiplication: u = b zeta - ((b zeta') >> 32) q, zeta' = floor(zeta 2^32 / q),
    # u < q (1 + b / 2^32). Bounds (lanes < 2^27.2 throughout, outputs
    # < 2^28) in docs/opt.md, round 4.
    biased = False

    @staticmethod
    def shoup(z):
        return ZETAS[z] * R32 // Q

    def ct(self, st, ai, bi, z):
        """a' = a + mont(b z), b' = a + 2q - mont(b z) (biased: a - u)."""
        a = self.a
        st.to_top(bi)
        if self.biased and isinstance(z, int):
            # Shoup: z is the zeta index here
            st.dup(bi, "h")
            st.push(self.shoup(z), "zs")
            st.op("MUL", 2, "h")
            st.push(32, "s")
            st.op("SHR", 2, "h")
            st.dup("M", "mm")
            st.op("AND", 2, "h")
            st.push(Q, "q")
            st.op("MUL", 2, "h")
            st.swap(1)
            st.push(ZETAS[z], "z")
            st.op("MUL", 2, "u")
            st.op("SUB", 2, "u")
        else:
            self.zeta(st, z)
            st.op("MUL", 2, "u")
            self.mont(st, "u")
        st.dup(ai, "a1")
        st.dup("u", "u1")
        st.op("ADD", 2, "s")
        d = st.depth(ai)
        st.swap(d)                      # s -> a's slot, old a on top
        st.rename("s", ai)
        st.s[-1] = "aold"
        if not self.biased:
            st.dup("C", "c")
            st.op("ADD", 2, "ac")
        st.op("SUB", 2, bi)             # (a + 2q) - u, biased: a - u

    def gs(self, st, ai, bi, z, C=None, ascale=None):
        """a' = a + b, b' = mont((b + C - a) z) (C on the stack);
        optionally a' := mont(a' ascale)."""
        a = self.a
        st.to_top(bi)
        st.dup(ai, "a1")
        st.dup(bi, "b1")
        st.op("ADD", 2, "s")
        if ascale is not None:
            st.push(ascale, "f")
            st.op("MUL", 2, "s")
            self.mont(st, "s")
        d = st.depth(ai)
        st.swap(d)
        st.rename("s", ai)
        st.s[-1] = "aold"               # [.., b, aold]
        if self.biased:
            # v4: (C - a) + b, no swap
            st.dup("C", "c")
            st.op("SUB", 2, "ca")
            st.op("ADD", 2, "d")
        else:
            st.swap(1)                  # [.., aold, b]
            st.dup("C", "c")
            st.op("ADD", 2, "bc")
            st.op("SUB", 2, "d")        # (b + C) - a
        self.zeta(st, z)
        st.op("MUL", 2, bi)
        self.mont(st, bi)

    # ── memory ──────────────────────────────────────────────────────────
    def load(self, st, ptr, offs, mont=False):
        for i, o in enumerate(offs):
            st.dup(ptr, f"x{i}")
            if o:
                st.push(o, "c")
                st.op("ADD", 2, f"x{i}")
            st.op("MLOAD", 1, f"x{i}")
            if mont:
                self.mont(st, f"x{i}")

    # optional hook (st, name, ptr, off) applied to every output word of the
    # inverse NTT's last pass before it is stored (v4: fused UseHint)
    post = None

    def store(self, st, ptr, offs, post=None):
        n = len(offs)
        for _ in range(n):
            nm = st.top()
            i = int(nm[1:])
            if post:
                post(st, nm, ptr, offs[i])
            st.dup(ptr, "p")
            if offs[i]:
                st.push(offs[i], "c")
                st.op("ADD", 2, "p")
            st.op("MSTORE", 2)

    # ── forward ─────────────────────────────────────────────────────────
    def gen_ntt(self, name):
        a = self.a
        a.region(name)
        a.label(name)
        st = Stack(a, ["ret", "P"])
        st.push(M32X4, "M")
        C = [] if self.biased else ["C"]
        if not self.biased:
            st.push(LANES(2 * Q), "C")
        # pass A: layers 1-3, words j + 32 i, j < 32
        st.dup("P", "end")
        st.push(32 * 32, "c")
        st.op("ADD", 2, "end")
        st.dup("P", "pj")
        la = self.fresh("ntta")
        a.label(la)
        self.load(st, "pj", [1024 * i for i in range(8)])
        zi = (lambda m: m) if self.biased else zm
        for i in range(4):
            self.ct(st, f"x{i}", f"x{i + 4}", zi(1))
        for i, z in ((0, 2), (1, 2), (4, 3), (5, 3)):
            self.ct(st, f"x{i}", f"x{i + 2}", zi(z))
        for i, z in ((0, 4), (2, 5), (4, 6), (6, 7)):
            self.ct(st, f"x{i}", f"x{i + 1}", zi(z))
        self.store(st, "pj", [1024 * i for i in range(8)])
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M"] + C + ["end", "pj"])
        st.dup("pj", "x")
        st.dup("end", "e")
        st.op("GT", 2, "f")
        a.jumpi(la)
        st.s.pop()
        st.pop("pj")
        st.pop("end")
        # pass B: layers 4-6; block b (32 words), j < 4: words 32b + j + 4i
        st.push(self.TB, "zb")
        st.dup("P", "pj")               # pj = P + 1024 b + 32 j
        lb, lbn = self.fresh("nttb"), self.fresh("nttbn")
        a.label(lb)
        self.load(st, "pj", [128 * i for i in range(8)])
        for i in range(4):
            self.ct(st, f"x{i}", f"x{i + 4}", ("zb", 0))
        for i, z in ((0, 1), (1, 1), (4, 2), (5, 2)):
            self.ct(st, f"x{i}", f"x{i + 2}", ("zb", 32 * z))
        for i, z in ((0, 3), (2, 4), (4, 5), (6, 6)):
            self.ct(st, f"x{i}", f"x{i + 1}", ("zb", 32 * z))
        self.store(st, "pj", [128 * i for i in range(8)])
        # j += 1; after j == 3: next block (pj += 1024 - 128, zb += 224)
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M"] + C + ["zb", "pj"])
        st.dup("pj", "x")
        st.push(127, "c")
        st.op("AND", 2, "x")            # (pj - P) mod 128 == 0 iff j wrapped (P is 0x2000-aligned mod 128)
        a.jumpi(lb)
        st.s.pop()
        st.add_const("pj", 1024 - 128)
        st.add_const("zb", 7 * 32)
        st.dup("zb", "x")
        st.push(self.TB + 8 * 7 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(lb)
        st.s.pop()
        st.pop("pj")
        st.pop("zb")
        # pass C: layers 7-8; block b of 4 words
        st.push(self.TC, "zc")
        st.dup("P", "pj")
        lc = self.fresh("nttc")
        a.label(lc)
        self.load(st, "pj", [0, 32, 64, 96])
        self.ct(st, "x0", "x2", ("zc", 0))
        self.ct(st, "x1", "x3", ("zc", 0))
        self.ct(st, "x0", "x1", ("zc", 32))
        self.ct(st, "x2", "x3", ("zc", 64))
        self.store(st, "pj", [0, 32, 64, 96])
        st.add_const("pj", 128)
        st.add_const("zc", 96)
        st.expect(["ret", "P", "M"] + C + ["zc", "pj"])
        st.dup("zc", "x")
        st.push(self.TC + 64 * 96, "e")
        st.op("GT", 2, "f")
        a.jumpi(lc)
        st.s.pop()
        st.pop("pj")
        st.pop("zc")
        if not self.biased:
            st.pop("C")
        st.pop("M")
        st.pop("P")
        a.op("JUMP")

    # ── inverse ─────────────────────────────────────────────────────────
    @staticmethod
    def cgs(L):
        """Subtraction constant for inverse layer L (1..8): >= 2^(26+L) and = 0 mod q."""
        return Q * -(-(1 << (26 + L)) // Q)

    premont = False

    def gen_intt(self, name, factor):
        a = self.a
        a.region(name)
        a.label(name)
        F = 8347681 * factor % Q         # 256^-1 * factor
        st = Stack(a, ["ret", "P"])
        st.push(M32X4, "M")
        st.push(LANES(self.cgs(8)), "C")
        # pass C': layers len 1, 2 on 4-word blocks, records backwards
        st.push(self.TC + 63 * 96, "zc")
        st.dup("P", "pj")
        lc = self.fresh("intc")
        a.label(lc)
        self.load(st, "pj", [0, 32, 64, 96], mont=self.premont)
        self.gs(st, "x0", "x1", ("zc", 64))
        self.gs(st, "x2", "x3", ("zc", 32))
        self.gs(st, "x0", "x2", ("zc", 0))
        self.gs(st, "x1", "x3", ("zc", 0))
        self.store(st, "pj", [0, 32, 64, 96])
        st.add_const("pj", 128)
        st.to_top("zc")
        st.push(96, "c")
        st.swap(1)
        st.op("SUB", 2, "zc")
        st.swap(1)
        st.expect(["ret", "P", "M", "C", "zc", "pj"])
        st.dup("zc", "x")
        st.push(self.TC, "e")
        st.op("GT", 2, "f")             # TC > zc: done (zc wrapped below TC)
        st.op("ISZERO", 1, "f")
        a.jumpi(lc)
        st.s.pop()
        st.pop("pj")
        st.pop("zc")
        # pass B': layers len 4, 8, 16; block b, j < 4: words 32b + j + 4i
        st.push(self.TB + 7 * 7 * 32, "zb")
        st.dup("P", "pj")
        lb = self.fresh("intb")
        a.label(lb)
        self.load(st, "pj", [128 * i for i in range(8)])
        for i, z in ((0, 6), (2, 5), (4, 4), (6, 3)):
            self.gs(st, f"x{i}", f"x{i + 1}", ("zb", 32 * z))
        for i, z in ((0, 2), (1, 2), (4, 1), (5, 1)):
            self.gs(st, f"x{i}", f"x{i + 2}", ("zb", 32 * z))
        for i in range(4):
            self.gs(st, f"x{i}", f"x{i + 4}", ("zb", 0))
        self.store(st, "pj", [128 * i for i in range(8)])
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M", "C", "zb", "pj"])
        st.dup("pj", "x")
        st.push(127, "c")
        st.op("AND", 2, "x")
        a.jumpi(lb)
        st.s.pop()
        st.add_const("pj", 1024 - 128)
        st.to_top("zb")
        st.push(7 * 32, "c")
        st.swap(1)
        st.op("SUB", 2, "zb")
        st.swap(1)
        st.expect(["ret", "P", "M", "C", "zb", "pj"])
        st.dup("zb", "x")
        st.push(self.TB, "e")
        st.op("GT", 2, "f")
        st.op("ISZERO", 1, "f")
        a.jumpi(lb)
        st.s.pop()
        st.pop("pj")
        st.pop("zb")
        # pass A': layers len 32, 64, 128 (+ scaling), words j + 32 i
        st.dup("P", "end")
        st.push(32 * 32, "c")
        st.op("ADD", 2, "end")
        st.dup("P", "pj")
        la = self.fresh("inta")
        a.label(la)
        self.load(st, "pj", [1024 * i for i in range(8)])
        for i, z in ((0, 7), (2, 6), (4, 5), (6, 4)):
            self.gs(st, f"x{i}", f"x{i + 1}", zm(z))
        for i, z in ((0, 3), (1, 3), (4, 2), (5, 2)):
            self.gs(st, f"x{i}", f"x{i + 2}", zm(z))
        for i in range(4):
            self.gs(st, f"x{i}", f"x{i + 4}", zm(1, F), self.cgs(8), ascale=F * R32 % Q)
        self.store(st, "pj", [1024 * i for i in range(8)], self.post)
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M", "C", "end", "pj"])
        st.dup("pj", "x")
        st.dup("end", "e")
        st.op("GT", 2, "f")
        a.jumpi(la)
        st.s.pop()
        st.pop("pj")
        st.pop("end")
        st.pop("C")
        st.pop("M")
        st.pop("P")
        a.op("JUMP")

    _n = 0

    def fresh(self, base):
        Kernel._n += 1
        return f"{base}_{Kernel._n}"
