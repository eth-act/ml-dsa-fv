"""4 + 4 merged NTT / inverse NTT for the Glamsterdam variant (EIP-8024).

Same arithmetic, butterflies (`opt_ntt.Kernel.ct` / `gs`), bias and bounds as
v4's kernel, but the eight layers are merged 4 + 4 instead of 3 + 3 + 2: each
pass holds 16 words on the stack (reached with DUPN / SWAPN), so the
polynomial array is read and written twice instead of three times.

Forward: pass A, layers 1-4 (len 128..16) on words j + 16 i (i < 16), Shoup
multiplication by immediate zetas (layer 4 too: zetas 8..15); pass B, layers
5-8 (len 8..1) on blocks of 16 consecutive words, Montgomery with the block's
15 zetas loaded once from the table onto the stack.
Inverse: pass 1, len 1..8 on blocks of 16 words (table records walked
backwards, Montgomery-reducing the accumulator at load as in v4); pass 2,
len 16..128 on words j + 16 i with immediate zetas and the 256^-1 * factor
scaling folded into the last layer.

Bounds. Forward: v4's argument holds per layer, and the Shoup bound
u < q (1 + b / 2^32) + 1 used for layer 4 is below the Montgomery bound v4
uses there; checked in opt_selftest_glam.py. Inverse: identical per-layer
operations and constants (C = cgs(8)), only the pass boundaries move.

Table (at TB): block b (b < 16) has 15 Montgomery zetas, index
(8 / L - 1) + g for len L in (8, 4, 2, 1) and group g < 8 / L:
zm(128 / L + b * 8 / L + g).
"""
from __future__ import annotations

from opt_asm import Stack
from opt_ntt import LANES, M32X4, R32, Kernel, zm
from opt_ref import Q

LENS_LO = (8, 4, 2, 1)


def rec(L, g):
    return 8 // L - 1 + g


class Kernel4x4(Kernel):
    def records(self):
        out = []
        for b in range(16):
            for L in LENS_LO:
                out += [zm(128 // L + b * 8 // L + g) for g in range(8 // L)]
        return out

    def zeta(self, st, z):
        if isinstance(z, str):
            st.dup(z, "z")
        else:
            super().zeta(st, z)

    def load_zetas(self, st, ptr, order):
        for r in order:
            st.dup(ptr, f"Z{r}")
            if r:
                st.push(32 * r, "c")
                st.op("ADD", 2, f"Z{r}")
            st.op("MLOAD", 1, f"Z{r}")

    def flush(self, st, ptr, offs):
        """Store the words x_i and drop the zetas Z_r in stack order (the
        butterflies' swaps interleave them)."""
        while st.top()[0] in "xZ":
            nm = st.top()
            if nm[0] == "Z":
                st.pop()
            else:
                st.dup(ptr, "p")
                o = offs[int(nm[1:])]
                if o:
                    st.push(o, "c")
                    st.op("ADD", 2, "p")
                st.op("MSTORE", 2)

    def gen_ntt(self, name):
        assert self.biased
        a = self.a
        a.region(name)
        a.label(name)
        st = Stack(a, ["ret", "P"], deep=True)
        st.push(M32X4, "M")
        # pass A: layers 1-4, words j + 16 i
        st.dup("P", "end")
        st.push(16 * 32, "c")
        st.op("ADD", 2, "end")
        st.dup("P", "pj")
        la = self.fresh("ntta")
        a.label(la)
        offs = [512 * i for i in range(16)]
        self.load(st, "pj", offs)
        for L in (128, 64, 32, 16):
            h = L // 16
            for G in range(128 // L):
                for t in range(h):
                    i = 2 * h * G + t
                    self.ct(st, f"x{i}", f"x{i + h}", 128 // L + G)   # Shoup, zeta index
        self.store(st, "pj", offs)
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M", "end", "pj"])
        st.dup("pj", "x")
        st.dup("end", "e")
        st.op("GT", 2, "f")
        a.jumpi(la)
        st.s.pop()
        st.pop("pj")
        st.pop("end")
        # pass B: layers 5-8 on blocks of 16 consecutive words
        st.push(self.TB, "zb")
        st.dup("P", "pj")
        lb = self.fresh("nttb")
        a.label(lb)
        offs = [32 * i for i in range(16)]
        self.load(st, "pj", offs)
        self.load_zetas(st, "zb", range(15))
        for L in LENS_LO:
            for g in range(16 // (2 * L)):
                for t in range(L):
                    i = 2 * L * g + t
                    self.ct(st, f"x{i}", f"x{i + L}", f"Z{rec(L, g)}")
        self.flush(st, "pj", offs)
        st.add_const("pj", 512)
        st.add_const("zb", 15 * 32)
        st.expect(["ret", "P", "M", "zb", "pj"])
        st.dup("zb", "x")
        st.push(self.TB + 16 * 15 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(lb)
        st.s.pop()
        st.pop("pj")
        st.pop("zb")
        st.pop("M")
        st.pop("P")
        a.op("JUMP")

    def gen_intt(self, name, factor):
        a = self.a
        a.region(name)
        a.label(name)
        F = 8347681 * factor % Q         # 256^-1 * factor
        st = Stack(a, ["ret", "P"], deep=True)
        st.push(M32X4, "M")
        st.push(LANES(self.cgs(8)), "C")
        # pass 1: len 1, 2, 4, 8 on blocks of 16 words; block b uses the
        # forward record of block 15 - b with groups reversed
        st.push(self.TB + 15 * 15 * 32, "zb")
        st.dup("P", "pj")
        l1 = self.fresh("int1")
        a.label(l1)
        offs = [32 * i for i in range(16)]
        self.load(st, "pj", offs, mont=self.premont)
        self.load_zetas(st, "zb", range(15))
        for L in reversed(LENS_LO):
            ng = 16 // (2 * L)
            for g in range(ng):
                for t in range(L):
                    i = 2 * L * g + t
                    self.gs(st, f"x{i}", f"x{i + L}", f"Z{rec(L, ng - 1 - g)}")
        self.flush(st, "pj", offs)
        st.add_const("pj", 512)
        st.to_top("zb")
        st.push(15 * 32, "c")
        st.swap(1)
        st.op("SUB", 2, "zb")
        st.swap(1)
        st.expect(["ret", "P", "M", "C", "zb", "pj"])
        st.dup("zb", "x")
        st.push(self.TB, "e")
        st.op("GT", 2, "f")             # TB > zb: done
        st.op("ISZERO", 1, "f")
        a.jumpi(l1)
        st.s.pop()
        st.pop("pj")
        st.pop("zb")
        # pass 2: len 16, 32, 64, 128 on words j + 16 i (+ scaling)
        st.dup("P", "end")
        st.push(16 * 32, "c")
        st.op("ADD", 2, "end")
        st.dup("P", "pj")
        l2 = self.fresh("int2")
        a.label(l2)
        offs = [512 * i for i in range(16)]
        self.load(st, "pj", offs)
        for L in (16, 32, 64, 128):
            h = L // 16
            for G in range(128 // L):
                m = 256 // L - 1 - G
                for t in range(h):
                    i = 2 * h * G + t
                    if L == 128:
                        self.gs(st, f"x{i}", f"x{i + h}", zm(1, F), ascale=F * R32 % Q)
                    else:
                        self.gs(st, f"x{i}", f"x{i + h}", zm(m))
        self.store(st, "pj", offs)
        st.add_const("pj", 32)
        st.expect(["ret", "P", "M", "C", "end", "pj"])
        st.dup("pj", "x")
        st.dup("end", "e")
        st.op("GT", 2, "f")
        a.jumpi(l2)
        st.s.pop()
        st.pop("pj")
        st.pop("end")
        st.pop("C")
        st.pop("M")
        st.pop("P")
        a.op("JUMP")
