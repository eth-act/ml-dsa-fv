#!/usr/bin/env python3
"""Glamsterdam variant of the optimised verifiers: MlDsaOpt/NN/glam/.

Usage: python3 scripts/gen_glam.py [--base v4|v3] [--out DIR] [44|65|87 ...]

The v4 design (scripts/gen_opt.py --version v4, unchanged and byte-identical;
`--base v3` builds the v3-based prototype of branch gas/glamsterdam) with the two
Keccak kernels replaced by the stack-resident, fully unrolled kernels of
scripts/opt_keccak_glam.py. They need two Glamsterdam EIPs:

* EIP-8024 (DUPN / SWAPN): the 25 lanes stay on the stack across rounds;
* EIP-7954 (64 KiB code limit): the unrolled kernels add ~25 KB of code.

With base v4 two further Glamsterdam-only changes apply (base v3 keeps the
v3 blk and NTT: the gas/glamsterdam prototype with the current kernels):

* blk / blkh / blkt fully unrolled with immediate lane addresses, the lane
  complementing undone on the loaded word instead of in KS (+5.3 KB);
* NTT and inverse NTT merged 4 + 4 with 16 words on the stack
  (scripts/opt_ntt_glam.py, new table layout in TBL, +3.3 KB).

The iota tables RC4 / RC1 are no longer read, so they are not initialised
(their memory stays allocated, so every other address and the memory size
are the same as the base version). Run the bytecode with opt_evm.run(..., fork="glamsterdam").
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_opt  # noqa: E402
from opt_asm import Stack  # noqa: E402
from opt_keccak_glam import gen_keccak_stack  # noqa: E402
from opt_ntt_glam import Kernel4x4  # noqa: E402
from opt_ref import Q  # noqa: E402

FORK = "glamsterdam"
CODE_LIMIT = 0x10000          # EIP-7954


def _kernel(a, name, st_addr, bt_addr, rct, unroll=2, scale=4, kz_addr=None):
    gen_keccak_stack(a, name, st_addr, scale)


class GlamGen(gen_opt.Gen):
    def __init__(self, L):
        super().__init__(L)
        if self.v4:
            # NTT / inverse NTT merged 4 + 4 (16 words on the stack)
            k = Kernel4x4(self.a, L.TBL)
            k.biased = self.nttk.biased
            self.nttk = k

    UH_FUSE = {44: True, 65: True, 87: True}
    CSUM_DEEP = True
    DZ_UNROLL = True

    def gen_ntts(self):
        if self.uh_fused():
            self.nttk.post_consts = self.uh_consts()
        super().gen_ntts()

    def init_tables(self):
        pass                  # iota is a PUSH immediate in the unrolled kernels

    def gen_blk(self):
        """v4's blk / blkh / blkt with the same entries and outputs, fully
        unrolled (EIP-7954 code size): lanes are read with PUSH addr MLOAD and
        un-complemented by a NOT on the loaded word (v4 flips the six
        complemented rate lanes in KS before and after, 12 loads + 12
        stores), and there are no pointer increments or loop tests.
        Entries: blk / blkh [ret, abp, flp] (lanes 0..20 / 0..11), blkt [ret]
        (lanes 12..20 of the last block, as in v4)."""
        if not self.v4:
            return super().gen_blk()
        a, L = self.a, self.L
        assert L.KS == 0
        a.region("blk")
        rate_c = {x for x in gen_opt.COMPLEMENTED if x < 21}
        common, it4, done = self.fresh("blkc"), self.fresh("blk4"), self.fresh("blkx")
        a.label("blk")
        a.op("PUSH0")                       # h = 0: all 7 iterations
        a.jump(common)
        a.label("blkh")
        a.push(1)                           # h = 1: iterations 0..3
        a.label(common)
        st = Stack(a, ["ret", "abp", "flp", "h"])
        masks, mvals = [], []
        for n, (i, j) in enumerate(self.UNZIP):
            m = sum(1 << p for p in range(256) if (p >> i) & 1 and not (p >> j) & 1)
            st.push(m, f"U{n}")
            masks.append(((1 << j) - (1 << i), f"U{n}"))
            mvals.append(m)
        layout = list(st.s)
        C = sum(((1 << 23) - Q) << (64 * sl) for sl in range(4))
        for it in range(7):
            if it == 4:
                st.dup("h", "f")
                a.jumpi(done)
                st.s.pop()
                a.label(it4)
                assert st.s == layout
            for w in range(3):
                lane = 3 * it + w
                st.push(L.KS + 32 * lane, f"W{w}")
                st.op("MLOAD", 1, f"W{w}")
                if lane in rate_c:
                    st.op("NOT", 1, f"W{w}")
                for d, mn in masks:
                    x = f"W{w}"
                    st.dup(x, "t")
                    st.push(d, "c")
                    st.op("SHR", 2, "t")
                    st.dup(x, "x2")
                    st.op("XOR", 2, "t")
                    st.dup(mn, "m")
                    st.op("AND", 2, "t")
                    st.dup("t", "t2")
                    st.push(d, "c")
                    st.op("SHL", 2, "t2")
                    st.op("XOR", 2, "t")
                    st.op("XOR", 2, x)
            st.push(0, "lf")
            for k in range(8):
                o = 3 * k
                w, b = o >> 3, o & 7
                if b <= 5:
                    st.dup(f"W{w}", "A")
                    if b:
                        st.push(8 * b, "s")
                        st.op("SHR", 2, "A")
                    st.push(gen_opt.lanemask(23), "m")
                    st.op("AND", 2, "A")
                else:
                    lo = 64 - 8 * b
                    st.dup(f"W{w}", "A")
                    st.push(8 * b, "s")
                    st.op("SHR", 2, "A")
                    st.push(gen_opt.lanemask(lo), "m")
                    st.op("AND", 2, "A")
                    st.dup(f"W{w + 1}", "B")
                    st.push(gen_opt.lanemask(23 - lo), "m")
                    st.op("AND", 2, "B")
                    st.push(lo, "s")
                    st.op("SHL", 2, "B")
                    st.op("OR", 2, "A")
                st.dup("A", "A2")
                st.dup("abp", "p")
                if 256 * it + 32 * k:
                    st.push(256 * it + 32 * k, "c")
                    st.op("ADD", 2, "p")
                st.op("MSTORE", 2)
                st.push(C, "c")
                st.op("ADD", 2, "A")
                st.op("OR", 2, "lf")
            st.dup("flp", "p")
            if it:
                st.push(32 * it, "c")
                st.op("ADD", 2, "p")
            st.op("MSTORE", 2)
            for w in (2, 1, 0):
                st.pop(f"W{w}")
        a.label(done)
        assert st.s == layout
        for n in reversed(range(len(masks))):
            st.pop(f"U{n}")
        for nm in ("h", "flp", "abp"):
            st.pop(nm)
        a.op("JUMP")
        # blkt [ret]: iterations 4..6 of the last block (v4: abp = ABUF + 256*32,
        # flp = FL + 32*32 at iteration 4)
        a.label("blkt")
        a.push(L.ABUF + 256 * 32 - 4 * 256)
        a.push(L.FL + 32 * 32 - 4 * 32)
        a.op("PUSH0")
        for m in mvals:
            a.push(m)
        a.jump(it4)

    def build(self, stop_after=None):
        orig = gen_opt.gen_keccak_f
        gen_opt.gen_keccak_f = _kernel
        try:
            return super().build(stop_after)
        finally:
            gen_opt.gen_keccak_f = orig


BASE = "v4"


def build(nn, base=BASE, **dbg):
    g = GlamGen(gen_opt.Layout(nn, base, glam=True))
    for k, v in dbg.items():
        setattr(g, k, v)
    return g, g.build()


def main(argv):
    base, out, sets = BASE, None, []
    it = iter(argv)
    for x in it:
        if x == "--base":
            base = next(it)
        elif x == "--out":
            out = next(it)
        else:
            sets.append(int(x))
    sets = sets or [44, 65, 87]
    assert base == BASE or out is not None, "MlDsaOpt/NN/glam/ holds the v4-based build; use --out"
    root = os.path.join(HERE, "..", "MlDsaOpt")
    for nn in sets:
        g, code = build(nn, base)
        assert len(code) <= CODE_LIMIT, f"{nn}: {len(code)} bytes exceeds EIP-7954"
        d = os.path.join(out, str(nn)) if out else os.path.join(root, str(nn), "glam")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "opt.hex"), "w") as f:
            f.write(code.hex() + "\n")
        with open(os.path.join(d, "opt.asm"), "w") as f:
            f.write(f"; GENERATED by scripts/gen_glam.py --base {base} {nn} (Glamsterdam: EIP-8024, EIP-7954); do not edit.\n")
            f.write(g.a.listing())
        with open(os.path.join(d, "layout.txt"), "w") as f:
            f.write(gen_opt.layout_text(g, code).replace("(limit 24576)", f"(limit {CODE_LIMIT}, EIP-7954)", 1))
        print(nn, "glam", base, len(code), "bytes", d)


if __name__ == "__main__":
    main(sys.argv[1:])
