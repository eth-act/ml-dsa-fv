#!/usr/bin/env python3
"""Generate the gas-optimised ML-DSA verifiers MlDsaOpt/{44,65,87}/opt.hex.

Usage: python3 scripts/gen_opt.py [44|65|87 ...]   (default: all three)

Writes MlDsaOpt/NN/opt.hex (runtime bytecode), MlDsaOpt/NN/opt.asm (the
readable intermediate form: annotated listing) and MlDsaOpt/NN/layout.txt
(subroutine entry points and memory map).

Design summary (details in docs/opt.md):
* Keccak-f[1600] in two representations generated from one round template
  (scripts/opt_keccak.py): `kf1`, one state with every lane replicated four
  times per word (single sponges: tr, mu, SampleInBall, final c-tilde hash),
  and `kf4`, four bit-interleaved states per word (ExpandA, four SHAKE128
  instances per permutation).
* Polynomial arithmetic on 4 x 64-bit lanes per word, the lanes holding four
  different polynomials at the same coefficient index, so every NTT butterfly
  is one word operation with a scalar zeta (scripts/opt_ntt.py).
* ExpandA fused with A*z: a kf4 group samples column j for four rows at once;
  coefficient t of the four rows is one packed word, multiplied by the scalar
  z_hat_j[t] and accumulated into the row-packed accumulator.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from opt_asm import Asm, Stack  # noqa: E402
from opt_keccak import gen_keccak_f, rc_table, REP, COMPLEMENTED  # noqa: E402
from opt_ref import Q, derived, interleave, spread  # noqa: E402
from opt_ntt import Kernel as NttKernel  # noqa: E402

M64 = (1 << 64) - 1
ALL = (1 << 256) - 1


def lanemask(bits):
    """Low `bits` bits of each 64-bit lane."""
    m = (1 << bits) - 1
    return m | m << 64 | m << 128 | m << 192


def bytepattern(pat, n):
    v = 0
    for i in range(32 // n):
        v = v << (8 * n) | pat
    return v


M8 = bytepattern(0x00FF, 2)
M16 = bytepattern(0x0000FFFF, 4)
M32 = bytepattern(0x00000000FFFFFFFF, 8)


VERSIONS = ("v2", "v3", "v4")
DEFAULT_VERSION = "v3"


class Layout:
    def __init__(self, nn, version=DEFAULT_VERSION):
        assert version in VERSIONS, version
        p = derived(nn)
        self.nn = nn
        self.version = version
        self.v3 = version in ("v3", "v4")    # v4 extends v3
        self.v4 = version == "v4"
        self.p = p
        self.k, self.l = p["k"], p["l"]
        self.PK, self.SIG = p["pklen"], p["siglen"]
        self.HDR = self.PK + self.SIG
        self.CT = self.PK                       # c-tilde offset in calldata
        self.Z0 = self.PK + p["ctb"]           # z offset
        self.H0 = self.Z0 + self.l * p["zbytes"]  # hint offset
        self.GR = (self.k + 3) // 4            # row groups
        self.GZ = (self.l + 3) // 4            # z groups
        addr = 0
        regions = []

        def alloc(name, size):
            nonlocal addr
            addr = (addr + 0xFF) & ~0xFF       # 256-byte alignment (NTT pass B relies on 128)
            regions.append((name, addr, size))
            setattr(self, name, addr)
            addr += size

        alloc("KS", 0x320)        # Keccak state (25 words)
        alloc("KB", 0x320)        # Keccak second buffer
        alloc("RC4", 0x300)       # iota constants, interleaved
        alloc("RC1", 0x300)       # iota constants, replicated
        alloc("MISC", 0x200)      # small words (rho interleaved, flags)
        alloc("TBL", 0x2000)      # NTT tables
        alloc("CW", 0x2000)       # c coefficient codes (+1: c = -1, -1: c = +1)
        alloc("ABUF", 336 * 32)   # positional candidates, row-packed
        alloc("FL", 42 * 32)      # per-8-candidate rejection flag words
        alloc("ZH", self.GZ * 0x2000)
        alloc("BASES", 64 * 32)        # window base offset per nonzero c coefficient
        alloc("IDX", 0x100)            # byte per position: slot + 1 in BASES (0 = zero coeff)
        # overlay: after ExpandA, ABUF/FL/ZH are dead and host the c*t1 tables
        if os.environ.get("OPT_DBG_NO_OVERLAY"):
            alloc("TT", self.GR * 0x1800)
            alloc("SP", self.GR * 0x2000)
        else:
            self.TT = self.ABUF                  # c*t1 window tables (GR x 6 KB)
            self.SP = self.TT + self.GR * 0x1800  # 2^13 S'(t) + n_neg(t), row-packed (GR x 8 KB)
            assert self.ABUF < self.FL < self.ZH and self.SP + self.GR * 0x2000 <= self.ZH + self.GZ * 0x2000
        assert self.CW + 0x2000 <= self.ABUF
        alloc("ACC", self.GR * 0x2000)
        alloc("HP", self.GR * 0x2000)  # hint bits, row-packed per coefficient (lane = row)
        self.w1lanes = 4 * p["w1bits"] * self.k  # 64-bit lanes of w1Encode
        alloc("FIN", 32 * (8 + self.w1lanes))  # mu || w1Encode, one lane per word (replicated)
        alloc("RHO1", 12 * 32)    # spread(rho lane i), spread(c-tilde lane i)
        alloc("CB", 34 * 32)      # SampleInBall stream: two 136-byte blocks as 64-bit lanes
        alloc("TRL", 8 * 32)      # tr lanes (from a SIMD slot)
        alloc("MU", 8 * 32)       # mu lanes (short messages: from a SIMD slot)
        alloc("BK", 25 * 32)      # kf4 state backup (6th RejNTTPoly block)
        if self.v3:
            alloc("KZ", 25 * 32)  # kf1 third round buffer (v3: 3 rounds per iteration)
        self.TOP = addr
        self.regions = regions


class Gen:
    def __init__(self, L: Layout):
        self.L = L
        self.v3 = L.v3
        self.v4 = L.v4
        self.a = Asm()
        self.n = 0
        self.nttk = NttKernel(self.a, L.TBL)

    def fresh(self, base):
        self.n += 1
        return f"{base}_{self.n}"

    def call(self, fn, args=()):
        """Call subroutine fn with constant args (pushed in order, last on top)."""
        a = self.a
        ret = self.fresh("ret")
        a.pushl(ret)
        for v in args:
            a.push(v)
        a.jump(fn)
        a.label(ret)

    # ── absorption helpers ──────────────────────────────────────────────
    CONSTS = ("M8", "M16", "M32", "M64", "REP")

    def push_consts(self, st):
        for name, v in zip(self.CONSTS, (M8, M16, M32, M64, REP)):
            st.push(v, name)

    def pop_consts(self, st):
        for name in reversed(self.CONSTS):
            st.pop(name)

    def bswap64x4(self, st, x):
        """Reverse the bytes inside each 64-bit lane of value x (on top)."""
        a = self.a
        for s, m in ((8, "M8"), (16, "M16"), (32, "M32")):
            st.dup(x, "y")
            st.push(s, "s")
            st.op("SHR", 2, "y")
            st.dup(m, "m")
            st.op("AND", 2, "y")
            st.swap(1)
            st.dup(m, "m")
            st.op("AND", 2, "x")
            st.push(s, "s")
            st.op("SHL", 2, "x")
            st.op("OR", 2, x)

    def absorb_cd_seq(self, st, first_lane, nlanes, off=None, const_off=0, mask_first=None):
        """KS[first_lane + i] ^= REP * LE64(calldata[base + 8i ..]), i < nlanes.

        base = off (stack value name) + const_off, or const_off if off is None.
        Needs CONSTS on the stack. mask_first: AND mask for the first lane value.
        """
        a = self.a
        i = 0
        while i < nlanes:
            n = min(4, nlanes - i)
            if off is not None:
                st.dup(off, "w")
                if const_off + 8 * i:
                    st.push(const_off + 8 * i, "c")
                    st.op("ADD", 2, "w")
            else:
                st.push(const_off + 8 * i, "w")
            st.op("CALLDATALOAD", 1, "w")
            self.bswap64x4(st, "w")
            for j in range(n):
                last = j == n - 1
                if not last:
                    st.dup("w", "v")
                if 192 - 64 * j:
                    st.push(192 - 64 * j, "s")
                    st.op("SHR", 2, "v")
                else:
                    st.rename(st.top(), "v")
                if j or (i == 0 and mask_first is not None):
                    if i == 0 and j == 0:
                        st.push(mask_first, "m")
                    else:
                        st.dup("M64", "m")
                    st.op("AND", 2, "v")
                st.dup("REP", "r")
                st.op("MUL", 2, "v")
                addr = self.L.KS + 32 * (first_lane + i + j)
                st.push(addr, "p")
                st.op("MLOAD", 1, "k")
                st.op("XOR", 2, "v")
                st.push(addr, "p")
                st.op("MSTORE", 2)
            i += n

    def gen_absorb17(self):
        """Subroutine absorb17: entry [ret, off]; KS[0..16] ^= calldata lanes at off."""
        a = self.a
        a.region("absorb17")
        a.label("absorb17")
        st = Stack(a, ["ret", "off"])
        self.push_consts(st)
        self.absorb_cd_seq(st, 0, 17, off="off")
        self.pop_consts(st)
        st.pop("off")
        a.op("JUMP")

    def absorb_inline(self, first_lane, nlanes, const_off, mask_first=None):
        st = Stack(self.a, [])
        self.push_consts(st)
        self.absorb_cd_seq(st, first_lane, nlanes, None, const_off, mask_first)
        self.pop_consts(st)

    def call_absorb17_top(self):
        """absorb17 with the offset on top of the stack (kept)."""
        a = self.a
        ret = self.fresh("ret")
        a.pushl(ret)
        a.op("DUP2")
        a.jump("absorb17")
        a.label(ret)

    def zero_ks(self, start=0):
        """Fresh sponge state for lanes start..24 (complemented lanes = all-ones)."""
        a = self.a
        for i in range(start, 25):
            a.op("PUSH0")
            if i in COMPLEMENTED:
                a.op("NOT")
            a.push(self.L.KS + 32 * i)
            a.op("MSTORE")

    def flip_ks(self, lanes):
        """Invert the given KS lanes in place (complemented <-> plain)."""
        a = self.a
        for i in lanes:
            a.push(self.L.KS + 32 * i)
            a.op("MLOAD")
            a.op("NOT")
            a.push(self.L.KS + 32 * i)
            a.op("MSTORE")

    def xor_ks_const(self, lane, value):
        a = self.a
        addr = self.L.KS + 32 * lane
        a.push(value)
        a.push(addr)
        a.op("MLOAD")
        a.op("XOR")
        a.push(addr)
        a.op("MSTORE")

    # ── program pieces ──────────────────────────────────────────────────
    def init_tables(self):
        a, L = self.a, self.L
        for i, v in enumerate(rc_table(4)):
            a.push(v)
            a.push(L.RC4 + 32 * i)
            a.op("MSTORE")
        a.push(REP)
        for i, v in enumerate(rc_table(1)):
            a.push(v // REP)
            a.op("DUP2")
            a.op("MUL")
            a.push(L.RC1 + 32 * i)
            a.op("MSTORE")
        a.op("POP")

    def hash_mu(self):
        """mu = H(tr || 0 || 0 || M, 64) with tr in KS[0..7]; mu -> FIN[0..7]."""
        a, L = self.a, self.L
        a.region("hash_mu")
        self.zero_ks(8)
        # block 0: lanes 8..16 = stream bytes 64..135 = 0,0,M[0..69]
        self.absorb_inline(8, 9, L.HDR - 2, mask_first=M64 ^ 0xFFFF)
        # nb = (66 + mlen) // 136 + 1 blocks; stack [mlen]
        a.push(L.HDR)
        a.op("CALLDATASIZE")
        a.op("SUB")                      # mlen
        a.push(66)
        a.op("ADD")                      # P = 66 + mlen (padding position)
        # loop: while P >= 136: kf1; absorb next block; P -= 136
        loop, done = self.fresh("muloop"), self.fresh("mudone")
        # stack [P, off] where off = calldata offset of the next block
        a.push(L.HDR - 66 + 136)
        a.op("SWAP1")                    # [off, P]
        a.label(loop)
        a.push(136)
        a.op("DUP2")
        a.op("LT")                       # P < 136
        a.jumpi(done)
        self.call("kf1")
        a.op("SWAP1")                    # [P, off]
        self.call_absorb17_top()
        a.push(136)
        a.op("ADD")
        a.op("SWAP1")                    # [off', P]
        a.push(136)
        a.op("SWAP1")
        a.op("SUB")                      # P - 136
        a.jump(loop)
        a.label(done)
        # pad: KS[P >> 3] ^= (0x1F << 8 (P & 7)) * REP
        a.op("DUP1")
        a.push(7)
        a.op("AND")
        a.push(3)
        a.op("SHL")
        a.push(0x1F * REP)
        a.op("SWAP1")
        a.op("SHL")                      # [off, P, pad] (bottom..top)
        a.op("SWAP2")
        a.op("POP")                      # [pad, P]
        a.push(3)
        a.op("SHR")
        a.push(5)
        a.op("SHL")
        a.push(L.KS)
        a.op("ADD")                      # [pad, addr]
        a.op("DUP1")
        a.op("MLOAD")                    # [pad, addr, v]
        a.op("SWAP1")
        a.op("SWAP2")                    # [addr, v, pad]
        a.op("XOR")
        a.op("SWAP1")
        a.op("MSTORE")
        self.xor_ks_const(16, (0x80 << 56) * REP)
        self.call("kf1")
        for i in range(8):
            a.push(L.KS + 32 * i)
            a.op("MLOAD")
            if i in COMPLEMENTED:
                a.op("NOT")
            a.push(L.FIN + 32 * i)
            a.op("MSTORE")

    # ── decoding ────────────────────────────────────────────────────────
    def bswap256(self, st, x):
        """Full 32-byte reversal of value x (on top). Needs M8, M16, M32, M64X."""
        for s, m in ((8, "M8"), (16, "M16"), (32, "M32"), (64, "M64X")):
            st.dup(x, "y")
            st.push(s, "s")
            st.op("SHR", 2, "y")
            st.dup(m, "m")
            st.op("AND", 2, "y")
            st.swap(1)
            st.dup(m, "m")
            st.op("AND", 2, "x")
            st.push(s, "s")
            st.op("SHL", 2, "x")
            st.op("OR", 2, x)
        st.dup(x, "y")
        st.push(128, "s")
        st.op("SHR", 2, "y")
        st.swap(1)
        st.push(128, "s")
        st.op("SHL", 2, "x")
        st.op("OR", 2, x)

    def gen_decode(self, name, stride, bits, post, flags=False):
        """Subroutine `name`: decode four little-endian `bits`-bit packed
        polynomials at calldata offsets off + stride*j (j = lane) into 256
        lane-packed words at dp (lane j = polynomial j). post(st, store)
        transforms the raw packed word on top and stores it.
        Entry [ret, off, dp]; exit [] (or [flagword] if flags: OR of the
        per-coefficient flag words produced by post).
        """
        a = self.a
        a.region(name)
        a.label(name)
        G = 64 // bits                 # coefficients per lane in one gather
        C = (256 // bits) // G * G      # coefficients per 32-byte load
        while C * bits > 256 or (C * bits) % 8:
            C -= G
        CB = C * bits // 8
        used = [0, 1, 2, 3]
        offs = [stride * j for j in range(4)]
        o0 = 0
        st = Stack(a, ["ret", "off", "dp"])
        if flags:
            st.push(0, "acc")
        st.dup("dp", "end")              # LIM: dp of the last (possibly overlapping) chunk
        st.push(32 * (256 - C), "c")
        st.op("ADD", 2, "end")
        st.push(lanemask(bits), "MB")
        st.to_top("dp")
        st.swap(1)
        st.to_top("off")
        st.swap(1)                     # [.., consts, off, dp]
        assert st.s[-2:] == ["off", "dp"], st.s

        def body(ncoef):
            assert ncoef % G == 0
            for nm, v in (("M8", M8), ("M16", M16), ("M32", M32), ("M64X", bytepattern((1 << 64) - 1, 16))):
                st.push(v, nm)
            for j in used:
                st.dup("off", "v")
                if offs[j] != o0:
                    st.push(offs[j] - o0, "c")
                    st.op("ADD", 2, "v")
                st.op("CALLDATALOAD", 1, f"V{j}")
                self.bswap256(st, f"V{j}")
            for _ in range(4):
                st.swap(4)
                st.pop()                 # drop the bswap masks (below the V words)
            st.push(0, "gs")             # bit offset of the gather group
            st.dup("dp", "gp")           # destination of its first coefficient
            glayout = list(st.s)
            gloop = self.fresh(name + "_g")
            a.label(gloop)
            # gather coefficients of every polynomial into lanes (G per lane)
            for j in used:
                st.dup(f"V{j}", "g")
                st.dup("gs", "s")
                st.op("SHR", 2, "g")
                st.push((1 << (G * bits)) - 1, "m")
                st.op("AND", 2, "g")
                if j:
                    st.push(64 * j, "s")
                    st.op("SHL", 2, "g")
                    st.op("OR", 2, "W")
                else:
                    st.rename("g", "W")
            if flags:
                st.push(0, "Lf")
            for kk in range(G):
                st.dup("W", "r")
                if kk:
                    st.push(bits * kk, "s")
                    st.op("SHR", 2, "r")
                st.dup("MB", "m")
                st.op("AND", 2, "raw")

                def store(off=32 * kk):
                    st.dup("gp", "p")
                    if off:
                        st.push(off, "c")
                        st.op("ADD", 2, "p")
                    st.op("MSTORE", 2)
                post(st, store)
            if flags:
                st.dup("acc", "A")
                st.op("OR", 2, "A")
                st.to_top("acc")
                st.pop()
                st.rename("A", "acc")
            st.pop("W")
            st.add_const("gs", G * bits)
            st.add_const("gp", 32 * G)
            assert st.s == glayout, (st.s, glayout)
            st.dup("gs", "x")
            st.push(ncoef * bits, "e")
            st.op("GT", 2, "f")
            a.jumpi(gloop)
            st.s.pop()
            st.pop("gp")
            st.pop("gs")
            for j in reversed(used):
                st.pop(f"V{j}")

        tail = 256 % C
        loop, done, noclamp = (self.fresh(name + x) for x in ("_loop", "_done", "_nc"))
        a.label(loop)
        body(C)
        # exit after the chunk at LIM; else advance (clamping the last chunk to LIM)
        st.dup("dp", "x")
        st.dup("end", "e")
        st.op("EQ", 2, "f")
        a.jumpi(done)
        st.s.pop()
        loop_layout = None
        st.add_const("off", CB)
        st.add_const("dp", 32 * C)
        if tail:
            st.dup("end", "e")
            st.dup("dp", "x")
            st.op("GT", 2, "f")          # dp > LIM
            st.op("ISZERO", 1, "f")
            a.jumpi(noclamp)
            st.s.pop()
            st.push(32 * (C - tail), "c")
            st.swap(1)
            st.op("SUB", 2, "dp")
            st.swap(1)
            st.push((C - tail) * bits // 8, "c")
            st.swap(1)
            st.op("SUB", 2, "off")
            st.swap(1)
            a.label(noclamp)
        a.jump(loop)
        a.label(done)
        st.pop("dp")
        st.pop("off")
        for nm in ("MB", "end"):
            st.pop(nm)
        if flags:
            st.swap(1)
        assert st.s[-1] == "ret" and len(st.s) == (2 if flags else 1), st.s
        a.op("JUMP")

    def z_post(self, st, store):
        """[W, Lf, raw] -> store K - raw; Lf |= ((raw + C2) << 32) | (K - raw + C1)."""
        L = self.L
        p = L.p
        Z = p["zbits"]
        K = p["g1"] + Q
        C2 = (1 << Z) - 2 * p["g1"] + p["beta"]      # bit Z set iff raw >= 2g1 - beta
        C1 = (1 << 25) - (K - p["beta"])              # bit 25 set iff K - raw >= K - beta
        lanes = lambda v: sum(v << (64 * j) for j in range(4))
        st.dup("raw", "x")
        st.push(lanes(C2), "c")
        st.op("ADD", 2, "x")
        st.push(32, "s")
        st.op("SHL", 2, "x")          # [Lf, raw, x]
        st.swap(1)                     # [Lf, x, raw]
        st.push(lanes(K), "k")
        st.op("SUB", 2, "zv")          # [Lf, x, zv]
        st.dup("zv", "zv2")
        store()                        # [Lf, x, zv]
        st.push(lanes(C1), "c")
        st.op("ADD", 2, "y")
        st.op("OR", 2, "f")
        st.op("OR", 2, "Lf")

    def flag_check(self):
        """[acc] -> [ok]: in every lane, bits zbits+32 and 25 of the z flag word are clear."""
        a, L = self.a, self.L
        bit = (1 << (L.p["zbits"] + 32)) | (1 << 25)
        a.push(sum(bit << (64 * j) for j in range(4)))
        a.op("AND")
        a.op("ISZERO")

    def gen_sample_in_ball(self):
        """c = SampleInBall(c-tilde) into CW (lane 0: 0, 1 or q-1). Exit [ok]."""
        a, L = self.a, self.L
        p = L.p
        tau = p["tau"]
        a.region("sample_in_ball")
        a.label("sib")
        cb = self.simd_c()
        if not cb:
            self.zero_ks()
            self.absorb_inline(0, p["ctb"] // 8, L.CT)
            self.xor_ks_const(p["ctb"] // 8, 0x1F * REP)
            self.xor_ks_const(16, (0x80 << 56) * REP)
            self.call("kf1")
            self.flip_ks([x for x in COMPLEMENTED if x < 17])
            a.push(L.KS)
            a.op("MLOAD")
            a.push(M64)
            a.op("AND")
        else:
            a.push(L.CB)                 # stream lanes squeezed in a SIMD slot
            a.op("MLOAD")
        # stack (bottom..top): [ret, signs, i, p]
        a.push(256 - tau)
        a.push(8)
        loop, nok, skip, done, fail = (self.fresh(x) for x in ("sibloop", "sibnok", "sibskip", "sibdone", "sibfail"))
        a.label(loop)
        a.op("DUP1")
        a.push(272)
        a.op("EQ")
        a.jumpi(fail)
        if not cb:
            a.op("DUP1")
            a.push(136)
            a.op("EQ")
            a.op("ISZERO")
            a.jumpi(nok)
            self.flip_ks([x for x in COMPLEMENTED if x < 17])
            self.call("kf1")
            self.flip_ks([x for x in COMPLEMENTED if x < 17])
            a.label(nok)
            # j = byte (p mod 136) of the current block
            a.push(136)
            a.op("DUP2")
            a.op("MOD")                 # pm
        else:
            a.op("DUP1")                # byte p of the 272-byte stream in CB
        a.op("DUP1")
        a.push(7)
        a.op("AND")
        a.push(3)
        a.op("SHL")                     # [.., pm, 8(pm&7)]
        a.op("SWAP1")
        a.push(3)
        a.op("SHR")
        a.push(5)
        a.op("SHL")
        a.push(L.CB if cb else L.KS)
        a.op("ADD")
        a.op("MLOAD")
        a.op("SWAP1")
        a.op("SHR")
        a.push(0xFF)
        a.op("AND")                     # [signs, i, p, j]
        a.op("SWAP1")
        a.push(1)
        a.op("ADD")
        a.op("SWAP1")                   # [signs, i, p+1, j]
        a.op("DUP3")
        a.op("DUP2")
        a.op("GT")                      # j > i
        a.jumpi(skip)
        # accept j (stack [ret, signs, i, p, j]); see docs: list of nonzero
        # coefficients kept as window base offsets 4064 + 8 pos - 2048 neg
        st = Stack(a, ["ret", "signs", "i", "p", "j"])
        CNT = L.MISC + 0x1C0
        # CW[i] = CW[j]
        st.dup("j", "aj")
        st.push(5, "c")
        st.op("SHL", 2, "aj")
        st.push(L.CW, "c")
        st.op("ADD", 2, "aj")
        st.dup("aj", "cj")
        st.op("MLOAD", 1, "cj")
        st.dup("i", "ai")
        st.push(5, "c")
        st.op("SHL", 2, "ai")
        st.push(L.CW, "c")
        st.op("ADD", 2, "ai")
        st.op("MSTORE", 2)
        # sgn = signs & 1; CW[j] = sgn ? 1 : -1   (code: +1 for c = -1, -1 for c = +1)
        st.dup("signs", "sg")
        st.push(1, "c")
        st.op("AND", 2, "sg")
        st.dup("sg", "n")                # NNEG += sg
        st.push(L.MISC + 0x1A0, "c")
        st.op("MLOAD", 1, "nn")
        st.op("ADD", 2, "n")
        st.push(L.MISC + 0x1A0, "c")
        st.op("MSTORE", 2)
        st.dup("sg", "code")
        st.push(1, "c")
        st.op("SHL", 2, "code")
        st.push(1, "c")
        st.swap(1)
        st.op("SUB", 2, "code")
        st.swap(1)
        st.swap(2)                       # [.., j, sg, code, aj] -> need code under aj
        st.op("MSTORE", 2)               # CW[j] = code
        # k = IDX[j]
        st.dup("j", "k")
        st.push(L.IDX, "c")
        st.op("ADD", 2, "k")
        st.op("MLOAD", 1, "k")
        st.push(248, "c")
        st.op("SHR", 2, "k")
        moved = self.fresh("sibmv")
        st.dup("k", "kk")
        st.op("ISZERO", 1, "kk")
        a.jumpi(moved)
        st.s.pop()
        # BASES[k-1] += 8 (i - j); IDX[i] = k
        st.dup("k", "ba")
        st.push(5, "c")
        st.op("SHL", 2, "ba")
        st.push(L.BASES - 32, "c")
        st.op("ADD", 2, "ba")
        st.dup("ba", "bv")
        st.op("MLOAD", 1, "bv")
        st.dup("j", "jj")
        st.dup("i", "ii")
        st.op("SUB", 2, "d")
        st.push(3, "c")
        st.op("SHL", 2, "d")
        st.op("ADD", 2, "bv")
        st.swap(1)
        st.op("MSTORE", 2)
        st.dup("k", "kv")
        st.dup("i", "ia")
        st.push(L.IDX, "c")
        st.op("ADD", 2, "ia")
        st.op("MSTORE8", 2)
        a.label(moved)
        st.pop("k")
        # BASES[cnt] = 4064 + 8 j - 2048 sg; IDX[j] = cnt + 1; cnt += 1
        st.push(CNT, "cp")
        st.op("MLOAD", 1, "cnt")
        st.push(1, "c")
        st.op("ADD", 2, "cnt")           # cnt + 1
        st.dup("cnt", "cv")
        st.dup("j", "ja")
        st.push(L.IDX, "c")
        st.op("ADD", 2, "ja")
        st.op("MSTORE8", 2)
        st.dup("cnt", "cs")
        st.push(CNT, "cp")
        st.op("MSTORE", 2)
        # value
        st.swap(1)                       # [.., cnt+1, sg]
        st.push(11, "c")
        st.op("SHL", 2, "sg")            # 2048 sg
        st.dup("j", "bj")
        st.push(3, "c")
        st.op("SHL", 2, "bj")
        st.push(4064, "c")
        st.op("ADD", 2, "bj")
        st.op("SUB", 2, "bval")          # 4064 + 8 j - 2048 sg
        st.swap(1)
        st.push(5, "c")
        st.op("SHL", 2, "cnt")
        st.push(L.BASES - 32, "c")
        st.op("ADD", 2, "cnt")
        st.op("MSTORE", 2)
        st.pop("j")
        st.expect(["ret", "signs", "i", "p"])
        a.op("SWAP2")
        a.push(1)
        a.op("SHR")
        a.op("SWAP2")                   # signs >>= 1
        a.op("SWAP1")
        a.push(1)
        a.op("ADD")
        a.op("SWAP1")                   # i += 1
        a.op("DUP2")
        a.push(256)
        a.op("EQ")
        a.jumpi(done)
        a.jump(loop)
        a.label(skip)
        a.op("POP")
        a.jump(loop)
        a.label(done)
        a.op("POP")
        a.op("POP")
        a.op("POP")
        a.push(1)
        a.op("SWAP1")
        a.op("JUMP")
        a.label(fail)
        a.op("POP")
        a.op("POP")
        a.op("POP")
        a.op("PUSH0")
        a.op("SWAP1")
        a.op("JUMP")

    def gen_decode_hint(self):
        """HintBitUnpack into HB (one 256-bit bitmap word per row). Exit [ok]."""
        a, L = self.a, self.L
        k, omega = L.k, L.p["omega"]
        a.region("decode_hint")
        a.label("dhint")
        # stack [ret, good, index]
        a.push(1)
        a.op("PUSH0")
        for i in range(k):
            bad, ok, iloop, idone = (self.fresh(x) for x in ("hbad", "hok", "hil", "hid"))
            # bound = byte(H0 + omega + i)
            a.push(L.H0 + omega + i)
            a.op("CALLDATALOAD")
            a.push(248)
            a.op("SHR")                 # [good, index, bound]
            a.op("DUP2")
            a.op("DUP2")
            a.op("LT")                  # bound < index
            a.op("DUP2")
            a.push(omega)
            a.op("LT")                  # omega < bound
            a.op("OR")
            a.op("ISZERO")
            a.jumpi(ok)
            a.op("POP")
            a.op("PUSH0")
            a.op("SWAP2")
            a.op("POP")                 # good = 0
            a.op("DUP1")                # bound = index
            a.label(ok)
            # [good, index(first), bound]; idx = first
            a.op("DUP2")                # [good, first, bound, idx]
            a.label(iloop)
            a.op("DUP2")
            a.op("DUP2")
            a.op("LT")
            a.op("ISZERO")
            a.jumpi(idone)              # idx >= bound
            # y = byte(H0 + idx)
            a.op("DUP1")
            a.push(L.H0)
            a.op("ADD")
            a.op("CALLDATALOAD")
            a.push(248)
            a.op("SHR")                 # [good, first, bound, idx, y]
            # if idx > first and byte(H0 + idx - 1) >= y: good = 0
            nomono = self.fresh("hnm")
            a.op("DUP4")
            a.op("DUP3")
            a.op("GT")                  # idx > first
            a.op("ISZERO")
            a.jumpi(nomono)
            a.op("DUP2")
            a.push(L.H0 - 1)
            a.op("ADD")
            a.op("CALLDATALOAD")
            a.push(248)
            a.op("SHR")                 # prev
            a.op("DUP2")
            a.op("GT")                  # y > prev
            a.jumpi(nomono)
            a.op("PUSH0")
            a.op("SWAP5")
            a.op("POP")
            a.label(nomono)
            # HP[i // 4][y] |= 1 << 64 (i % 4)
            a.push(5)
            a.op("SHL")
            a.push(L.HP + 0x2000 * (i // 4))
            a.op("ADD")                 # [.., idx, addr]
            a.op("DUP1")
            a.op("MLOAD")
            a.push(1 << (64 * (i % 4)))
            a.op("OR")
            a.op("SWAP1")
            a.op("MSTORE")
            a.push(1)
            a.op("ADD")
            a.jump(iloop)
            a.label(idone)
            a.op("POP")                 # [good, first, bound]
            a.op("SWAP1")
            a.op("POP")                 # [good, index=bound]
        # trailing indices must be zero
        tloop, tdone, tz = (self.fresh(x) for x in ("htl", "htd", "htz"))
        a.label(tloop)
        a.op("DUP1")
        a.push(omega)
        a.op("GT")
        a.op("ISZERO")
        a.jumpi(tdone)                  # index >= omega
        a.op("DUP1")
        a.push(L.H0)
        a.op("ADD")
        a.op("CALLDATALOAD")
        a.push(248)
        a.op("SHR")
        a.op("ISZERO")
        a.jumpi(tz)
        a.op("PUSH0")
        a.op("SWAP2")
        a.op("POP")
        a.label(tz)
        a.push(1)
        a.op("ADD")
        a.jump(tloop)
        a.label(tdone)
        a.op("POP")
        a.op("SWAP1")
        a.op("JUMP")

    # ── ExpandA fused with A * z ───────────────────────────────────────
    @staticmethod
    def spread_stages():
        """(shift, mask) stages mapping bit b of a 64-bit value to bit 4b."""
        stages = []
        pos = list(range(64))
        for jb in range(5, -1, -1):
            sft = 3 << jb
            pos = [p + sft if (b >> jb) & 1 else p for b, p in enumerate(pos)]
            stages.append((sft, sum(1 << p for p in pos)))
        return stages

    def spread_top(self):
        a = self.a
        for sft, m in self.spread_stages():
            a.op("DUP1")
            a.push(sft)
            a.op("SHL")
            a.op("OR")
            a.push(m)
            a.op("AND")

    UNZIP = [(0, 6), (0, 4), (0, 2), (1, 7), (1, 5), (1, 3)]

    def unzip_top(self):
        """4-way bit de-interleave of the top word: bit 4b+k -> bit 64k+b."""
        a = self.a
        for i, j in self.UNZIP:
            d = (1 << j) - (1 << i)
            m = sum(1 << p for p in range(256) if (p >> i) & 1 and not (p >> j) & 1)
            a.op("DUP1")
            a.push(d)
            a.op("SHR")
            a.op("DUP2")
            a.op("XOR")
            a.push(m)
            a.op("AND")
            a.op("DUP1")
            a.push(d)
            a.op("SHL")
            a.op("XOR")
            a.op("XOR")

    def gen_blk(self):
        """blk: entry [ret, abp, flp]. De-interleave the 21 rate lanes of the
        kf4 state (four SHAKE128 streams) and write the block's 56 positional
        RejNTTPoly candidates of every slot as row-packed words abp..abp+56*32;
        for every 8 candidates the flag word (lane s bit 23 set iff slot s
        rejected one of them) goes to flp.. (7 words)."""
        a, L = self.a, self.L
        assert L.KS == 0
        a.region("blk")
        a.label("blk")
        rate_c = [x for x in COMPLEMENTED if x < 21]
        self.flip_ks(rate_c)
        st = Stack(a, ["ret", "abp", "flp"])
        st.push(0, "xp")                    # KS address of the next lane
        masks = []
        for n, (i, j) in enumerate(self.UNZIP):
            m = sum(1 << p for p in range(256) if (p >> i) & 1 and not (p >> j) & 1)
            st.push(m, f"U{n}")
            masks.append(((1 << j) - (1 << i), f"U{n}"))
        layout = list(st.s)
        loop = self.fresh("bkl")
        a.label(loop)
        for w in range(3):
            st.dup("xp", f"W{w}")
            if w:
                st.push(32 * w, "c")
                st.op("ADD", 2, f"W{w}")
            st.op("MLOAD", 1, f"W{w}")
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
        C = sum(((1 << 23) - Q) << (64 * sl) for sl in range(4))
        for k in range(8):
            o = 3 * k
            w, b = o >> 3, o & 7
            if b <= 5:
                st.dup(f"W{w}", "A")
                if b:
                    st.push(8 * b, "s")
                    st.op("SHR", 2, "A")
                st.push(lanemask(23), "m")
                st.op("AND", 2, "A")
            else:
                lo = 64 - 8 * b
                st.dup(f"W{w}", "A")
                st.push(8 * b, "s")
                st.op("SHR", 2, "A")
                st.push(lanemask(lo), "m")
                st.op("AND", 2, "A")
                st.dup(f"W{w + 1}", "B")
                st.push(lanemask(23 - lo), "m")
                st.op("AND", 2, "B")
                st.push(lo, "s")
                st.op("SHL", 2, "B")
                st.op("OR", 2, "A")
            st.dup("A", "A2")
            st.dup("abp", "p")
            if k:
                st.push(32 * k, "c")
                st.op("ADD", 2, "p")
            st.op("MSTORE", 2)
            st.push(C, "c")
            st.op("ADD", 2, "A")
            st.op("OR", 2, "lf")
        st.dup("flp", "p")
        st.op("MSTORE", 2)
        for w in (2, 1, 0):
            st.pop(f"W{w}")
        st.add_const("abp", 256)
        st.add_const("flp", 32)
        st.add_const("xp", 96)
        assert st.s == layout, (st.s, layout)
        st.dup("xp", "x")
        st.push(21 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for n in reversed(range(len(masks))):
            st.pop(f"U{n}")
        for nm in ("xp", "flp", "abp"):
            st.pop(nm)
        self.flip_ks(rate_c)
        a.op("JUMP")

    def gen_pass3(self, masked=False):
        """pass3: ACC[t] += ABUF[t] * ((Z[t] >> zsh) & M64), t < 256 (lane-wise).
        Entry [ret, accp, zp, zsh]; pass3m: [ret, accp, zp, zsh, lmask] and the
        candidate words are AND-ed with lmask first."""
        a, L = self.a, self.L
        name = "pass3m" if masked else "pass3"
        a.region(name)
        a.label(name)
        st = Stack(a, ["ret", "cp", "zp", "zsh"] + (["lm"] if masked else []))
        st.push(L.ABUF, "ap")
        loop = self.fresh("p3loop")
        layout = list(st.s)
        a.label(loop)
        U = 8
        for k in range(U):
            o = 32 * k
            st.dup("cp", "addr")
            if o:
                st.push(o, "c")
                st.op("ADD", 2, "addr")
            st.dup("addr", "accv")
            st.op("MLOAD", 1, "accv")
            st.dup("ap", "A")
            if o:
                st.push(o, "c")
                st.op("ADD", 2, "A")
            st.op("MLOAD", 1, "A")
            if masked:
                st.dup("lm", "m")
                st.op("AND", 2, "A")
            st.dup("zp", "Z")
            if o:
                st.push(o, "c")
                st.op("ADD", 2, "Z")
            st.op("MLOAD", 1, "Z")
            st.dup("zsh", "s")
            st.op("SHR", 2, "Z")
            st.push(M64, "m")
            st.op("AND", 2, "Z")
            st.op("MUL", 2, "P")
            st.op("ADD", 2, "accv")
            st.swap(1)
            st.op("MSTORE", 2)
        for nm in ("cp", "zp", "ap"):
            st.add_const(nm, 32 * U)
        assert st.s == layout
        st.dup("ap", "x")
        st.push(L.ABUF + 256 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for nm in reversed(layout[1:]):
            st.pop(nm)
        a.op("JUMP")

    def gen_pass3x(self, name, rb, insts):
        """Mixed accumulation (v3): ABUF slot s holds an instance of row
        4 rb + l and column j for each (s, l, j) in insts. Instances with the
        same column and the same slot-to-lane shift share one product:
        ACC_rb[t] += ((ABUF[t] >> 64 max(s-l, 0)) masked << 64 max(l-s, 0))
        * z_hat_j[t]. Lanes are < 2^23 * 2^32 per product, sums < 2^64.
        Entry [ret]."""
        a, L = self.a, self.L
        a.region(name)
        a.label(name)
        terms = {}
        for (sl, ln, j) in insts:
            terms.setdefault((j, ln - sl), []).append(sl)
        st = Stack(a, ["ret"])
        st.push(0, "o")
        loop = self.fresh("p3xl")
        layout = list(st.s)
        a.label(loop)
        st.push(L.ACC + 0x2000 * rb, "addr")
        st.dup("o", "oo")
        st.op("ADD", 2, "addr")
        st.dup("addr", "accv")
        st.op("MLOAD", 1, "accv")
        st.push(L.ABUF, "X")
        st.dup("o", "oo")
        st.op("ADD", 2, "X")
        st.op("MLOAD", 1, "X")
        items = sorted(terms.items())
        for n, ((j, d), slots) in enumerate(items):
            last = n == len(items) - 1
            if last:
                st.rename("X", "x")
            else:
                st.dup("X", "x")
            mask = sum(M64 << (64 * s_) for s_ in slots)
            if mask != ALL:
                st.push(mask, "m")
                st.op("AND", 2, "x")
            if d > 0:
                st.push(64 * d, "c")
                st.op("SHL", 2, "x")
            elif d < 0:
                st.push(-64 * d, "c")
                st.op("SHR", 2, "x")
            st.push(L.ZH + 0x2000 * (j // 4), "z")
            st.dup("o", "oo")
            st.op("ADD", 2, "z")
            st.op("MLOAD", 1, "z")
            if j % 4:
                st.push(64 * (j % 4), "c")
                st.op("SHR", 2, "z")
            if j % 4 != 3:
                st.push(M64, "m")
                st.op("AND", 2, "z")
            st.op("MUL", 2, "x")
            # accv += x
            if last:
                st.op("ADD", 2, "accv")
            else:
                st.swap(1)                    # [.., accv, x, X]
                st.swap(2)                    # [.., X, x, accv]
                st.op("ADD", 2, "accv")
                st.swap(1)                    # [.., accv, X]
        st.swap(1)
        st.op("MSTORE", 2)
        st.add_const("o", 32)
        assert st.s == layout, st.s
        st.dup("o", "x")
        st.push(256 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        st.pop("o")
        a.op("JUMP")

    def gen_pass3k(self, name, rb, j0, n):
        """Kronecker accumulation for the extra group: slots 3, 2, .. hold
        A[r][j0], A[r][j0+1], .. (r = 4 rb + 3). With Z' = z_hat_{j0..} in
        lanes 0..n-1, lane 3 of ABUF[t] * Z' is sum_i a_i z_hat_{j0+i} (lower
        lanes hold partial sums < 2^53, no carry). Entry [ret]."""
        a, L = self.a, self.L
        a.region(name)
        a.label(name)
        st = Stack(a, ["ret"])
        st.push(0, "o")
        loop = self.fresh("p3kl")
        layout = list(st.s)
        a.label(loop)
        st.push(L.ACC + 0x2000 * rb, "addr")
        st.dup("o", "oo")
        st.op("ADD", 2, "addr")
        st.dup("addr", "accv")
        st.op("MLOAD", 1, "accv")
        st.push(L.ABUF, "X")
        st.dup("o", "oo")
        st.op("ADD", 2, "X")
        st.op("MLOAD", 1, "X")
        if n < 4:
            st.push(sum(M64 << (64 * (3 - i)) for i in range(n)), "m")
            st.op("AND", 2, "X")
        g0, s0 = j0 // 4, j0 % 4
        st.push(L.ZH + 0x2000 * g0, "Z")
        st.dup("o", "oo")
        st.op("ADD", 2, "Z")
        st.op("MLOAD", 1, "Z")
        if s0:
            st.push(64 * s0, "c")
            st.op("SHR", 2, "Z")
        if s0 + n > 4:
            st.push(L.ZH + 0x2000 * (g0 + 1), "Y")
            st.dup("o", "oo")
            st.op("ADD", 2, "Y")
            st.op("MLOAD", 1, "Y")
            st.push(64 * (4 - s0), "c")
            st.op("SHL", 2, "Y")
            st.op("OR", 2, "Z")
        st.op("MUL", 2, "P")
        st.push(M64 << 192, "m")
        st.op("AND", 2, "P")
        st.op("ADD", 2, "accv")
        st.swap(1)
        st.op("MSTORE", 2)
        st.add_const("o", 32)
        assert st.s == layout
        st.dup("o", "x")
        st.push(256 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        st.pop("o")
        a.op("JUMP")

    def gen_fix(self):
        """fix: entry [ret, sh] (sh = 64 s). Slot s rejected a candidate among
        its first 256 positional ones: compact lane s of ABUF in place (exact
        RejNTTPoly; the 6th squeeze is made on demand, 1008-byte bound),
        group of 8 candidates by group: a group whose flag word has no
        rejection in lane s is 8 masked word copies, a flagged group is
        scanned candidate by candidate. Exit [ok]."""
        a, L = self.a, self.L
        a.region("fix")
        a.label("fix")
        HAVE6 = L.MISC + 0x1E0
        END256 = L.ABUF + 256 * 32
        st = Stack(a, ["ret", "sh"])
        st.push(M64, "lm")
        st.dup("sh", "s")
        st.op("SHL", 2, "lm")            # lane mask
        st.dup("lm", "nm")
        st.op("NOT", 1, "nm")
        # first flagged group (exists: the caller saw a flag among groups 0..31)
        st.push(L.FL, "fp")
        f1, f1d = self.fresh("fxf1"), self.fresh("fxf1d")
        a.label(f1)
        st.dup("fp", "x")
        st.op("MLOAD", 1, "x")
        st.dup("sh", "s")
        st.push(23, "c")
        st.op("ADD", 2, "s")
        st.op("SHR", 2, "x")
        st.push(1, "c")
        st.op("AND", 2, "x")
        a.jumpi(f1d)
        st.s.pop()
        st.add_const("fp", 32)
        a.jump(f1)
        a.label(f1d)
        # wp = rp = ABUF + 8 (fp - FL)  (candidates before this group are final)
        st.dup("fp", "wp")
        st.push(L.FL, "c")
        st.swap(1)
        st.op("SUB", 2, "wp")
        st.push(3, "c")
        st.op("SHL", 2, "wp")
        st.push(L.ABUF, "c")
        st.op("ADD", 2, "wp")
        st.dup("wp", "rp")
        if getattr(self, "dbg_force6", False):
            st.dup("fp", "flim")         # debug: squeeze the 6th block after one group
            st.push(32, "c")
            st.op("ADD", 2, "flim")
        else:
            st.push(L.FL + 35 * 32, "flim")
        layout = ["ret", "sh", "lm", "nm", "fp", "wp", "rp", "flim"]
        st.expect(layout)
        gl, clean, gnext, ext, fail, done, cont, sl, sskip = (self.fresh(x) for x in
            ("fxg", "fxcl", "fxn", "fxe", "fxf", "fxd", "fxc", "fxs", "fxss"))
        a.label(gl)
        st.expect(layout)
        st.dup("fp", "x")
        st.dup("flim", "y")
        st.op("EQ", 2, "x")
        a.jumpi(ext)
        st.s.pop()
        st.dup("fp", "x")
        st.op("MLOAD", 1, "x")
        st.dup("sh", "s")
        st.push(23, "c")
        st.op("ADD", 2, "s")
        st.op("SHR", 2, "x")
        st.push(1, "c")
        st.op("AND", 2, "x")
        st.op("ISZERO", 1, "x")
        a.jumpi(clean)
        st.s.pop()
        # flagged group, branch-free: every candidate is written at wp, and wp
        # advances only on acceptance (a rejected value is overwritten by the
        # next accepted one; writes past position 255 are never read again,
        # since writes stay behind rp)
        for i in range(8):
            st.dup("rp", "v")
            if i:
                st.push(32 * i, "c")
                st.op("ADD", 2, "v")
            st.op("MLOAD", 1, "v")
            st.dup("sh", "s")
            st.op("SHR", 2, "v")
            st.push(M64, "m")
            st.op("AND", 2, "v")
            st.dup("v", "v2")
            st.push(Q, "q")
            st.op("GT", 2, "acc")            # q > v
            st.swap(1)                       # [.., acc, v]
            st.dup("sh", "s")
            st.op("SHL", 2, "v")
            st.dup("wp", "o")
            st.op("MLOAD", 1, "o")
            st.dup("nm", "m")
            st.op("AND", 2, "o")
            st.op("OR", 2, "o")
            st.dup("wp", "p")
            st.op("MSTORE", 2)               # [.., acc]
            st.push(5, "c")
            st.op("SHL", 2, "acc")
            st.dup("wp", "w2")
            st.op("ADD", 2, "wn")
            st.to_top("wp")
            st.pop()
            st.rename("wn", "wp")
        st.expect(layout)
        st.add_const("rp", 256)
        a.jump(gnext)
        # clean group: 8 masked copies lane(wp + 32 i) := lane(rp + 32 i)
        a.label(clean)
        st.expect(layout)
        for i in range(8):
            st.dup("rp", "x")
            if i:
                st.push(32 * i, "c")
                st.op("ADD", 2, "x")
            st.op("MLOAD", 1, "x")
            st.dup("lm", "m")
            st.op("AND", 2, "x")
            st.dup("wp", "p")
            if i:
                st.push(32 * i, "c")
                st.op("ADD", 2, "p")
            st.dup("p", "o")
            st.op("MLOAD", 1, "o")
            st.dup("nm", "m")
            st.op("AND", 2, "o")
            st.swap(1)                   # [x, o, p] -> [x, p, o]? keep: x | o at p
            st.swap(2)
            st.op("OR", 2, "x")
            st.swap(1)
            st.op("MSTORE", 2)
        st.add_const("wp", 256)
        st.add_const("rp", 256)
        a.label(gnext)
        st.expect(layout)
        st.add_const("fp", 32)
        st.push(END256 - 1, "e")
        st.dup("wp", "x")
        st.op("GT", 2, "f")              # wp > END256 - 1: 256 coefficients written
        a.jumpi(done)
        st.s.pop()
        a.jump(gl)
        a.label(ext)
        # candidates exhausted: squeeze the 6th block once, else fail
        st.dup("flim", "x")
        st.push(L.FL + 42 * 32, "e")
        st.op("EQ", 2, "x")
        a.jumpi(fail)
        st.s.pop()
        st.push(HAVE6, "p")
        st.op("MLOAD", 1, "h")
        a.jumpi(cont)
        st.s.pop()
        st.push(1, "one")
        st.push(HAVE6, "p")
        st.op("MSTORE", 2)
        a.push(25 * 32)
        a.push(L.KS)
        a.push(L.BK)
        a.op("MCOPY")                    # keep the group state (slots may carry tr)
        self.call("kf4")
        self.call("blk", [L.ABUF + 280 * 32, L.FL + 35 * 32])
        a.push(25 * 32)
        a.push(L.BK)
        a.push(L.KS)
        a.op("MCOPY")
        a.label(cont)
        st.pop("flim")
        st.push(L.FL + 42 * 32, "flim")
        a.jump(gl)
        a.label(done)
        for _ in range(7):
            a.op("POP")
        a.push(1)
        a.op("SWAP1")
        a.op("JUMP")
        a.label(fail)
        for _ in range(7):
            a.op("POP")
        a.op("PUSH0")
        a.op("SWAP1")
        a.op("JUMP")

    def gen_gfix(self):
        """gfix: entry [ret, amask]: OR of the first 32 rejection-flag words;
        every active slot s (bit s of amask) that rejected a candidate among
        its first 256 positional ones is fixed up (fix). Exit [ok]."""
        a, L = self.a, self.L
        a.region("gfix")
        a.label("gfix")
        st = Stack(a, ["ret", "amask"])
        st.push(L.FL, "p")
        st.op("MLOAD", 1, "flags")
        for c in range(1, 32):
            st.push(L.FL + 32 * c, "p")
            st.op("MLOAD", 1, "x")
            st.op("OR", 2, "flags")
        st.push(sum(1 << (23 + 64 * s) for s in range(4)), "m")
        st.op("AND", 2, "flags")
        st.push(1, "ok")
        st.swap(1)                       # [.., ok, flags]
        fast = self.fresh("gfast")
        st.dup("flags", "f")
        st.op("ISZERO", 1, "f")
        a.jumpi(fast)
        st.s.pop()
        for sl in range(4):
            skip = self.fresh("gskip")
            st.dup("flags", "f")
            st.push(23 + 64 * sl, "s")
            st.op("SHR", 2, "f")
            st.dup("amask", "n")
            st.push(sl, "c")
            st.op("SHR", 2, "n")
            st.op("AND", 2, "f")
            st.push(1, "one")
            st.op("AND", 2, "f")
            st.op("ISZERO", 1, "f")
            a.jumpi(skip)
            st.s.pop()
            ret = self.fresh("ret")
            a.pushl(ret)
            a.push(64 * sl)
            a.jump("fix")
            a.label(ret)
            st.s.append("r")
            st.swap(1)
            st.swap(2)                    # [.., flags, r, ok]
            st.op("AND", 2, "ok")
            st.swap(1)                    # [.., ok, flags]
            a.label(skip)
        a.label(fast)
        st.pop("flags")
        st.swap(1)
        st.pop("amask")
        st.swap(1)
        a.op("JUMP")

    def gen_group(self):
        """group: entry [ret, rb, col, amask]; one ExpandA SIMD group (column
        col, rows 4 rb + s for the slots s in amask; other slots duplicate
        row 4 rb) fused with the accumulation into ACC_rb. Exit [ok]."""
        a, L = self.a, self.L
        a.region("group")
        a.label("group")
        st = Stack(a, ["ret", "rb", "col", "amask"])
        HAVE6 = L.MISC + 0x1E0
        st.push(0, "z")
        st.push(HAVE6, "p")
        st.op("MSTORE", 2)
        ret = self.fresh("ret")
        st.pushl(ret, "r")
        st.push(0, "KEEP")
        st.push(15, "AMULT")
        st.push(0, "CMULT")
        # L4 = interleave_s(col | (4 rb + s') << 8 | 0x1F << 16), s' = s for s in amask else 0
        #    = 15 (spread(col) + spread(0x1F << 16) + (rb << 40)) + slot terms
        st.dup("col", "L4")
        st.push(1, "c")
        st.op("AND", 2, "L4")
        st.dup("col", "t")
        st.push(2, "c")
        st.op("AND", 2, "t")
        st.push(3, "c")
        st.op("SHL", 2, "t")
        st.op("OR", 2, "L4")
        st.dup("col", "t")
        st.push(4, "c")
        st.op("AND", 2, "t")
        st.push(6, "c")
        st.op("SHL", 2, "t")
        st.op("OR", 2, "L4")             # spread(col), col < 8
        st.dup("rb", "t")
        st.push(40, "c")
        st.op("SHL", 2, "t")
        st.op("OR", 2, "L4")
        st.push(spread(0x1F << 16), "c")
        st.op("OR", 2, "L4")
        st.push(15, "c")
        st.op("MUL", 2, "L4")
        for sl, term in ((1, 1 << 33), (2, 1 << 38), (3, (1 << 35) | (1 << 39))):
            st.dup("amask", "t")
            st.push(sl, "c")
            st.op("SHR", 2, "t")
            st.push(1, "c")
            st.op("AND", 2, "t")
            st.push(term, "c")
            st.op("MUL", 2, "t")
            st.op("OR", 2, "L4")
        a.jump("ginit")
        a.label(ret)
        for _ in range(5):
            st.s.pop()
        st.expect(["ret", "rb", "col", "amask"])
        for blk in range(5):
            self.call("kf4")
            self.call("blk", [L.ABUF + 56 * 32 * blk, L.FL + 7 * 32 * blk])
        ret = self.fresh("ret")
        a.pushl(ret)
        a.op("DUP2")                     # amask
        a.jump("gfix")
        a.label(ret)
        st.s.append("ok")
        if self.v4:
            # v4: the caller accumulates (deferred, fused passes)
            for nm in ("amask", "col", "rb"):
                st.swap(1)
                st.pop()
            st.swap(1)
            a.op("JUMP")
            return
        # pass3(ACC + 0x2000 rb, ZH + 0x2000 (col >> 2), 64 (col & 3))
        ret = self.fresh("ret")
        st.pushl(ret, "r2")
        st.dup("rb", "a1")
        st.push(13, "c")
        st.op("SHL", 2, "a1")
        st.push(L.ACC, "c")
        st.op("ADD", 2, "a1")
        st.dup("col", "a2")
        st.push(2, "c")
        st.op("SHR", 2, "a2")
        st.push(13, "c")
        st.op("SHL", 2, "a2")
        st.push(L.ZH, "c")
        st.op("ADD", 2, "a2")
        st.dup("col", "a3")
        st.push(3, "c")
        st.op("AND", 2, "a3")
        st.push(6, "c")
        st.op("SHL", 2, "a3")
        a.jump("pass3")
        a.label(ret)
        for _ in range(4):
            st.s.pop()
        # [ret, rb, col, amask, ok] -> [ok] + jump ret
        for nm in ("amask", "col", "rb"):
            st.swap(1)
            st.pop()
        st.swap(1)
        a.op("JUMP")

    # ── schedule-driven SIMD groups (ExpandA + tr + c riding in slots) ──
    def build_schedule(self):
        """Groups of four SIMD slots, each running 5 squeezes. Roles:
        ('A', row, col) ExpandA instance, ('tr', run) a 5-block run of
        tr = H(pk) (continued in the same slot by the next group), ('c',)
        SampleInBall's H(c-tilde), None (unused: zero state). Returns a list of
        dicts: slots, keep (slot carried over), pass3 description."""
        L = self.L
        k, l = L.k, L.l
        trruns = (L.PK // 136 + 1) // 5
        assert (L.PK // 136 + 1) % 5 == 0
        groups = []

        def pure(rb, j):
            rows = [4 * rb + s if 4 * rb + s < k else None for s in range(4)]
            return dict(slots=[('A', r, j) if r is not None else None for r in rows],
                        p3=('aligned', rb, j), keep=None)
        if L.nn == 65 and self.v3:
            # rows 0-3: 5 aligned groups. Rows 4, 5 (10 instances), tr (3 runs),
            # H(c-tilde) and mu share 4 groups (16 slot-runs); instances sit in
            # arbitrary slots and are accumulated by per-group "mix" passes.
            for j in range(l):
                groups.append(pure(0, j))
            inst = [('A', 4 + (i % 2), i // 2) for i in range(2 * l)]
            plan = [inst[0:3] + [('tr', 0)], inst[3:6] + [('tr', 1)], inst[6:9] + [('tr', 2)],
                    inst[9:10] + [('c',), ('mu',), None]]
            for gi, slots in enumerate(plan):
                mix = [(s_, r[1] - 4, r[2]) for s_, r in enumerate(slots) if r and r[0] == 'A']
                groups.append(dict(slots=slots, keep=3 if gi in (1, 2) else None, p3=('mix', 1, mix)))
            return groups
        if L.nn == 65:
            for j in range(l):
                g = pure(0, j)
                groups.append(g)
            for j in range(l):
                g = pure(1, j)
                if j < trruns:
                    g['slots'][3] = ('tr', j)
                    g['keep'] = 3 if j else None
                if j == 0:
                    g['slots'][2] = ('c',)
                if j == trruns:
                    g['slots'][3] = ('mu',)
                groups.append(g)
            return groups
        # 44 / 87: tr runs in slot 3 of the last trruns groups of the last row
        # group; the displaced A instances (row 4 rb + 3) go to one extra group
        rbl = L.GR - 1
        disp = []
        for rb in range(L.GR):
            for j in range(l):
                g = pure(rb, j)
                if rb == rbl and j >= l - trruns:
                    run = j - (l - trruns)
                    disp.append(g['slots'][3])
                    g['slots'][3] = ('tr', run)
                    g['keep'] = 3 if run else None
                    g['p3'] = ('masked', rb, j)
                groups.append(g)
        # displaced instance i (column j0 + i) in slot 3 - i: one Kronecker
        # product gives row 4 rbl + 3's dot product in lane 3
        slots = [None] * 4
        for i, d in enumerate(disp):
            slots[3 - i] = d
        extra = dict(slots=slots, keep=None, p3=('kron', rbl, disp[0][2], len(disp)))
        if L.nn == 44:
            extra['slots'][0] = ('c',)
            extra['slots'][1] = ('mu',)
        groups.append(extra)
        return groups

    def simd_c(self):
        return self.L.nn in (44, 65)

    @staticmethod
    def slotbits(slots):
        """All bit positions of the given slots in an interleaved word."""
        return sum(spread((1 << 64) - 1) << s for s in slots)

    def gen_spr(self):
        """spr: entry [ret, v] -> [spread(v)] (bit b -> bit 4b, v < 2^64)."""
        a = self.a
        a.region("spr")
        a.label("spr")
        self.spread_top()
        a.op("SWAP1")
        a.op("JUMP")

    def call_spr(self):
        """spread the top of the stack via the spr subroutine."""
        a = self.a
        ret = self.fresh("ret")
        a.pushl(ret)
        a.op("SWAP1")
        a.jump("spr")
        a.label(ret)

    def init_rho1(self):
        """RHO1[i] = spread(rho lane i) (slot 0 position), RHO1[4 + i] =
        spread(c-tilde lane i) when c-tilde's sponge runs in a SIMD slot."""
        a, L = self.a, self.L
        st = Stack(a, [])
        self.push_consts(st)
        nl = 4 + (L.p["ctb"] // 8 if self.simd_c() else 0)
        for i in range(nl):
            off = 0 if i < 4 else L.CT
            ii = i if i < 4 else i - 4
            if ii % 4 == 0:
                if i:
                    st.pop("w")
                st.push(off + 8 * ii, "w")
                st.op("CALLDATALOAD", 1, "w")
                self.bswap64x4(st, "w")
            st.dup("w", "v")
            if 192 - 64 * (ii % 4):
                st.push(192 - 64 * (ii % 4), "s")
                st.op("SHR", 2, "v")
            if ii % 4:
                st.dup("M64", "m")
                st.op("AND", 2, "v")
            self.call_spr()
            st.push(L.RHO1 + 32 * i, "p")
            st.op("MSTORE", 2)
        st.pop("w")
        self.pop_consts(st)

    def gen_ginit(self):
        """ginit: entry [ret, KEEP, AMULT, CMULT, L4]: initialise the kf4 state
        for a group: kept slots (bits KEEP) carry over, slots in AMULT
        (sum of 2^s) get the ExpandA seed rho || col || row (L4 holds lane 4,
        which includes every slot's column/row bytes and padding), the slot in
        CMULT gets c-tilde || pad (rate 136), other slots start at zero.
        Complemented lanes of fresh slots are inverted."""
        a, L = self.a, self.L
        a.region("ginit")
        a.label("ginit")
        st = Stack(a, ["ret", "KEEP", "AMULT", "CMULT", "L4"])
        CL = L.p["ctb"] // 8
        st.dup("KEEP", "NK")
        st.op("NOT", 1, "NK")
        for x in range(25):
            terms = 0
            if x < 4:
                st.push(L.RHO1 + 32 * x, "p")
                st.op("MLOAD", 1, "d")
                st.dup("AMULT", "m")
                st.op("MUL", 2, "d")
                terms += 1
            if self.simd_c() and x < CL:
                st.push(L.RHO1 + 32 * (4 + x), "p")
                st.op("MLOAD", 1, "e")
                st.dup("CMULT", "m")
                st.op("MUL", 2, "e")
                if terms:
                    st.op("XOR", 2, "d")
                else:
                    st.rename("e", "d")
                terms += 1
            consts = []
            if x == 4:
                consts.append("L4")
            if self.simd_c() and x == CL and x != 4:
                consts.append(("cm", spread(0x1F)))
            if self.simd_c() and x == 16:
                consts.append(("cm", spread(0x80 << 56)))
            if x == 20:
                consts.append(("am", spread(0x80 << 56)))
            for cst in consts:
                if cst == "L4":
                    st.dup("L4", "e")
                else:
                    kind, v = cst
                    st.push(v, "e")
                    st.dup("CMULT" if kind == "cm" else "AMULT", "m")
                    st.op("MUL", 2, "e")
                if terms:
                    st.op("XOR", 2, "d")
                else:
                    st.rename("e", "d")
                terms += 1
            if x in COMPLEMENTED:
                st.dup("NK", "e")
                if terms:
                    st.op("XOR", 2, "d")
                else:
                    st.rename("e", "d")
                terms += 1
            if not terms:
                st.push(0, "d")
            # carried-over slots
            st.push(L.KS + 32 * x, "p")
            st.op("MLOAD", 1, "o")
            st.dup("KEEP", "k")
            st.op("AND", 2, "o")
            st.op("OR", 2, "d")
            st.push(L.KS + 32 * x, "p")
            st.op("MSTORE", 2)
        st.pop("NK")
        for nm in ("L4", "CMULT", "AMULT", "KEEP"):
            st.pop(nm)
        a.op("JUMP")

    def gen_trabs(self):
        """trabs: entry [ret, off, sh, n4, lastmask, kp]: KS slot sh ^= spread
        of 4 n4 little-endian lanes from calldata at off into the lanes from
        address kp on (lanes of the last group of four masked by lastmask, a
        mask on the byte-swapped word)."""
        a, L = self.a, self.L
        a.region("trabs")
        a.label("trabs")
        st = Stack(a, ["ret", "off", "sh", "n4", "lm", "kp"])
        if self.v4:
            return self.gen_trabs_zip(st)
        stages = self.spread_stages()
        for k, (_, m) in enumerate(stages):
            st.push(m, f"S{k}")
        loop, nomask = self.fresh("tal"), self.fresh("tanm")
        layout = list(st.s)
        a.label(loop)
        for nm, v in (("M8", M8), ("M16", M16), ("M32", M32)):
            st.push(v, nm)
        st.dup("off", "w")
        st.op("CALLDATALOAD", 1, "w")
        self.bswap64x4(st, "w")
        for _ in range(3):
            st.swap(1)
            st.pop()
        st.dup("n4", "f")
        st.push(1, "c")
        st.op("EQ", 2, "f")
        st.op("ISZERO", 1, "f")
        a.jumpi(nomask)
        st.s.pop()
        st.dup("lm", "m")
        st.op("AND", 2, "w")
        a.label(nomask)
        for i in range(4):
            if i < 3:
                st.dup("w", "v")
            else:
                st.rename("w", "v")
            if i < 3:
                st.push(192 - 64 * i, "s")
                st.op("SHR", 2, "v")
            if 0 < i < 3:
                st.push(M64, "m")
                st.op("AND", 2, "v")
            elif i == 3:
                st.push(M64, "m")
                st.op("AND", 2, "v")
            for k, (sft, _) in enumerate(stages):
                st.dup("v", "t")
                st.push(sft, "c")
                st.op("SHL", 2, "t")
                st.op("OR", 2, "v")
                st.dup(f"S{k}", "m")
                st.op("AND", 2, "v")
            st.dup("sh", "s")
            st.op("SHL", 2, "v")
            st.dup("kp", "p")
            if i:
                st.push(32 * i, "c")
                st.op("ADD", 2, "p")
            st.dup("p", "p2")
            st.op("MLOAD", 1, "k")
            st.swap(1)
            st.swap(2)
            st.op("XOR", 2, "v")
            st.swap(1)
            st.op("MSTORE", 2)
        st.add_const("off", 32)
        st.add_const("kp", 128)
        st.sub_const("n4", 1)
        assert st.s == layout, (st.s, layout)
        st.dup("n4", "f")
        a.jumpi(loop)
        st.s.pop()
        for k in reversed(range(len(stages))):
            st.pop(f"S{k}")
        st.pop("kp")
        for nm in ("lm", "n4", "sh", "off"):
            st.pop(nm)
        a.op("JUMP")

    # bswap64x4 then zip (bit 64 i + b -> 4 b + i) as one bit permutation of
    # the CALLDATALOAD word: complement index bit 4, then the zip
    # transpositions of index bits (unzip's in reverse order), the second
    # one with complement (an index-bit map, found by search; checked below)
    TRZIP = [('c', 4), ('t', 1, 3, 0), ('t', 1, 5, 1), ('t', 1, 7, 0),
             ('t', 0, 2, 0), ('t', 0, 4, 0), ('t', 0, 6, 0)]

    @classmethod
    def trzip_stages(cls):
        """Delta swaps (d, mask) of TRZIP: t = ((x >> d) ^ x) & mask;
        x ^= t ^ (t << d) moves bit p to p + d for p in mask."""
        out = []
        for st_ in cls.TRZIP:
            if st_[0] == 'c':
                i = st_[1]
                out.append((1 << i, sum(1 << p for p in range(256) if not (p >> i) & 1)))
            else:
                _, i, j, c = st_
                if c:
                    out.append(((1 << i) + (1 << j), sum(1 << p for p in range(256)
                                                         if not (p >> i) & 1 and not (p >> j) & 1)))
                else:
                    out.append(((1 << j) - (1 << i), sum(1 << p for p in range(256)
                                                         if (p >> i) & 1 and not (p >> j) & 1)))
        # check: bit p of the word ends at 4 n + k, k = p >> 6, n = LE bit of byte-swapped lane
        perm = list(range(256))
        for d, m in out:
            perm = [x + d if (m >> x) & 1 else (x - d if x >= d and (m >> (x - d)) & 1 else x) for x in perm]
        for p in range(256):
            k, q = p >> 6, p & 63
            assert perm[p] == 4 * ((7 - (q >> 3)) << 3 | (q & 7)) + k
        return out

    def gen_trabs_zip(self, st):
        """trabs body (v4): byte swap and zip of the four lanes of a calldata
        word as one 7-stage delta-swap network (TRZIP): lane i of the
        byte-swapped word lands in slot i (bit 64 i + b -> bit 4 b + i), so
        KS[kp + 32 i] ^= ((Z >> (3 - i)) & slot0) << sh for calldata lane i."""
        a = self.a
        S0 = self.slotbits([0])
        zs = self.trzip_stages()
        for k, (_, m) in enumerate(zs):
            st.push(m, f"U{k}")
        st.push(S0, "S0")
        loop, nomask = self.fresh("tal"), self.fresh("tanm")
        layout = list(st.s)
        a.label(loop)
        st.dup("off", "w")
        st.op("CALLDATALOAD", 1, "w")
        st.dup("n4", "f")
        st.push(1, "c")
        st.op("EQ", 2, "f")
        st.op("ISZERO", 1, "f")
        a.jumpi(nomask)
        st.s.pop()
        st.dup("lm", "m")               # lane-aligned: same mask before the byte swap
        st.op("AND", 2, "w")
        a.label(nomask)
        for k, (d, _) in enumerate(zs):
            st.dup("w", "t")
            st.push(d, "c")
            st.op("SHR", 2, "t")
            st.dup("w", "x2")
            st.op("XOR", 2, "t")
            st.dup(f"U{k}", "m")
            st.op("AND", 2, "t")
            st.dup("t", "t2")
            st.push(d, "c")
            st.op("SHL", 2, "t2")
            st.op("XOR", 2, "t")
            st.op("XOR", 2, "w")
        for i in range(4):
            # calldata lane i sits in word lane 3 - i -> slot 3 - i
            s_ = 3 - i
            if i < 3:
                st.dup("w", "v")
            else:
                st.rename("w", "v")
            if s_:
                st.push(s_, "c")
                st.op("SHR", 2, "v")
            st.dup("S0", "m")
            st.op("AND", 2, "v")
            st.dup("sh", "s")
            st.op("SHL", 2, "v")
            st.dup("kp", "p")
            if i:
                st.push(32 * i, "c")
                st.op("ADD", 2, "p")
            st.dup("p", "p2")
            st.op("MLOAD", 1, "k")
            st.swap(1)
            st.swap(2)
            st.op("XOR", 2, "v")
            st.swap(1)
            st.op("MSTORE", 2)
        st.add_const("off", 32)
        st.add_const("kp", 128)
        st.sub_const("n4", 1)
        assert st.s == layout, (st.s, layout)
        st.dup("n4", "f")
        a.jumpi(loop)
        st.s.pop()
        st.pop("S0")
        for k in reversed(range(len(zs))):
            st.pop(f"U{k}")
        st.pop("kp")
        for nm in ("lm", "n4", "sh", "off"):
            st.pop(nm)
        a.op("JUMP")

    def has_mu_slot(self):
        return any(r and r[0] == 'mu' for g in self.schedule for r in g['slots'])

    def gen_mu0(self):
        """mu0: entry [ret, sh]. If |M| <= 69, mu's single padded block
        (tr || 0 || 0 || M || pad) is absorbed into the fresh slot sh, so one
        SIMD squeeze yields mu; otherwise nothing (mu then uses kf1)."""
        a, L = self.a, self.L
        a.region("mu0")
        a.label("mu0")
        st = Stack(a, ["ret", "sh"])
        st.push(L.HDR, "h")
        a.op("CALLDATASIZE")
        st.s.append("cs")
        st.op("SUB", 2, "mlen")
        skip = self.fresh("mu0s")
        st.push(69, "c")
        st.dup("mlen", "m")
        st.op("GT", 2, "f")
        a.jumpi(skip)
        st.s.pop()
        for x in range(8):
            st.push(L.TRL + 32 * x, "p")
            st.op("MLOAD", 1, "v")
            self.call_spr()
            st.dup("sh", "s")
            st.op("SHL", 2, "v")
            st.push(L.KS + 32 * x, "p")
            st.op("MLOAD", 1, "k")
            st.op("XOR", 2, "v")
            st.push(L.KS + 32 * x, "p")
            st.op("MSTORE", 2)
        # lanes 8..16: stream bytes 64..135 = calldata from HDR - 2 ...
        ret = self.fresh("ret")
        st.pushl(ret, "r")
        st.push(L.HDR - 2, "o")
        st.dup("sh", "s")
        st.push(3, "n")
        st.push(ALL ^ ((1 << 192) - 1), "lm")
        st.push(L.KS + 8 * 32, "kp")
        a.jump("trabs")
        a.label(ret)
        for _ in range(6):
            st.s.pop()
        # ... minus the two signature bytes in front of M (lane 8, bytes 0, 1)
        st.push(L.HDR - 2, "o")
        st.op("CALLDATALOAD", 1, "w")
        st.dup("w", "v")
        st.push(248, "c")
        st.op("SHR", 2, "v")
        st.swap(1)
        st.push(232, "c")
        st.op("SHR", 2, "w")
        st.push(0xFF00, "c")
        st.op("AND", 2, "w")
        st.op("OR", 2, "v")
        self.call_spr()
        st.dup("sh", "s")
        st.op("SHL", 2, "v")
        st.push(L.KS + 8 * 32, "p")
        st.op("MLOAD", 1, "k")
        st.op("XOR", 2, "v")
        st.push(L.KS + 8 * 32, "p")
        st.op("MSTORE", 2)
        # padding: 0x1F at stream byte P = 66 + |M|, 0x80 at byte 135
        st.dup("mlen", "P")
        st.push(66, "c")
        st.op("ADD", 2, "P")
        st.dup("P", "b")
        st.push(7, "c")
        st.op("AND", 2, "b")
        st.push(3, "c")
        st.op("SHL", 2, "b")
        st.push(0x1F, "v")
        st.swap(1)
        st.op("SHL", 2, "v")
        self.call_spr()
        st.dup("sh", "s")
        st.op("SHL", 2, "v")             # [.., P, v]
        st.swap(1)
        st.push(3, "c")
        st.op("SHR", 2, "P")
        st.push(5, "c")
        st.op("SHL", 2, "P")
        st.push(L.KS, "c")
        st.op("ADD", 2, "P")             # [.., v, addr]
        st.dup("P", "p2")
        st.op("MLOAD", 1, "k")
        st.swap(1)
        st.swap(2)                       # [.., addr, k, v]
        st.op("XOR", 2, "v")
        st.swap(1)
        st.op("MSTORE", 2)
        st.push(spread(0x80 << 56), "v")
        st.dup("sh", "s")
        st.op("SHL", 2, "v")
        st.push(L.KS + 16 * 32, "p")
        st.op("MLOAD", 1, "k")
        st.op("XOR", 2, "v")
        st.push(L.KS + 16 * 32, "p")
        st.op("MSTORE", 2)
        a.label(skip)
        st.pop("mlen")
        st.pop("sh")
        a.op("JUMP")

    def gen_cext(self):
        """cext: entry [ret, dst, sh, n]: dst[x] = lane x (64-bit value) of
        slot sh of the kf4 state, x < n (complemented lanes inverted)."""
        a, L = self.a, self.L
        a.region("cext")
        a.label("cext")
        cmask = sum(1 << x for x in COMPLEMENTED)
        st = Stack(a, ["ret", "dst", "sh", "n"])
        st.push(0, "x")
        loop = self.fresh("cxl")
        layout = list(st.s)
        a.label(loop)
        st.dup("x", "v")
        st.push(5, "c")
        st.op("SHL", 2, "v")
        st.op("MLOAD", 1, "v")
        st.dup("sh", "s")
        st.op("SHR", 2, "v")
        st.push(spread((1 << 64) - 1), "m")
        st.op("AND", 2, "v")
        # compress: the spread stages inverted (bit 4b -> bit b)
        sts = self.spread_stages()
        before = [(1 << 64) - 1] + [m for _, m in sts[:-1]]
        for (sft, _), mb in reversed(list(zip(sts, before))):
            st.dup("v", "t")
            st.push(sft, "c")
            st.op("SHR", 2, "t")
            st.op("OR", 2, "v")
            st.push(mb, "c")
            st.op("AND", 2, "v")
        st.push(cmask, "c")
        st.dup("x", "xx")
        st.op("SHR", 2, "c")
        st.push(1, "o")
        st.op("AND", 2, "c")
        st.push((1 << 64) - 1, "m")
        st.op("MUL", 2, "c")
        st.op("XOR", 2, "v")
        st.dup("x", "p")
        st.push(5, "c")
        st.op("SHL", 2, "p")
        st.dup("dst", "d")
        st.op("ADD", 2, "p")
        st.op("MSTORE", 2)
        st.add_const("x", 1)
        assert st.s == layout
        st.dup("n", "e")
        st.dup("x", "xx")
        st.op("LT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for nm in ("x", "n", "sh", "dst"):
            st.pop(nm)
        a.op("JUMP")

    # ── v4: deferred, fused A * z accumulation ──────────────────────────
    @staticmethod
    def acc_items(g):
        """Accumulation terms of one group's (fixed-up) ABUF: ('lane', j,
        mask or None, d): ACC += ((X & mask) << 64 d) * z_hat_j lane-wise
        (d < 0: >>), ('kron', j0, n): ACC lane 3 += Kronecker dot product."""
        p3, slots = g['p3'], g['slots']
        if p3[0] == 'aligned':
            assert all(r and r[0] == 'A' for r in slots)
            return [('lane', p3[2], None, 0)]
        if p3[0] == 'masked':
            lm = sum(M64 << (64 * s_) for s_, r in enumerate(slots) if r and r[0] == 'A')
            return [('lane', p3[2], lm, 0)]
        if p3[0] == 'mix':
            terms = {}
            for (sl, ln, j) in p3[2]:
                terms.setdefault((j, ln - sl), []).append(sl)
            out = []
            for (j, d), sls in sorted(terms.items()):
                m = sum(M64 << (64 * s_) for s_ in sls)
                out.append(('lane', j, None if m == ALL else m, d))
            return out
        assert p3[0] == 'kron'
        return [('kron', p3[2], p3[3])]

    def plan_accumulation(self):
        """v4: instead of one ACC read-modify-write pass per group, a group's
        fixed-up candidates (ABUF[0, 256)) are copied (MCOPY) to a side
        buffer that is dead during ExpandA, and one fused pass per batch
        adds all of the batch's products into ACC_rb, reading and writing
        each ACC word once. The first batch of a row group stores instead
        of adding, so ACC needs no zero initialisation and a later row
        group's ACC serves as a side buffer meanwhile. Side buffers: CW
        (SampleInBall runs after ExpandA), HP (HintBitUnpack runs after
        ExpandA), ACC_g for row groups g not yet started; CW and HP are
        zeroed again after ExpandA."""
        L = self.L
        sched = self.schedule
        rbs = [g['p3'][1] for g in sched]
        assert rbs == sorted(rbs), rbs
        last = {rb: gi for gi, rb in enumerate(rbs)}
        self.acc_plan = {}
        self.fused = []
        self.zeroed = []
        pending, started = [], set()
        for gi, g in enumerate(sched):
            rb = rbs[gi]
            pool = [L.CW] + [L.HP + 0x2000 * h for h in range(L.GR)] \
                + [L.ACC + 0x2000 * h for h in range(rb + 1, L.GR)]
            free = [b for b in pool if b not in [x for x, _ in pending]]
            if gi == last[rb] or not free:
                bufs = pending + [(L.ABUF, self.acc_items(g))]
                name = f"pass3f{gi}"
                self.fused.append((name, rb, rb not in started, bufs))
                self.acc_plan[gi] = ('pass', name)
                started.add(rb)
                pending = []
            else:
                b = free[0]
                pending.append((b, self.acc_items(g)))
                self.acc_plan[gi] = ('copy', b)
                if b < L.ACC or b >= L.HP:
                    if b not in self.zeroed:
                        self.zeroed.append(b)

    def accumulate(self, gi):
        a, L = self.a, self.L
        kind, x = self.acc_plan[gi]
        if kind == 'copy':
            a.push(0x2000)
            a.push(L.ABUF)
            a.push(x)
            a.op("MCOPY")
        else:
            self.call(x)

    def zero_side_buffers(self):
        """v4: zero the side buffers in CW / HP again (8 KB each): MSTORE one
        word, then double the zero prefix with MCOPY; later buffers copy
        from the first."""
        a = self.a
        z0 = None
        for b in self.zeroed:
            if z0 is None:
                a.op("PUSH0")
                a.push(b)
                a.op("MSTORE")
                n = 32
                while n < 0x2000:
                    a.push(n)
                    a.push(b)
                    a.push(b + n)
                    a.op("MCOPY")
                    n *= 2
                z0 = b
            else:
                a.push(0x2000)
                a.push(z0)
                a.push(b)
                a.op("MCOPY")

    def gen_pass3f(self, name, rb, first, bufs, unroll):
        """Fused accumulation (v4): for t < 256, ACC_rb[t] (+)= sum over the
        side buffers B and their terms of the lane-wise products (see
        acc_items); `first`: store instead of add. Per term, lanes are
        < 2^23 * 2^32; the sum per ACC lane is the same as v3's (< 2^57).
        Entry [ret]."""
        a, L = self.a, self.L
        a.region(name)
        a.label(name)
        acc = L.ACC + 0x2000 * rb
        zuse = {}
        masks = []
        kron = False
        for _, items in bufs:
            for it in items:
                if it[0] == 'lane':
                    gs = [it[1] // 4]
                    if it[2] is not None and it[2] not in masks:
                        masks.append(it[2])
                else:
                    kron = True
                    g0, s0 = divmod(it[1], 4)
                    gs = [g0] + ([g0 + 1] if s0 + it[2] > 4 else [])
                    if it[2] < 4:
                        km = sum(M64 << (64 * (3 - i)) for i in range(it[2]))
                        if km not in masks:
                            masks.append(km)
                for zg in gs:
                    zuse[zg] = zuse.get(zg, 0) + 1
        if kron:
            masks.append(M64 << 192)
        addrs = [acc] + [L.ZH + 0x2000 * zg for zg in zuse] + [b for b, _ in bufs]
        base = min(addrs)
        st = Stack(a, ["ret"])
        st.push(M64, "M64")
        for i, m in enumerate(masks):
            st.push(m, f"m{i}")
        mname = {m: f"m{i}" for i, m in enumerate(masks)}
        st.push(base, "p")
        layout = list(st.s)
        loop = self.fresh("p3fl")
        a.label(loop)

        def addr(x, off, nm):
            st.dup("p", nm)
            if x - base + off:
                st.push(x - base + off, "c")
                st.op("ADD", 2, nm)

        for u in range(unroll):
            off = 32 * u
            for zg in sorted(zuse):
                if zuse[zg] >= 2:
                    addr(L.ZH + 0x2000 * zg, off, f"Z{zg}")
                    st.op("MLOAD", 1, f"Z{zg}")

            def zget(zg, nm):
                if zuse[zg] >= 2:
                    st.dup(f"Z{zg}", nm)     # shared: popped after the store
                else:
                    addr(L.ZH + 0x2000 * zg, off, nm)
                    st.op("MLOAD", 1, nm)

            have = False
            if not first:
                addr(acc, off, "acc")
                st.op("MLOAD", 1, "acc")
                have = True
            for b, items in bufs:
                addr(b, off, "X")
                st.op("MLOAD", 1, "X")
                for k, it in enumerate(items):
                    # z (the scalar or Kronecker multiplier) first, then x
                    if it[0] == 'lane':
                        _, j, m, d = it
                        zget(j // 4, "z")
                        s_ = j % 4
                        if s_:
                            st.push(64 * s_, "c")
                            st.op("SHR", 2, "z")
                        if s_ != 3:
                            st.dup("M64", "mm")
                            st.op("AND", 2, "z")
                    else:
                        _, j0, n = it
                        g0, s0 = divmod(j0, 4)
                        zget(g0, "z")
                        if s0:
                            st.push(64 * s0, "c")
                            st.op("SHR", 2, "z")
                        if s0 + n > 4:
                            zget(g0 + 1, "y")
                            st.push(64 * (4 - s0), "c")
                            st.op("SHL", 2, "y")
                            st.op("OR", 2, "z")
                    if k == len(items) - 1:
                        assert st.s[-2] == "X", st.s
                        st.to_top("X")
                        st.rename("X", "x")
                    else:
                        st.dup("X", "x")
                    if it[0] == 'lane':
                        if m is not None:
                            st.dup(mname[m], "mm")
                            st.op("AND", 2, "x")
                        if d > 0:
                            st.push(64 * d, "c")
                            st.op("SHL", 2, "x")
                        elif d < 0:
                            st.push(-64 * d, "c")
                            st.op("SHR", 2, "x")
                        st.op("MUL", 2, "x")
                    else:
                        if n < 4:
                            st.dup(mname[sum(M64 << (64 * (3 - i)) for i in range(n))], "mm")
                            st.op("AND", 2, "x")
                        st.op("MUL", 2, "x")
                        st.dup(mname[M64 << 192], "mm")
                        st.op("AND", 2, "x")
                    # accumulate x; X (if still needed) stays on top
                    if not have:
                        st.rename("x", "acc")
                        if st.s[-2] == "X":
                            st.swap(1)           # [acc, X]
                        have = True
                    elif st.s[-2] == "acc":
                        st.op("ADD", 2, "acc")
                    else:
                        assert st.s[-3:] == ["acc", "X", "x"], st.s
                        st.swap(1)               # [acc, x, X]
                        st.swap(2)               # [X, x, acc]
                        st.op("ADD", 2, "acc")
                        st.swap(1)               # [acc, X]
            zs = [f"Z{zg}" for zg in sorted(zuse) if zuse[zg] >= 2]
            assert st.s == layout + zs + ["acc"], st.s
            addr(acc, off, "q")
            st.op("MSTORE", 2)
            for _ in zs:
                st.op("POP", 1)
        st.add_const("p", 32 * unroll)
        assert st.s == layout
        st.dup("p", "x")
        st.push(base + 256 * 32, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for nm in reversed(layout[1:]):
            st.pop(nm)
        a.op("JUMP")

    def expand_a(self):
        """All SIMD groups of the schedule; stack [ok] -> [ok]."""
        a, L = self.a, self.L
        a.region("expand_a")
        if self.v4:
            self.plan_accumulation()
        nb = L.PK // 136 + 1
        for gi, g in enumerate(self.schedule):
            slots = g['slots']
            p3 = g['p3']
            Aslots = [s_ for s_, r in enumerate(slots) if r and r[0] == 'A']
            amask = sum(1 << s_ for s_ in Aslots)
            seeds = []
            for s_ in range(4):
                r = slots[s_]
                if r and r[0] == 'A':
                    seeds.append(r[2] | r[1] << 8 | 0x1F << 16)
                elif g['keep'] is None and p3[0] == 'aligned' and r is None:
                    # pure group with fewer rows: duplicate the first instance
                    r0 = slots[0]
                    seeds.append(r0[2] | r0[1] << 8 | 0x1F << 16)
                else:
                    seeds.append(0)
            trs = [s_ for s_, r in enumerate(slots) if r and r[0] == 'tr']
            cs = [s_ for s_, r in enumerate(slots) if r and r[0] == 'c']
            mus = [s_ for s_, r in enumerate(slots) if r and r[0] == 'mu']
            if p3[0] == 'aligned' and not trs and not cs and not mus:
                rb, j = p3[1], p3[2]
                assert amask == (1 << len(Aslots)) - 1 and j < 8 and rb < 2
                ret = self.fresh("ret")
                a.pushl(ret)
                a.push(rb)
                a.push(j)
                a.push(amask)
                a.jump("group")
                a.label(ret)
                a.op("AND")
                if self.v4:
                    self.accumulate(gi)
                continue
            # mixed group: explicit init, block loop with tr / c riders
            amult = sum(1 << s_ for s_ in range(4) if seeds[s_])
            cslot = cs[0] if cs else None
            if cslot is not None:
                seeds[cslot] = 0x1F if L.p["ctb"] // 8 == 4 else 0
            l4 = interleave(seeds)
            keep = self.slotbits([g['keep']]) if g['keep'] is not None else 0
            a.op("PUSH0")
            a.push(L.MISC + 0x1E0)
            a.op("MSTORE")                   # HAVE6 = 0
            self.call("ginit", [keep, amult, (1 << cslot) if cslot is not None else 0, l4])
            if mus:
                self.call("mu0", [mus[0]])
            for blk in range(5):
                if trs:
                    sh = trs[0]
                    b = 5 * slots[sh][1] + blk
                    if b < nb - 1:
                        self.call("trabs", [136 * b, sh, 5, ALL ^ ((1 << 192) - 1), L.KS])
                    else:
                        rem = (L.PK % 136) // 8
                        n4 = (rem + 3) // 4
                        keepl = rem - 4 * (n4 - 1)
                        self.call("trabs", [136 * b, sh, n4, ALL ^ ((1 << (256 - 64 * keepl)) - 1), L.KS])
                        self.xor_ks_const(rem, spread(0x1F) << sh)
                        self.xor_ks_const(16, spread(0x80 << 56) << sh)
                self.call("kf4")
                self.call("blk", [L.ABUF + 56 * 32 * blk, L.FL + 7 * 32 * blk])
                if cslot is not None and blk < 2:
                    self.call("cext", [L.CB + 17 * 32 * blk, cslot, 17])
                if mus and blk == 0:
                    self.call("cext", [L.MU, mus[0], 8])
            if trs and 5 * slots[trs[0]][1] + 4 == nb - 1:
                self.call("cext", [L.TRL, trs[0], 8])
            ret = self.fresh("ret")
            a.pushl(ret)
            a.push(amask)
            a.jump("gfix")
            a.label(ret)
            a.op("AND")
            if self.v4:
                self.accumulate(gi)
            elif p3[0] == 'aligned':
                rb, j = p3[1], p3[2]
                self.call("pass3", [L.ACC + 0x2000 * rb, L.ZH + 0x2000 * (j // 4), 64 * (j % 4)])
            elif p3[0] == 'masked':
                rb, j = p3[1], p3[2]
                lm = sum(M64 << (64 * s_) for s_ in Aslots)
                self.call("pass3m", [L.ACC + 0x2000 * rb, L.ZH + 0x2000 * (j // 4), 64 * (j % 4), lm])
            elif p3[0] == 'mix':
                self.call(f"pass3x{gi}")
            else:
                self.call(f"pass3k{gi}")

    # ── sparse c * t1 in the normal domain ──────────────────────────────
    # Per row group, a table of 768 16-bit fields per row, interleaved by row
    # (field 4e + r at byte X - 2 (4e + r), X = TT + 6142): entries e < 256
    # and e >= 512 hold 1023 - t1_r[e mod 256], 256 <= e < 512 hold t1_r[e - 256].
    # Then S'(t) = sum over nonzero c_p of the window entry e = t - p + 256
    # (+256 if c_p = -1) equals c*t1(t) + 1023 n_neg(t); one 32-byte MLOAD
    # reads 4 coefficients x 4 rows, so a row group needs 64 x tau loads.
    @staticmethod
    def dswap(st, x, d, m):
        """delta swap on stack value x (on top): swap bits p and p + d for p in m."""
        st.dup(x, "t")
        st.push(d, "c")
        st.op("SHR", 2, "t")
        st.dup(x, "x2")
        st.op("XOR", 2, "t")
        st.push(m, "c")
        st.op("AND", 2, "t")
        st.dup("t", "t2")
        st.push(d, "c")
        st.op("SHL", 2, "t2")
        st.op("XOR", 2, "t")
        st.op("XOR", 2, x)

    # 4x4 transpose of 16-bit cells: (r, k) at 64 r + 16 k <-> (k, r)
    T1M = sum(((1 << 32) - 1) << (32 + 64 * r) for r in (0, 1))
    T2M = sum(0xFFFF << (64 * r + 16 * k) for r in (0, 2) for k in (1, 3))

    def transpose16(self, st, x):
        self.dswap(st, x, 96, self.T1M)
        self.dswap(st, x, 48, self.T2M)

    def gen_tbuild(self):
        """tbuild: entry [ret, off, tt]: the window table of the four t1 rows
        at calldata offsets off + 320 r into tt (6 KB)."""
        a, L = self.a, self.L
        a.region("tbuild")
        a.label("tbuild")
        st = Stack(a, ["ret", "off", "tt"])
        st.dup("tt", "end")                 # last chunk: words 58..63 (t 232..255)
        st.push(4064 - 32 * 58, "c")
        st.op("ADD", 2, "end")              # P address of word v is tt + 4064 - 32 v
        st.swap(2)
        st.swap(1)
        st.expect(["ret", "end", "off", "tt"])
        st.dup("tt", "pa")
        st.push(4064, "c")
        st.op("ADD", 2, "pa")
        loop, done, noclamp, inner = (self.fresh("tb" + x) for x in ("l", "d", "nc", "in"))
        a.label(loop)
        for nm, v in (("M8", M8), ("M16", M16), ("M32", M32), ("M64X", bytepattern((1 << 64) - 1, 16))):
            st.push(v, nm)
        for r in range(4):
            st.dup("off", f"V{r}")
            if r:
                st.push(320 * r, "c")
                st.op("ADD", 2, f"V{r}")
            st.op("CALLDATALOAD", 1, f"V{r}")
            self.bswap256(st, f"V{r}")
        for _ in range(4):
            st.swap(4)
            st.pop()                        # drop the bswap masks (below the V words)
        st.push(0, "sh")                    # 40 kk
        inner_layout = list(st.s)
        a.label(inner)
        # gather 4 coefficients of each row: lane r = t1_r[4v..4v+3] (10-bit fields)
        for r in range(4):
            st.dup(f"V{r}", "g")
            st.dup("sh", "s")
            st.op("SHR", 2, "g")
            st.push((1 << 40) - 1, "c")
            st.op("AND", 2, "g")
            if r:
                st.push(64 * r, "c")
                st.op("SHL", 2, "g")
                st.op("OR", 2, "W")
            else:
                st.rename("g", "W")
        # 10-bit fields at 10k -> 16-bit cells at 16k inside each lane
        st.dup("W", "h")
        st.push(lanemask(40) ^ lanemask(20), "c")
        st.op("AND", 2, "h")
        st.push(12, "c")
        st.op("SHL", 2, "h")
        st.swap(1)
        st.push(lanemask(20), "c")
        st.op("AND", 2, "W")
        st.op("OR", 2, "W")
        st.dup("W", "h")
        st.push(sum((0x3FF << 10 | 0x3FF << 42) << (64 * r) for r in range(4)), "c")
        st.op("AND", 2, "h")
        st.push(6, "c")
        st.op("SHL", 2, "h")
        st.swap(1)
        st.push(sum((0x3FF | 0x3FF << 32) << (64 * r) for r in range(4)), "c")
        st.op("AND", 2, "W")
        st.op("OR", 2, "W")
        self.transpose16(st, "W")           # cell (k, r) at 64 k + 16 r = field 4k + r
        # P word at pa; N copies at pa + 2048 and pa - 2048
        st.dup("W", "w2")
        st.dup("pa", "p")
        st.op("MSTORE", 2)
        st.push(sum(1023 << (16 * f) for f in range(16)), "c")
        st.op("XOR", 2, "W")
        st.dup("W", "w2")
        st.dup("pa", "p")
        st.push(2048, "c")
        st.op("ADD", 2, "p")
        st.op("MSTORE", 2)
        st.dup("pa", "p")
        st.push(2048, "c")
        st.swap(1)
        st.op("SUB", 2, "p")
        st.op("MSTORE", 2)
        st.sub_const("pa", 32)
        st.add_const("sh", 40)
        assert st.s == inner_layout, (st.s, inner_layout)
        st.dup("sh", "x")
        st.push(240, "e")
        st.op("GT", 2, "f")
        a.jumpi(inner)
        st.s.pop()
        st.pop("sh")
        for r in (3, 2, 1, 0):
            st.pop(f"V{r}")
        # pa is 6 words further now; exit after the chunk that ended at end - 192
        st.dup("pa", "x")
        st.dup("end", "e")
        st.push(6 * 32, "c")
        st.swap(1)
        st.op("SUB", 2, "e")
        st.op("EQ", 2, "f")
        a.jumpi(done)
        st.s.pop()
        st.add_const("off", 30)
        st.dup("end", "e")
        st.dup("pa", "x")
        st.op("LT", 2, "f")               # pa < end: clamp to the last chunk
        st.op("ISZERO", 1, "f")
        a.jumpi(noclamp)
        st.s.pop()
        st.pop("pa")
        st.dup("end", "pa")
        st.add_const("off", (-10) % (1 << 256))  # off = start + 290 (coefficient 232)
        a.label(noclamp)
        st.expect(["ret", "end", "off", "tt", "pa"])
        a.jump(loop)
        a.label(done)
        for nm in ("pa", "tt", "off", "end"):
            st.pop(nm)
        a.op("JUMP")

    def gen_csum(self):
        """csum: entry [ret, tt, sp]: SP[t] = 2^13 S'(t) + n_neg(t) (all lanes)
        for t < 256 from the window table at tt and the BASES list."""
        a, L = self.a, self.L
        tau = L.p["tau"]
        a.region("csum")
        a.label("csum")
        st = Stack(a, ["ret", "tt", "sp"])
        # g = n_neg(-1) = number of +1 coefficients; codes: CW = -1 for c = +1
        st.push(L.MISC + 0x1A0, "c")
        st.op("MLOAD", 1, "nn")
        st.push(tau, "c")
        st.op("SUB", 2, "g")             # g = n_neg(-1) = number of +1 coefficients
        st.push(L.CW, "cw")
        st.dup("tt", "bu")                  # bu = tt - 32 u
        loop = self.fresh("csl")
        a.label(loop)
        for m in range(tau):
            st.push(L.BASES + 32 * m, "c")
            st.op("MLOAD", 1, "b")
            st.dup("bu", "bb")
            st.op("ADD", 2, "b")
            st.op("MLOAD", 1, "b")
            if m:
                st.op("ADD", 2, "S")
            else:
                st.rename("b", "S")
        self.transpose16(st, "S")          # cell (r, k) at 64 r + 16 k
        for k in range(4):
            # g += CW[t]  (+1 for c_t = -1, -1 for c_t = +1)
            st.dup("cw", "c")
            if k:
                st.push(32 * k, "o")
                st.op("ADD", 2, "c")
            st.op("MLOAD", 1, "c")
            st.dup("g", "g2")
            st.op("ADD", 2, "gn")
            st.to_top("g")
            st.pop()
            st.rename("gn", "g")
            st.dup("S", "e")
            if k:
                st.push(16 * k, "s")
                st.op("SHR", 2, "e")
            st.push(lanemask(16), "m")
            st.op("AND", 2, "e")
            st.push(13, "s")
            st.op("SHL", 2, "e")
            st.dup("g", "gl")
            st.push(1 | 1 << 64 | 1 << 128 | 1 << 192, "c")
            st.op("MUL", 2, "gl")
            st.op("ADD", 2, "e")
            st.dup("sp", "p")
            if k:
                st.push(32 * k, "o")
                st.op("ADD", 2, "p")
            st.op("MSTORE", 2)
        st.pop("S")
        st.add_const("cw", 128)
        st.add_const("sp", 128)
        st.to_top("bu")
        st.push(32, "c")
        st.swap(1)
        st.op("SUB", 2, "bu")
        st.dup("cw", "x")
        st.push(L.CW + 0x2000, "e")
        st.op("GT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for nm in st.s[::-1][:-1]:
            st.pop(nm)
        a.op("JUMP")

    # ── NTT-domain glue ─────────────────────────────────────────────────
    DIVK = {190464: (39, 2886403), 523776: (42, 8396809)}
    DIVG2 = {95232: (38, 2886403), 261888: (42, 16793617)}   # exact floor(y / g2), y < q + g2

    def gen_usehint(self):
        """usehint: entry [ret, wp] (wp = ACC_g): for the 256 row-packed words
        at wp (lanes < 2^32), W[t] := UseHint(HP[t], (W[t] - 2^13 c*t1[t]) mod q)
        lane-wise, with HP_g and SP_g at fixed offsets from ACC_g."""
        a, L = self.a, self.L
        p = L.p
        g2, m = p["g2"], p["m"]
        K, M = self.DIVK[2 * g2]
        X4 = lambda v: sum(v << (64 * j) for j in range(4))
        a.region("usehint")
        a.label("usehint")
        st = Stack(a, ["ret", "wp"])
        st.dup("wp", "end")
        st.push(0x2000, "c")
        st.op("ADD", 2, "end")
        st.swap(1)                       # [ret, end, wp]; HP and SP move with ACC
        assert L.HP - L.ACC > 0 and L.SP < L.ACC
        loop = self.fresh("uhloop")
        a.label(loop)
        # x = W + 128 q - (2^13 S' + n_neg)   (subtracts c * t1 * 2^d mod q)
        st.push(L.ACC - L.SP, "c")
        st.dup("wp", "e")
        st.op("SUB", 2, "e")
        st.op("MLOAD", 1, "e")
        st.dup("wp", "x")
        st.op("MLOAD", 1, "x")
        st.push(X4(128 * Q), "c")
        st.op("ADD", 2, "x")
        st.op("SUB", 2, "x")
        # r = x mod q: quotient (x * M) >> 53 is exact for x < 4.3e9 (lanes < 2^31 here)
        st.dup("x", "qq")
        st.push(1074791297, "c")
        st.op("MUL", 2, "qq")
        st.push(53, "c")
        st.op("SHR", 2, "qq")
        st.push(lanemask(9), "c")
        st.op("AND", 2, "qq")
        st.push(Q, "c")
        st.op("MUL", 2, "qq")
        st.swap(1)
        st.op("SUB", 2, "r")
        if self.v3:
            # D = (r + g2 - 1) div g2 (exact multiply-shift); r1 = D >> 1 and
            # r0 > 0 iff D is odd, so h * pos = h & D and
            # v = (D >> 1) + m - h + 2 (h & D), in [m - 1, 2m]
            KD, MD = self.DIVG2[g2]
            st.push(X4(g2 - 1), "c")
            st.op("ADD", 2, "D")
            st.push(MD, "c")
            st.op("MUL", 2, "D")
            st.push(KD, "c")
            st.op("SHR", 2, "D")
            st.push(lanemask(7), "c")
            st.op("AND", 2, "D")
            st.dup("wp", "h")
            st.push(L.HP - L.ACC, "c")
            st.op("ADD", 2, "h")
            st.op("MLOAD", 1, "h")       # [D, h]
            st.dup("D", "d2")
            st.dup("h", "h2")
            st.op("AND", 2, "hd")
            st.dup("hd", "hd2")
            st.op("ADD", 2, "hd")        # [D, h, 2 (h & D)]
            st.swap(1)
            st.push(X4(m), "c")
            st.op("SUB", 2, "mh")        # [D, 2hD, m - h]
            st.op("ADD", 2, "t")         # [D, t]
            st.swap(1)
            st.push(1, "c")
            st.op("SHR", 2, "r1")
            st.push(lanemask(6), "c")
            st.op("AND", 2, "r1")
            st.op("ADD", 2, "v")
        else:
            # r1 = (r + g2 - 1) div 2g2
            st.dup("r", "r1")
            st.push(X4(g2 - 1), "c")
            st.op("ADD", 2, "r1")
            st.push(M, "c")
            st.op("MUL", 2, "r1")
            st.push(K, "c")
            st.op("SHR", 2, "r1")
            st.push(lanemask(6), "c")
            st.op("AND", 2, "r1")
            # pos = (r + g2 - r1 2g2) > g2
            st.dup("r1", "e")
            st.push(2 * g2, "c")
            st.op("MUL", 2, "e")
            st.dup("r", "rr")
            st.push(X4(g2), "c")
            st.op("ADD", 2, "rr")
            st.op("SUB", 2, "e")
            st.push(X4((1 << 24) - g2 - 1), "c")
            st.op("ADD", 2, "e")
            st.push(24, "c")
            st.op("SHR", 2, "e")
            st.push(lanemask(1), "c")
            st.op("AND", 2, "pos")
            # h
            st.dup("wp", "h")
            st.push(L.HP - L.ACC, "c")
            st.op("ADD", 2, "h")
            st.op("MLOAD", 1, "h")           # [r, r1, pos, h]
            st.swap(1)
            st.dup("h", "hh")
            st.op("AND", 2, "hpos")          # [r, r1, h, hpos]
            st.push(1, "c")
            st.op("SHL", 2, "hpos")
            st.swap(1)
            st.push(X4(m), "c")
            st.op("SUB", 2, "mh")            # m - h
            st.op("ADD", 2, "v")
            st.op("ADD", 2, "v")             # r1 + m - h + 2 h pos, in [m-1, 2m]
        if m & (m - 1) == 0:
            st.push(X4(m - 1), "c")
            st.op("AND", 2, "v")
        else:
            assert m == 44
            st.dup("v", "qq")
            st.push(94, "c")
            st.op("MUL", 2, "qq")
            st.push(12, "c")
            st.op("SHR", 2, "qq")
            st.push(lanemask(2), "c")
            st.op("AND", 2, "qq")
            st.push(44, "c")
            st.op("MUL", 2, "qq")
            st.swap(1)
            st.op("SUB", 2, "v")
        if not self.v3:
            st.swap(1)
            st.pop()                     # drop r
        st.dup("wp", "p")
        st.op("MSTORE", 2)
        st.add_const("wp", 32)
        st.expect(["ret", "end", "wp"])
        st.dup("end", "e")
        st.dup("wp", "x")
        st.op("LT", 2, "f")              # wp < end
        a.jumpi(loop)
        st.s.pop()
        st.pop("wp")
        st.pop("end")
        a.op("JUMP")

    def gen_pack(self):
        """pack: entry [ret, wp, fp, nrows]: w1Encode the row-packed UseHint
        results at wp; row j's little-endian 64-bit stream lanes go
        (replicated) to fp + 32 (lpr j + i)."""
        a, L = self.a, self.L
        wb = L.p["w1bits"]
        lpr = L.w1lanes // L.k
        CH = 32 if wb == 6 else 16       # coefficients per chunk
        NL = CH * wb // 64               # stream lanes per row per chunk
        a.region("pack")
        a.label("pack")
        st = Stack(a, ["ret", "wp", "fp", "nrows"])
        st.dup("wp", "end")
        st.push(0x2000, "c")
        st.op("ADD", 2, "end")
        st.swap(3)
        st.swap(2)
        st.swap(1)                       # [ret, end, wp, fp, nrows]
        st.expect(["ret", "end", "wp", "fp", "nrows"])
        loop = self.fresh("pkloop")
        a.label(loop)

        def emit(k):
            # lane j of V -> fin row j, chunk lane k; rows >= nrows are skipped
            # (their fp slots belong to the next row group or are unused)
            for j in range(4):
                skip = self.fresh("pks")
                if j:
                    st.push(j, "c")
                    st.dup("nrows", "n")
                    st.op("GT", 2, "f")      # nrows > j
                    st.op("ISZERO", 1, "f")
                    a.jumpi(skip)
                    st.s.pop()
                st.dup("V", "v")
                if j:
                    st.push(64 * j, "c")
                    st.op("SHR", 2, "v")
                if j < 3:
                    st.push(M64, "c")
                    st.op("AND", 2, "v")
                st.push(REP, "c")
                st.op("MUL", 2, "v")
                st.dup("fp", "p")
                off = 32 * (lpr * j + k)
                if off:
                    st.push(off, "c")
                    st.op("ADD", 2, "p")
                st.op("MSTORE", 2)
                a.label(skip)
            st.pop("V")

        st.push(0, "V")
        k = 0
        for tq in range(CH):
            bit = wb * tq
            kk, sh = divmod(bit, 64)
            st.dup("wp", "r")
            if tq:
                st.push(32 * tq, "c")
                st.op("ADD", 2, "r")
            st.op("MLOAD", 1, "r")
            if sh + wb <= 64:
                if sh:
                    st.push(sh, "c")
                    st.op("SHL", 2, "r")
                st.op("OR", 2, "V")
                if sh + wb == 64:
                    emit(k)
                    k += 1
                    if tq < CH - 1:
                        st.push(0, "V")
            else:
                st.dup("r", "r2")
                st.push(sh, "c")
                st.op("SHL", 2, "r2")
                st.push(lanemask(64) ^ lanemask(sh), "c")
                st.op("AND", 2, "r2")    # low part, kept inside each lane
                st.to_top("V") if False else None
                # stack: [.., V, r, r2]
                st.swap(1)               # [.., V, r2, r]
                st.swap(2)               # [.., r, r2, V]
                st.op("OR", 2, "V")      # [.., r, V]
                emit(k)
                k += 1
                st.push(64 - sh, "c")
                st.op("SHR", 2, "V")
                st.push(lanemask(sh + wb - 64), "c")
                st.op("AND", 2, "V")
        assert k == NL
        st.add_const("wp", 32 * CH)
        st.add_const("fp", 32 * NL)
        st.expect(["ret", "end", "wp", "fp", "nrows"])
        st.dup("end", "e")
        st.dup("wp", "x")
        st.op("LT", 2, "f")
        a.jumpi(loop)
        st.s.pop()
        for nm in ("nrows", "fp", "wp", "end"):
            st.pop(nm)
        a.op("JUMP")

    def final_hash(self):
        """[ok] -> [ok & (H(mu || w1Encode) == c-tilde)]."""
        a, L = self.a, self.L
        a.region("final_hash")
        self.zero_ks()
        nl = 8 + L.w1lanes
        full, rem = divmod(nl, 17)
        # stack [ok, src]
        a.push(L.FIN)
        loop = self.fresh("fhloop")
        a.label(loop)
        for i in range(17):
            a.op("DUP1")
            if i:
                a.push(32 * i)
                a.op("ADD")
            a.op("MLOAD")
            a.push(L.KS + 32 * i)
            a.op("MLOAD")
            a.op("XOR")
            a.push(L.KS + 32 * i)
            a.op("MSTORE")
        self.call("kf1")
        a.push(17 * 32)
        a.op("ADD")
        a.op("DUP1")
        a.push(L.FIN + 17 * 32 * full)
        a.op("GT")
        a.jumpi(loop)
        a.op("POP")
        for i in range(rem):
            a.push(L.FIN + 32 * (17 * full + i))
            a.op("MLOAD")
            a.push(L.KS + 32 * i)
            a.op("MLOAD")
            a.op("XOR")
            a.push(L.KS + 32 * i)
            a.op("MSTORE")
        self.xor_ks_const(rem, 0x1F * REP)
        self.xor_ks_const(16, (0x80 << 56) * REP)
        self.call("kf1")
        # compare with c-tilde
        st = Stack(a, ["ok"])
        self.push_consts(st)
        nlanes = L.p["ctb"] // 8
        for u in range((nlanes + 3) // 4):
            n = min(4, nlanes - 4 * u)
            st.push(L.CT + 32 * u, "w")
            st.op("CALLDATALOAD", 1, "w")
            self.bswap64x4(st, "w")
            if n < 4:
                st.push(64 * (4 - n), "s")
                st.op("SHR", 2, "w")
            for i in range(n):
                st.push(L.KS + 32 * (4 * u + i), "p")
                st.op("MLOAD", 1, "l")
                if 4 * u + i in COMPLEMENTED:
                    st.op("NOT", 1, "l")
                st.dup("M64", "m")
                st.op("AND", 2, "l")
                sh = 64 * (n - 1 - i)
                if sh:
                    st.push(sh, "s")
                    st.op("SHL", 2, "l")
                if i:
                    st.op("OR", 2, "P")
                else:
                    st.rename("l", "P")
            st.op("EQ", 2, "e")
            st.dup("ok", "o")
            st.op("AND", 2, "e")
            st.to_top("ok")
            st.pop()
            st.rename("e", "ok")
        self.pop_consts(st)

    R = (1 << 32) % Q

    def ntt_init(self):
        self.nttk.gen_init()

    def gen_ntts(self):
        self.nttk.gen_ntt("ntt")
        self.nttk.premont = True
        self.nttk.gen_intt("intt", self.R)

    P3F_UNROLL = {44: 2, 65: 2, 87: 2}

    def call_dhint(self):
        a = self.a
        ret = self.fresh("ret")
        a.pushl(ret)
        a.jump("dhint")
        a.label(ret)
        a.op("AND")

    def build(self, stop_after=None):
        a, L = self.a, self.L
        self.schedule = self.build_schedule()
        a.region("main")
        # short calldata -> 0
        a.push(L.HDR)
        a.op("CALLDATASIZE")
        a.op("LT")
        a.jumpi("short")
        # touch the top of memory once
        a.op("PUSH0")
        a.push(L.TOP - 32)
        a.op("MSTORE")
        self.init_tables()
        # z (lane-packed by polynomial) with norm flags
        a.op("PUSH0")                    # acc
        for g in range(L.GZ):
            used = sum(M64 << (64 * j) for j in range(4) if 4 * g + j < L.l)
            self.call("dz", [L.Z0 + L.p["zbytes"] * 4 * g, L.ZH + 0x2000 * g])
            a.push(used)
            a.op("AND")
            a.op("OR")
        self.flag_check()
        if not self.v4:
            self.call_dhint()
        if not self.simd_c() and not self.v4:
            ret = self.fresh("ret")
            a.pushl(ret)
            a.jump("sib")
            a.label(ret)
            a.op("AND")                  # [ok]
        self.ntt_init()
        for g in range(L.GZ):
            self.call("ntt", [L.ZH + 0x2000 * g])
        self.init_rho1()
        self.expand_a()
        if self.v4:
            # CW and HP served as side buffers during ExpandA
            self.zero_side_buffers()
            self.call_dhint()
        # mu: squeezed in a SIMD slot for |M| <= 69, else a kf1 sponge from tr
        mulong, mudone = self.fresh("mulong"), self.fresh("mudone")
        if self.has_mu_slot():
            a.push(L.HDR + 70)
            a.op("CALLDATASIZE")
            a.op("LT")
            a.op("ISZERO")
            a.jumpi(mulong)
            for x in range(8):
                a.push(L.MU + 32 * x)
                a.op("MLOAD")
                a.push(REP)
                a.op("MUL")
                a.push(L.FIN + 32 * x)
                a.op("MSTORE")
            a.jump(mudone)
            a.label(mulong)
        for x in range(8):
            a.push(L.TRL + 32 * x)
            a.op("MLOAD")
            a.push(REP)
            a.op("MUL")
            if x in COMPLEMENTED:
                a.op("NOT")
            a.push(L.KS + 32 * x)
            a.op("MSTORE")
        self.hash_mu()
        if self.has_mu_slot():
            a.label(mudone)
        if self.simd_c() or self.v4:
            ret = self.fresh("ret")
            a.pushl(ret)
            a.jump("sib")
            a.label(ret)
            a.op("AND")
        for g in range(L.GR):
            self.call("tbuild", [32 + 320 * 4 * g, L.TT + 0x1800 * g])
            self.call("csum", [L.TT + 0x1800 * g, L.SP + 0x2000 * g])
        lpr = L.w1lanes // L.k
        for g in range(L.GR):
            self.call("intt", [L.ACC + 0x2000 * g])     # Montgomery-reduces ACC at load
            self.call("usehint", [L.ACC + 0x2000 * g])
            self.call("pack", [L.ACC + 0x2000 * g, L.FIN + 32 * (8 + lpr * 4 * g), min(4, L.k - 4 * g)])
        self.final_hash()
        a.op("PUSH0")
        a.op("MSTORE")
        a.push(32)
        a.op("PUSH0")
        a.op("RETURN")
        a.label("short")
        a.op("PUSH0")
        a.op("PUSH0")
        a.op("MSTORE")
        a.push(32)
        a.op("PUSH0")
        a.op("RETURN")
        self.gen_absorb17()
        self.gen_sample_in_ball()
        self.gen_decode_hint()
        self.gen_decode("dz", L.p["zbytes"], L.p["zbits"], self.z_post, flags=True)
        self.gen_blk()
        if self.v4:
            for name, rb, first, bufs in self.fused:
                self.gen_pass3f(name, rb, first, bufs, self.P3F_UNROLL[L.nn])
        else:
            self.gen_pass3()
            if any(g['p3'][0] == 'masked' for g in self.schedule):
                self.gen_pass3(masked=True)
            for gi, g in enumerate(self.schedule):
                if g['p3'][0] == 'kron':
                    self.gen_pass3k(f"pass3k{gi}", *g['p3'][1:])
                elif g['p3'][0] == 'mix':
                    self.gen_pass3x(f"pass3x{gi}", *g['p3'][1:])
        self.gen_gfix()
        self.gen_ginit()
        self.gen_trabs()
        self.gen_cext()
        self.gen_spr()
        if self.has_mu_slot():
            self.gen_mu0()
        self.gen_fix()
        self.gen_group()
        self.gen_tbuild()
        self.gen_csum()
        self.gen_usehint()
        self.gen_pack()
        self.gen_ntts()
        gen_keccak_f(a, "kf1", L.KS, L.KB, L.RC1, unroll=2, scale=1, kz_addr=L.KZ if self.v3 else None)
        gen_keccak_f(a, "kf4", L.KS, L.KB, L.RC4, unroll=2, scale=4)
        return a.assemble()


def layout_text(g, code):
    L = g.L
    out = [f"ML-DSA-{L.nn} optimised verifier: {len(code)} bytes (limit 24576)", "",
           "Subroutines / regions (pc ranges of the generated code):"]
    rp = g.a.region_pcs + [(len(code), "END")]
    for (p, n), (q, _) in zip(rp, rp[1:]):
        out.append(f"  {p:6d} .. {q:6d}  {q - p:5d} bytes  {n}")
    out += ["", "Memory map (byte offsets):"]
    for name, addr, size in L.regions:
        out.append(f"  {name:6s} {addr:#08x} .. {addr + size:#08x}  ({size} bytes)")
    out.append(f"  TT     {L.TT:#08x} (overlays ABUF/FL/ZH after ExpandA)")
    out.append(f"  SP     {L.SP:#08x} (overlays ABUF/FL/ZH after ExpandA)")
    out.append(f"  top    {L.TOP:#08x} (touched once at entry)")
    out += ["", "SIMD groups (slot roles; each group squeezes 5 blocks of 4 states):"]
    for i, gr in enumerate(g.schedule):
        out.append(f"  {i:2d}: slots={gr['slots']} keep={gr['keep']} acc={gr['p3']}")
    return "\n".join(out) + "\n"


def main(argv):
    """gen_opt.py [--version v2|v3|v4] [--out DIR] [44|65|87 ...]

    v2 = the formally verified artifacts (MlDsaOptNN/Bytecode.lean), written to
    MlDsaOpt/NN/v2/ by default; v3 = the current proved design, written to
    MlDsaOpt/NN/; v4 = round 4 (not yet proved), written to MlDsaOpt/NN/v4/.
    --out DIR writes DIR/NN/ instead."""
    version, out, sets = DEFAULT_VERSION, None, []
    it = iter(argv)
    for x in it:
        if x == "--version":
            version = next(it)
        elif x == "--out":
            out = next(it)
        else:
            sets.append(int(x))
    sets = sets or [44, 65, 87]
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "MlDsaOpt")
    for nn in sets:
        L = Layout(nn, version)
        g = Gen(L)
        code = g.build()
        assert len(code) <= 24576, f"{nn}: {len(code)} bytes exceeds EIP-170"
        if out is not None:
            d = os.path.join(out, str(nn))
        elif version in ("v2", "v4"):
            d = os.path.join(root, str(nn), version)
        else:
            d = os.path.join(root, str(nn))
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "opt.hex"), "w") as f:
            f.write(code.hex() + "\n")
        with open(os.path.join(d, "opt.asm"), "w") as f:
            f.write(f"; GENERATED by scripts/gen_opt.py --version {version} {nn}; do not edit.\n")
            f.write(g.a.listing())
        with open(os.path.join(d, "layout.txt"), "w") as f:
            f.write(layout_text(g, code))
        print(nn, version, len(code), "bytes", d)


if __name__ == "__main__":
    main(sys.argv[1:])
