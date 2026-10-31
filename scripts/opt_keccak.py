"""Keccak-f[1600] kernels for the optimised verifier (bytecode generators).

Representation: 4-way bit-interleaved SIMD. A state word holds lane (x, y)
of four independent Keccak states ("slots"): bit b of slot k sits at bit
4b + k. Bitwise operations act on all slots at once and a 64-bit rotation by
n of every slot is a 256-bit rotation by 4n, so one permutation of 25 words
permutes four states. Lanes listed in COMPLEMENTED are kept inverted in
memory (lane-complementing transform), so callers must initialise them to
all-ones and invert them when reading output. With `scale = 1` the same code implements the
replicated single-state representation: a word holds lane x as x||x||x||x.
There every rotation is a single shift by d = n or n - 64 ("decaying
window"): the result equals the replicated rotated lane on the input's valid
bit window shifted by d, and bitwise operations intersect windows. Starting
from fully replicated lanes, two rounds leave every lane valid on at least
bits [58, 200) (checked by `decay_windows`), so the second round of each loop
iteration re-replicates bits [64, 128) before storing.

The permutation keeps the state in memory at fixed addresses (25 words at
`st`, a second 25-word buffer at `bt`; rounds alternate between them) and the
24 iota constants (interleaved, i.e. spread to all four slots) in a memory
table at `rct`. The round body is straight-line code generated here with
explicit stack scheduling; `unroll` rounds per loop iteration.
"""
from __future__ import annotations

from opt_asm import Asm, Stack
from opt_ref import ROT, RC, interleave

ALL = (1 << 256) - 1

# Lane complementing (Keccak implementation overview, sec. 2.2): lanes in
# COMPLEMENTED are stored inverted between rounds; chi then needs one NOT per
# plane. CHI[y][x] = (op, NOT operand B[x+1], NOT operand B[x+2], NOT output)
# for out[x] = B[x] ^ op(B[x+1], B[x+2]).
COMPLEMENTED = [1, 2, 8, 12, 17, 20]     # lane index x + 5y
CHI = [
    [("OR", 0, 0, 0), ("OR", 1, 0, 0), ("AND", 0, 0, 0), ("OR", 0, 0, 0), ("AND", 0, 0, 0)],
    [("OR", 0, 0, 0), ("AND", 0, 0, 0), ("OR", 0, 1, 0), ("OR", 0, 0, 0), ("AND", 0, 0, 0)],
    [("OR", 0, 0, 0), ("AND", 0, 0, 0), ("AND", 1, 0, 0), ("OR", 0, 0, 1), ("AND", 0, 0, 0)],
    [("AND", 0, 0, 0), ("OR", 0, 0, 0), ("OR", 1, 0, 0), ("AND", 0, 0, 1), ("OR", 0, 0, 0)],
    [("AND", 1, 0, 0), ("OR", 0, 0, 1), ("AND", 0, 0, 0), ("OR", 0, 0, 0), ("AND", 0, 0, 0)],
]


def rot_top(st: Stack, n4: int, name: str, decay: bool = False):
    """Rotate the top word left by n4 bits (256-bit rotation), consuming it.

    decay (replicated representation only): a single shift by d = n4 or
    n4 - 64 (|d| <= 32); the result is only valid on the input's valid bit
    window shifted by d (see gen_keccak_f)."""
    if decay and n4 % 64:
        d = n4 if n4 <= 32 else n4 - 64
        st.a.push(abs(d))
        st.a.op("SHL" if d > 0 else "SHR")
        st.rename(st.top(), name)
        return
    if n4 % 256 == 0:
        st.rename(st.top(), name)
        return
    a = st.a
    a.op("DUP1")
    a.push(n4)
    a.op("SHL")
    a.op("SWAP1")
    a.push(256 - n4)
    a.op("SHR")
    a.op("OR")
    st.rename(st.top(), name)


def round_body(st: Stack, src: int, dst: int, rc_name: str, rc_off: int, scale: int = 4,
               decay: bool = False, rerep: bool = False):
    """One Keccak round reading lanes at `src`, writing at `dst`.

    The iota constant is mload(rc_name + rc_off) where rc_name is a stack
    value (the round-constant table pointer).
    """
    a = st.a
    base = len(st.s)
    # theta: column parities C0..C4
    for x in range(5):
        a.push(src + 32 * x)
        a.op("MLOAD")
        for y in range(1, 5):
            a.push(src + 32 * (x + 5 * y))
            a.op("MLOAD")
            a.op("XOR")
        st.s.append(f"C{x}")
    # D[x] = C[x-1] ^ rot1(C[x+1]): every C is copied once and consumed once
    # 1. D3 = C2 ^ R4
    st.dup("C4", "t")
    rot_top(st, scale, "t", decay)
    st.dup("C2", "u")
    st.op("XOR", 2, "D3")
    # 2. D0 = C4 ^ R1 (C4 consumed)
    st.to_top("C4")
    st.dup("C1", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D0")
    # 3. D2 = C1 ^ R3 (C1 consumed)
    st.to_top("C1")
    st.dup("C3", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D2")
    # 4. D4 = C3 ^ R0 (C3 consumed)
    st.to_top("C3")
    st.dup("C0", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D4")
    # 5. D1 = C0 ^ R2 (both consumed): bring C0 then C2 to the top
    st.to_top("C0")
    st.swap(1)
    st.to_top("C2")
    assert st.s[-2] == "C0", st.s
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D1")
    assert sorted(st.s[base:]) == [f"D{x}" for x in range(5)]
    # rho, pi, chi, one output row at a time (lane-complementing chi)
    for yo in range(5):
        for xo in (4, 1, 0, 3, 2):       # B4 deepest, B2 on top
            sx, sy = (xo + 3 * yo) % 5, xo
            s = sx + 5 * sy
            a.push(src + 32 * s)
            a.op("MLOAD")
            st.s.append("m")
            st.dup(f"D{sx}", "d")
            st.op("XOR", 2, "v")
            rot_top(st, scale * ROT[s], f"B{xo}", decay)
        for xo in range(5):
            op, n1, n2, nout = CHI[yo][xo]
            b0, b1, b2 = f"B{xo}", f"B{(xo + 1) % 5}", f"B{(xo + 2) % 5}"
            if xo == 4:
                # stack [.., B4, B1, B0]: consume B0, B1, then B4
                assert st.s[-3:] == ["B4", "B1", "B0"], st.s
                assert not n1 and not n2
                st.op(op, 2, "f")
                st.op("XOR", 2, "o")
            else:
                st.dup(b1, "f1")
                if n1:
                    st.op("NOT", 1, "f1")
                st.dup(b2, "f2")
                if n2:
                    st.op("NOT", 1, "f2")
                st.op(op, 2, "f")
                if xo in (2, 3):
                    assert st.s[-2] == b0, st.s   # B2 / B3 consumed in place
                else:
                    st.dup(b0, "b")
                st.op("XOR", 2, "o")
            if nout:
                st.op("NOT", 1, "o")
            if yo == 0 and xo == 0:
                st.dup(rc_name, "rp")
                if rc_off:
                    st.push(rc_off, "off")
                    st.op("ADD", 2, "rp")
                st.op("MLOAD", 1, "rc")
                st.op("XOR", 2, "o")
            if rerep:
                # valid window contains bits [64, 128): replicate that block
                st.push(64, "c")
                st.op("SHR", 2, "o")
                st.dup("M64", "m")
                st.op("AND", 2, "o")
                st.dup("REP", "r")
                st.op("MUL", 2, "o")
            a.push(dst + 32 * (xo + 5 * yo))
            st.s.append("addr")
            st.op("MSTORE", 2)
    assert len(st.s) == base + 5, st.s
    for _ in range(5):
        st.pop()


def gen_keccak_f(a: Asm, name: str, st_addr: int, bt_addr: int, rct: int, unroll: int = 2, scale: int = 4):
    """Subroutine `name`: Keccak-f on the 25 interleaved words at st_addr.

    Entry stack: [ret]. Clobbers bt_addr..bt_addr+800. Exit: jumps to ret.
    """
    assert 24 % unroll == 0 and unroll % 2 == 0
    a.region(name)
    a.label(name)
    st = Stack(a, ["ret"])
    st.push(rct, "rp")
    decay = scale == 1
    if decay:
        assert unroll == 2
        st.push((1 << 64) - 1, "M64")
        st.push(REP, "REP")
    a.label(name + "_loop")
    for r in range(unroll):
        src, dst = (st_addr, bt_addr) if r % 2 == 0 else (bt_addr, st_addr)
        round_body(st, src, dst, "rp", 32 * r, scale, decay=decay, rerep=decay and r % 2 == 1)
    st.add_const("rp", 32 * unroll)
    st.dup("rp", "c")
    a.push(rct + 32 * 24)
    st.s.append("end")
    st.op("GT", 2, "lt")      # end > rp
    a.jumpi(name + "_loop")
    st.s.pop()
    if decay:
        st.pop("REP")
        st.pop("M64")
    st.pop("rp")
    a.op("JUMP")


REP = 1 | 1 << 64 | 1 << 128 | 1 << 192


def decay_windows():
    """Valid bit windows of all lanes after two decay rounds from full windows."""
    def inter(ws):
        return max(w[0] for w in ws), min(w[1] for w in ws)

    def sh(w, d):
        return max(0, w[0] + d), min(256, w[1] + d)

    win = [(0, 256)] * 25
    for _ in range(2):
        C = [inter([win[x + 5 * y] for y in range(5)]) for x in range(5)]
        D = [inter([C[(x - 1) % 5], sh(C[(x + 1) % 5], 1)]) for x in range(5)]
        A = [inter([win[i], D[i % 5]]) for i in range(25)]
        B = [None] * 25
        for x in range(5):
            for y in range(5):
                r = ROT[x + 5 * y]
                B[y + 5 * ((2 * x + 3 * y) % 5)] = sh(A[x + 5 * y], r if r <= 32 else r - 64)
        win = [inter([B[5 * (i // 5) + k] for k in range(5)]) for i in range(25)]
    return win


assert all(lo <= 64 and hi >= 128 for lo, hi in decay_windows())


def rc_table(scale=4):
    """iota constants: interleaved to all four slots (scale 4) or replicated
    four times (scale 1, single-sponge representation x||x||x||x)."""
    if scale == 4:
        return [interleave([v] * 4) for v in RC]
    return [v * REP for v in RC]
