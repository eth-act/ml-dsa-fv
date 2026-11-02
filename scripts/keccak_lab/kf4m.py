"""kf4m: the v3/v4 4-way kf4 with memory rotations where they are byte
rotations.

Same layout and interface as kf4 (bit b of slot k at 4b + k), except that
the 25 words sit at stride 64 so that a word can be stored twice. A 64-bit
rotation by n is a 256-bit rotation by 4n bits, a byte rotation when n is
even: 12 of the 24 rotated lanes (ROT = 62, 28, 36, 44, 6, 20, 10, 8, 18,
2, 56, 14). For those lanes the chi output is stored twice and rho reads
MLOAD(A + n/2) ^ MLOAD(D + n/2); D[x] (5 words) is also stored twice and
kept on the stack for the other lanes. Odd lanes, theta and chi are
unchanged (opt_keccak.round_body).
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from opt_asm import Asm, Stack  # noqa: E402
from opt_keccak import CHI, COMPLEMENTED, rc_table, rot_top  # noqa: E402
from opt_ref import ROT  # noqa: E402
import opt_ref  # noqa: E402

import lab  # noqa: E402

MEMROT = [i for i in range(25) if ROT[i] and ROT[i] % 2 == 0]


def wa(buf, i):
    return buf + 64 * i


def round4m(st: Stack, src, dst, dbuf, rc_name, rc_off):
    a = st.a
    base = len(st.s)
    for x in range(5):
        a.push(wa(src, x))
        a.op("MLOAD")
        for y in range(1, 5):
            a.push(wa(src, x + 5 * y))
            a.op("MLOAD")
            a.op("XOR")
        st.s.append(f"C{x}")
    # theta schedule of opt_keccak.round_body
    st.dup("C4", "t")
    rot_top(st, 4, "t")
    st.dup("C2", "u")
    st.op("XOR", 2, "D3")
    st.to_top("C4")
    st.dup("C1", "t")
    rot_top(st, 4, "t")
    st.op("XOR", 2, "D0")
    st.to_top("C1")
    st.dup("C3", "t")
    rot_top(st, 4, "t")
    st.op("XOR", 2, "D2")
    st.to_top("C3")
    st.dup("C0", "t")
    rot_top(st, 4, "t")
    st.op("XOR", 2, "D4")
    st.to_top("C0")
    st.swap(1)
    st.to_top("C2")
    rot_top(st, 4, "t")
    st.op("XOR", 2, "D1")
    for x in range(5):
        if any(s % 5 == x for s in MEMROT):
            for off in (0, 32):
                st.dup(f"D{x}", "c")
                st.push(wa(dbuf, x) + off, "a")
                st.op("MSTORE", 2)
    for yo in range(5):
        for xo in (4, 1, 0, 3, 2):
            sx, sy = (xo + 3 * yo) % 5, xo
            s = sx + 5 * sy
            n = ROT[s]
            if s in MEMROT:
                st.push(wa(src, s) + n // 2, "a")
                st.op("MLOAD", 1, "m")
                st.push(wa(dbuf, sx) + n // 2, "a")
                st.op("MLOAD", 1, "d")
                st.op("XOR", 2, f"B{xo}")
            else:
                st.push(wa(src, s), "a")
                st.op("MLOAD", 1, "m")
                st.dup(f"D{sx}", "d")
                st.op("XOR", 2, "v")
                rot_top(st, 4 * n, f"B{xo}")
        for xo in range(5):
            op, n1, n2, nout = CHI[yo][xo]
            b1, b2 = f"B{(xo + 1) % 5}", f"B{(xo + 2) % 5}"
            if xo == 4:
                assert st.s[-3:] == ["B4", "B1", "B0"], st.s
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
                    assert st.s[-2] == f"B{xo}", st.s
                else:
                    st.dup(f"B{xo}", "b")
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
            i = xo + 5 * yo
            if i in MEMROT:
                st.dup("o", "c")
                st.push(wa(dst, i) + 32, "a")
                st.op("MSTORE", 2)
            st.push(wa(dst, i), "a")
            st.op("MSTORE", 2)
    assert len(st.s) == base + 5, st.s
    for _ in range(5):
        st.pop()


def gen_kf4m(a: Asm, name, st_addr, bt_addr, d_addr, rct):
    a.region(name)
    a.label(name)
    st = Stack(a, ["ret"])
    st.push(rct, "rp")
    a.label(name + "_loop")
    for r, (src, dst) in enumerate(((st_addr, bt_addr), (bt_addr, st_addr))):
        round4m(st, src, dst, d_addr, "rp", 32 * r)
    st.add_const("rp", 64)
    st.dup("rp", "c")
    a.push(rct + 32 * 24)
    st.s.append("end")
    st.op("GT", 2, "lt")
    a.jumpi(name + "_loop")
    st.s.pop()
    st.pop("rp")
    a.op("JUMP")


class Layout4m:
    n = 4
    ST, BT, DB, RCT = 0, 0x640, 0xC80, 0xE00
    mem_size = 0xE00 + 24 * 32

    def encode(self, states):
        out = {}
        for i in range(25):
            w = opt_ref.interleave([s[i] for s in states]) ^ (lab.M256 if i in COMPLEMENTED else 0)
            out[wa(self.ST, i)] = w
            if i in MEMROT:
                out[wa(self.ST, i) + 32] = w
        return out

    def setup(self, mem):
        for i, v in enumerate(rc_table(4)):
            mem[self.RCT + 32 * i:self.RCT + 32 * i + 32] = v.to_bytes(32, "big")

    def decode(self, mem):
        lanes = [int.from_bytes(mem[wa(self.ST, i):wa(self.ST, i) + 32], "big")
                 ^ (lab.M256 if i in COMPLEMENTED else 0) for i in range(25)]
        d = [opt_ref.deinterleave(w) for w in lanes]
        return [[d[i][k] for i in range(25)] for k in range(4)]


if __name__ == "__main__":
    L = Layout4m()
    g, sz, n = lab.check(lambda a: gen_kf4m(a, "kf", L.ST, L.BT, L.DB, L.RCT), L)
    print(f"kf4m: {g:,} gas/call, {g / 4:,.0f}/state, {sz:,} B, {n} KAT calls ok")
