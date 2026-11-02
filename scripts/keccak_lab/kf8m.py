"""kf8m: eight Keccak-f[1600] states per call, rotations through memory.

Layout. Lane i of state s is split into its even and odd bits (32 each).
Word (i, h) holds bit 2b + h of lane i of state s at bit 8b + s, so every
byte of a word is one bit position of all eight states. 50 words hold the
eight states.

Rotation by memory. Every word W is stored twice, at a and a + 32. Then
MLOAD(a + k) = rotl256(W, 8k) for 0 <= k <= 32, a byte rotation, which is a
32-bit rotation by k of each state's half-lane. A 64-bit lane rotation by
n = 2m is a rotation of both halves by m; n = 2m + 1 rotates the odd half by
m + 1 into the even half and the even half by m into the odd half. So rho
costs one MLOAD at an offset address, and only the duplicate store is extra
(DUP1 PUSH MSTORE PUSH MSTORE = 15 instead of PUSH MSTORE = 6).

Theta. rho rotates A ^ D, so D[x] (10 words) is also stored twice and read
at the same offset as the lane it is applied to: B = MLOAD(A + k) ^
MLOAD(D + k + f). D[x] = C[x-1] ^ rotl64(C[x+1], 1) needs a rotation of the
odd half of C[x+1] by one byte. Instead of rotating C, each D word is stored
in a frame f (stored value = rotr(D, 8f)) and each column parity C is
computed in a frame by reading its five lanes at offset -c: the frame
equations around the 5-cycle of D/C dependencies close up to one byte, so
one physical rotation per round remains (instead of five). `FRAMES` gives
the frames; the generator inserts a shift rotation wherever a term's frame
does not match.

Chi, lane complementing and iota are those of opt_keccak (per half).

Interface. The state lives at `st` in the duplicated layout: word (i, h) at
st + 64 (2i + h) and again at st + 64 (2i + h) + 32. Callers that write the
state (absorption) must write both copies; readers read the first.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from opt_asm import Asm, Stack  # noqa: E402
from opt_keccak import CHI, COMPLEMENTED, rot_top  # noqa: E402
from opt_ref import ROT, RC  # noqa: E402

import lab  # noqa: E402

# D frames: PHI[x] for D[x] even half, PSI[x] for odd half (bytes). The
# derivation (module docstring): C[x][0] in frame PHI[x+1] = PSI[x-1],
# C[x][1] in frame PSI[x+1] = PHI[x-1] - 1. PHI[y] = y satisfies all but one
# of these (C[1][1] for D[0][0]), which costs one rotation.
PHI = [0, 1, 2, 3, 4]
PSI = [PHI[(x + 2) % 5] for x in range(5)]


def waddr(buf, i, h):
    return buf + 64 * (2 * i + h)


def rho_src(s, ho):
    """Output half ho of rotl64(lane s, ROT[s]) = rotl32(half h, k): (h, k)."""
    n = ROT[s]
    if n % 2 == 0:
        return ho, n // 2
    return (1, n // 2 + 1) if ho == 0 else (0, n // 2)


def rc8(rc):
    """iota constant -> (even word, odd word), each bit spread to all 8 slots."""
    e, o = lab.halves(rc)
    return lab.spread_stride(e, 32, 8) * 0xFF, lab.spread_stride(o, 32, 8) * 0xFF


def store2(st: Stack, addr):
    """Store the top word at addr and addr + 32, consuming it."""
    st.dup(st.top(), "c")
    st.push(addr, "a")
    st.op("MSTORE", 2)
    st.push(addr + 32, "a")
    st.op("MSTORE", 2)


def theta8(st: Stack, src, dbuf, phi=PHI, psi=PSI, cframes=None, stats=None):
    """Compute D (10 words, duplicated, in frames phi/psi) into dbuf."""
    fD = {(x, 0): phi[x] % 32 for x in range(5)}
    fD.update({(x, 1): psi[x] % 32 for x in range(5)})
    # terms: D[x][0] = C[x-1][0] (frame f) ^ C[x+1][1] (frame f - 1)
    #        D[x][1] = C[x-1][1] (frame f) ^ C[x+1][0] (frame f)
    terms = {}
    for x in range(5):
        f0, f1 = fD[(x, 0)], fD[(x, 1)]
        terms[(x, 0)] = [((x - 1) % 5, 0, f0), ((x + 1) % 5, 1, (f0 - 1) % 32)]
        terms[(x, 1)] = [((x - 1) % 5, 1, f1), ((x + 1) % 5, 0, f1)]
    if cframes is None:
        # majority frame per C
        cframes = {}
        for x in range(5):
            for h in range(2):
                fs = [f for t in terms.values() for (cx, ch, f) in t if (cx, ch) == (x, h)]
                cframes[(x, h)] = max(set(fs), key=fs.count)
    for x in range(5):
        for h in range(2):
            j = (-cframes[(x, h)]) % 32
            for y in range(5):
                st.push(waddr(src, x + 5 * y, h) + j, "a")
                st.op("MLOAD", 1, "t" if y else f"C{x}{h}")
                if y:
                    st.op("XOR", 2, f"C{x}{h}")
    uses = {}
    for t in terms.values():
        for cx, ch, _ in t:
            uses[(cx, ch)] = uses.get((cx, ch), 0) + 1
    nrot = 0
    ndead = 0

    def plan(k, order):
        """Ops for D word k with operand order; None if impossible."""
        (x1, h1, f1), (x2, h2, f2) = [terms[k][i] for i in order]
        if cframes[(x2, h2)] != f2:
            return None          # the rotated operand must come first
        n1, n2 = f"C{x1}{h1}", f"C{x2}{h2}"
        last1, last2 = uses[(x1, h1)] == 1, uses[(x2, h2)] == 1
        s = list(st.s)
        cost = 0
        if last1:
            i = len(s) - 1 - s[::-1].index(n1)
            if i != len(s) - 1:
                cost += 1
                s[i], s[-1] = s[-1], s[i]
            s[-1] = "t"
        else:
            cost += 1
            s.append("t")
        d2 = len(s) - 1 - (len(s) - 1 - s[::-1].index(n2))
        if last2 and d2 == 1:
            mode2 = "inplace"
        elif last2:
            mode2, cost = "dupdead", cost + 2
        else:
            mode2, cost = "dup", cost + 1
        return cost, mode2

    todo = list(terms)
    while todo:
        best = None
        for k in todo:
            for order in ((0, 1), (1, 0)):
                p = plan(k, order)
                if p and (best is None or p[0] < best[0]):
                    best = (p[0], k, order, p[1])
        _, k, order, mode2 = best
        todo.remove(k)
        (x1, h1, f1), (x2, h2, f2) = [terms[k][i] for i in order]
        n1, n2 = f"C{x1}{h1}", f"C{x2}{h2}"
        uses[(x1, h1)] -= 1
        uses[(x2, h2)] -= 1
        if uses[(x1, h1)]:
            st.dup(n1, "t")
        else:
            st.to_top(n1)
            st.rename(n1, "t")
        a = cframes[(x1, h1)]
        if a != f1:
            rot_top(st, 8 * ((a - f1) % 32), "t")
            nrot += 1
        if mode2 == "inplace":
            assert st.s[-2] == n2, (st.s, n2)
        else:
            st.dup(n2, "u")
            if mode2 == "dupdead":
                st.rename(n2, "dead")
                ndead += 1
        st.op("XOR", 2, "D")
        store2(st, waddr(dbuf, *k))
    for _ in range(ndead):
        st.pop("dead")
    if stats is not None:
        stats["theta_rot"] = nrot
        stats["theta_dead"] = ndead
    return fD


def round8(st: Stack, src, dst, dbuf, rc_get, stats=None, frames=(PHI, PSI)):
    """One round: lanes at src (duplicated layout) -> dst (duplicated)."""
    base = len(st.s)
    fD = theta8(st, src, dbuf, frames[0], frames[1], stats=stats)
    for yo in range(5):
        for ho in range(2):
            for xo in (4, 1, 0, 3, 2):       # B4 deepest, B2 on top
                sx, sy = (xo + 3 * yo) % 5, xo
                s = sx + 5 * sy
                h, k = rho_src(s, ho)
                st.push(waddr(src, s, h) + k, "a")
                st.op("MLOAD", 1, "m")
                st.push(waddr(dbuf, sx, h) + (k + fD[(sx, h)]) % 32, "a")
                st.op("MLOAD", 1, "d")
                st.op("XOR", 2, f"B{xo}")
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
                    rc_get(st, ho)
                    st.op("XOR", 2, "o")
                store2(st, waddr(dst, xo + 5 * yo, ho))
    assert len(st.s) == base, st.s


def gen_kf8m(a: Asm, name, st_addr, bt_addr, d_addr, rct=None, unrolled=False, stats=None, unroll=2,
             frames=(PHI, PSI)):
    """Subroutine `name`: Keccak-f on 8 states at st_addr (duplicated layout).

    Looped (Osaka): `unroll` rounds per iteration alternating st -> bt -> st,
    iota from the 48-word table at rct (even, odd word per round).
    unrolled: 24 straight-line rounds, iota as PUSH immediates."""
    a.region(name)
    a.label(name)
    st = Stack(a, ["ret"])
    if unrolled:
        for r in range(24):
            src, dst = (st_addr, bt_addr) if r % 2 == 0 else (bt_addr, st_addr)
            ev, od = rc8(RC[r])

            def rc_get(st, ho, ev=ev, od=od):
                st.push(ev if ho == 0 else od, "rc")
            round8(st, src, dst, d_addr, rc_get, stats, frames)
        st.a.op("JUMP")
        return
    assert unroll % 2 == 0 and 24 % unroll == 0
    st.push(rct, "rp")
    a.label(name + "_loop")
    for r in range(unroll):
        src, dst = (st_addr, bt_addr) if r % 2 == 0 else (bt_addr, st_addr)

        def rc_get(st, ho, r=r):
            off = 32 * (2 * r + ho)
            st.dup("rp", "p")
            if off:
                st.push(off, "o")
                st.op("ADD", 2, "p")
            st.op("MLOAD", 1, "rc")
        round8(st, src, dst, d_addr, rc_get, stats, frames)
    st.add_const("rp", 64 * unroll)
    st.dup("rp", "c")
    a.push(rct + 32 * 48)
    st.s.append("end")
    st.op("GT", 2, "lt")
    a.jumpi(name + "_loop")
    st.s.pop()
    st.pop("rp")
    a.op("JUMP")


def rc_table8():
    out = []
    for rc in RC:
        out += list(rc8(rc))
    return out


class Layout8:
    """Duplicated 8-way layout at ST; buffers BT, DB; iota table RCT."""
    n = 8
    ST, BT, DB, RCT = 0x0000, 0x0C80, 0x1900, 0x1B80
    mem_size = 0x1B80 + 48 * 32

    def encode(self, states):
        out = {}
        for i in range(25):
            hs = [lab.halves(s[i]) for s in states]
            for h in range(2):
                w = lab.interleave8([v[h] for v in hs])
                if i in COMPLEMENTED:
                    w ^= lab.M256
                out[waddr(self.ST, i, h)] = w
                out[waddr(self.ST, i, h) + 32] = w
        return out

    def setup(self, mem):
        for i, v in enumerate(rc_table8()):
            mem[self.RCT + 32 * i:self.RCT + 32 * i + 32] = v.to_bytes(32, "big")

    def decode(self, mem):
        res = [[0] * 25 for _ in range(8)]
        for i in range(25):
            ws = []
            for h in range(2):
                a = waddr(self.ST, i, h)
                w = int.from_bytes(mem[a:a + 32], "big")
                assert w == int.from_bytes(mem[a + 32:a + 64], "big"), "copies differ"
                if i in COMPLEMENTED:
                    w ^= lab.M256
                ws.append(lab.deinterleave8(w))
            for s in range(8):
                res[s][i] = lab.unhalves(ws[0][s], ws[1][s])
        return res


if __name__ == "__main__":
    L = Layout8()
    for unrolled, unroll in ((False, 2), (False, 4), (False, 6), (True, 24)):
        stats = {}
        g, sz, n = lab.check(lambda a: gen_kf8m(a, "kf", L.ST, L.BT, L.DB, L.RCT, unrolled, stats, unroll), L)
        print(f"kf8m {unroll:2d} rounds/iter{' (no loop, immediate iota)' if unrolled else ''}: {g:,} gas/call, "
              f"{g / 8:,.0f}/state, {sz:,} B, {n} KAT calls ok, theta rotations/round {stats['theta_rot']}")
    stats = {}
    g, sz, n = lab.check(lambda a: gen_kf8m(a, "kf", L.ST, L.BT, L.DB, L.RCT, False, stats, 2,
                                            ([0] * 5, [0] * 5)), L)
    print(f"kf8m  2 rounds/iter, no D frames: {g:,} gas/call, {g / 8:,.0f}/state, {sz:,} B, {n} KAT calls ok, "
          f"theta rotations/round {stats['theta_rot']}")
