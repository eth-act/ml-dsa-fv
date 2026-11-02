"""Stack-resident Keccak-f[1600] kernels for Glamsterdam (EIP-8024).

Same representations as `opt_keccak.py` (scale 4: four states, bit-interleaved;
scale 1: one state replicated x||x||x||x with v3's decaying windows, offset
-1 and re-replication of bits [192, 256) every third round), same lane
complementing and the same memory interface: the 25 words at `st_addr` in,
Keccak-f of them out. Nothing else in memory is read or written (no round
buffers, no iota table).

What changes is where the state lives between rounds. With EIP-8024's DUPN /
SWAPN (3 gas, any depth up to 235) the 25 lanes stay on the stack:

* entry: 25 MLOADs; exit: the last round MSTOREs its outputs directly;
* theta's column parities read lanes with DUPN instead of PUSH + MLOAD;
* rho/pi fetch a lane with a SWAPN that parks a value in its slot (a chi
  output, or a B until its last use): 8 SWAPNs per plane load 5 lanes and
  store 5 outputs, with no POPs (round_stack);
* all 24 rounds are unrolled (EIP-7954 allows 64 KiB of code), so iota is a
  PUSH immediate and there is no loop overhead.

The stack layout of the lanes is a different permutation after every round;
the generator tracks it by name (opt_asm.Stack with deep=True), so no code is
spent restoring a fixed layout.
"""
from __future__ import annotations

from opt_asm import Asm, Stack
from opt_keccak import CHI, REP, rc_table, rot_top
from opt_ref import ROT


def theta(st: Stack, scale, decay):
    """Push C0..C4 from the lanes L0..L24, then turn them into D0..D4
    (the scheduling of opt_keccak.round_body)."""
    for x in range(5):
        st.dup(f"L{x}", f"C{x}")
        for y in range(1, 5):
            st.dup(f"L{x + 5 * y}", "t")
            st.op("XOR", 2, f"C{x}")
    st.dup("C4", "t")
    rot_top(st, scale, "t", decay)
    st.dup("C2", "u")
    st.op("XOR", 2, "D3")
    st.to_top("C4")
    st.dup("C1", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D0")
    st.to_top("C1")
    st.dup("C3", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D2")
    st.to_top("C3")
    st.dup("C0", "t")
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D4")
    st.to_top("C0")
    st.swap(1)
    st.to_top("C2")
    assert st.s[-2] == "C0", st.s
    rot_top(st, scale, "t", decay)
    st.op("XOR", 2, "D1")
    # D0 below D4: the last plane's first four lanes then meet D2, D3, D4, D0
    # right below them and consume them (see round_stack)
    assert st.s[-5:] == ["D4", "D0", "D3", "D2", "D1"], st.s
    st.a.exchange(3, 4)
    st.s[-5], st.s[-4] = "D0", "D4"


def round_stack(st: Stack, rc: int, scale: int, decay, rerep: bool, out_addr):
    """One round on the stack-resident lanes L0..L24.

    Plane schedule (found by a shortest-path search over stack schedules,
    cost = DUPs + SWAPs + POPs): every SWAPN both parks a value and fetches
    one. The top value (the previous plane's last output, or a D at the
    start of the round) is parked in the slot of the lane for B1; B1, B2, B3
    are parked in the slots of the lanes for B2, B3, B4 as those come up;
    outputs 2, 3, 0, 1 are parked in the slots of the lane for B0 and of B3,
    B2, B1, which come up for their last (consuming) use. Output 4 stays on
    top. That is 8 SWAPs and 10 DUPs per plane and no POPs; the dead D's
    stay on the stack (popped once at the end of the kernel).

    If out_addr is None the outputs replace the inputs as L0..L24 (new
    positions); otherwise they are stored to out_addr + 32 i, and every
    leftover value is renamed J for the caller to pop."""
    theta(st, scale, decay)
    last = out_addr is not None
    for yo in range(5):
        lane = {}
        for xo in range(5):
            sx = (xo + 3 * yo) % 5
            lane[xo] = (sx + 5 * xo, sx)

        def conv(xo, fetch=True):
            s, sx = lane[xo]
            if fetch:
                st.to_top(f"L{s}")       # parks the current top in the lane's slot
                st.rename(f"L{s}", "v")
            else:
                st.dup(f"L{s}", "v")
                st.rename(f"L{s}", "J")
            if st.s[-2] == f"D{sx}" and yo == 4:
                pass                     # last use of this D, right below the lane
            else:
                st.dup(f"D{sx}", "d")
            st.op("XOR", 2, "v")
            rot_top(st, scale * ROT[s], f"B{xo}", decay)

        def chi(xo, consume_f=False, consume_x=False):
            op, n1, n2, nout = CHI[yo][xo]
            b1, b2 = f"B{(xo + 1) % 5}", f"B{(xo + 2) % 5}"
            if consume_f:
                assert set(st.s[-2:]) == {b1, b2}, st.s
                if n1:
                    assert st.top() == b1
                    st.op("NOT", 1, b1)
                if n2:
                    assert st.top() == b2
                    st.op("NOT", 1, b2)
            else:
                st.dup(b1, "f1")
                if n1:
                    st.op("NOT", 1, "f1")
                st.dup(b2, "f2")
                if n2:
                    st.op("NOT", 1, "f2")
            st.op(op, 2, "f")
            if consume_x:
                assert st.s[-2] == f"B{xo}", st.s
            else:
                st.dup(f"B{xo}", "b")
            st.op("XOR", 2, "o")
            if nout:
                st.op("NOT", 1, "o")
            if yo == 0 and xo == 0:
                st.push(rc, "rc")
                st.op("XOR", 2, "o")
            if rerep:
                st.push(192, "c")
                st.op("SHR", 2, "o")
                st.dup("REP", "r")
                st.op("MUL", 2, "o")
            i = xo + 5 * yo
            if last:
                st.push(out_addr + 32 * i, "addr")
                st.op("MSTORE", 2)
            else:
                st.rename("o", f"N{i}")

        if last:
            # outputs are stored, so nothing is parked: one SWAPN, then the
            # other lanes are DUPed (searched like the plane schedule); B's
            # X1/X2 and X4/X0 meet on top for outputs X0 and X3, whose
            # consumed operand must not be NOTed below the top
            c = next(c for c in range(5)
                     if not CHI[yo][c][1] and not CHI[yo][(c + 3) % 5][1])
            X = [(k + c) % 5 for k in range(5)]
            conv(X[3])
            for k in (4, 0, 1):
                conv(X[k], fetch=False)
            chi(X[4])
            conv(X[2], fetch=False)
            chi(X[2])
            chi(X[1])
            chi(X[0], consume_f=True)
            chi(X[3], consume_f=True, consume_x=True)
            continue
        c = 4 if yo == 4 else 0          # the last plane starts at B0, which uses D2
        X = [(k + c) % 5 for k in range(5)]
        for k in (1, 2, 3, 4):
            conv(X[k])
        chi(X[2])
        conv(X[0])
        chi(X[3])
        st.to_top(f"B{X[3]}")
        chi(X[0])
        st.to_top(f"B{X[2]}")
        chi(X[1], consume_f=True)
        st.to_top(f"B{X[1]}")
        chi(X[4], consume_f=True, consume_x=True)
    for x in range(5):
        if st.has(f"D{x}"):
            st.rename(f"D{x}", "J")
    if not last:
        for i in range(25):
            st.rename(f"N{i}", f"L{i}")


def gen_keccak_stack(a: Asm, name: str, st_addr: int, scale: int = 4):
    """Subroutine `name`: Keccak-f on the 25 words at st_addr, state on the
    stack. Entry stack: [ret]; exit: jumps to ret. Clobbers no other memory.

    scale 4: interleaved 4-state kernel. scale 1: replicated kernel with v3's
    decay (offset -1, every rotation a left shift) and re-replication of bits
    [192, 256) in rounds 2, 5, ..., 23 (decay_windows(3, -1))."""
    a.region(name)
    a.label(name)
    st = Stack(a, ["ret"], deep=True)
    decay = -1 if scale == 1 else None
    if decay is not None:
        st.push(REP, "REP")
    for i in range(25):
        st.push(st_addr + 32 * i, "addr")
        st.op("MLOAD", 1, f"L{i}")
    for r, rc in enumerate(rc_table(scale)):
        round_stack(st, rc, scale, decay, decay is not None and r % 3 == 2,
                    st_addr if r == 23 else None)
    assert set(st.s[1:]) <= {"J", "REP"}, st.s
    while st.top() != "ret":
        st.pop()
    st.a.op("JUMP")
