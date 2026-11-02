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
* rho/pi read a lane with DUPN, which leaves a dead slot; each chi output is
  swapped into one of the five dead slots of its plane (SWAPN + POP, 5 gas
  instead of PUSH + MSTORE, 6 gas);
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


def round_stack(st: Stack, rc: int, scale: int, decay, rerep: bool, out_addr):
    """One round on the stack-resident lanes L0..L24.

    If out_addr is None the outputs replace the inputs as L0..L24 (new
    positions); otherwise they are stored to out_addr + 32 i and the dead
    input slots stay on the stack for the caller to pop."""
    base = len(st.s)
    theta(st, scale, decay)
    dead = []
    for yo in range(5):
        for xo in (4, 1, 0, 3, 2):       # B4 deepest, B2 on top
            sx, sy = (xo + 3 * yo) % 5, xo
            s = sx + 5 * sy
            if st.top() == f"L{s}":      # swapped up by the previous plane's last output
                st.rename(f"L{s}", "m")
            else:
                st.dup(f"L{s}", "m")
                st.rename(f"L{s}", f"X{s}")  # input slot is dead from here on
                dead.append(f"X{s}")
            st.dup(f"D{sx}", "d")
            st.op("XOR", 2, "v")
            rot_top(st, scale * ROT[s], f"B{xo}", decay)
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
                st.push(rc, "rc")
                st.op("XOR", 2, "o")
            if rerep:
                st.push(192, "c")
                st.op("SHR", 2, "o")
                st.dup("REP", "r")
                st.op("MUL", 2, "o")
            i = xo + 5 * yo
            if out_addr is not None:
                st.push(out_addr + 32 * i, "addr")
                st.op("MSTORE", 2)
            elif xo == 4 and yo < 4:
                # the plane's last output takes the slot of the next plane's
                # first input, which comes to the top: one SWAPN for a store
                # and a load
                st.rename("o", f"N{i}")
                st.to_top(f"L{(4 + 3 * (yo + 1)) % 5 + 20}")
            else:
                st.rename("o", f"N{i}")
                st.to_top(dead.pop())    # output into a dead slot, dead value on top
                st.pop()
    assert len(st.s) == base + 5, st.s
    for _ in range(5):
        st.pop()
    if out_addr is None:
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
    while st.top() != "ret":
        st.pop()
    st.a.op("JUMP")
