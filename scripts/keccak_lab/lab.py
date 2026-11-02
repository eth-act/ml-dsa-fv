"""Shared harness for the Keccak-f[1600] kernel lab (prototypes only).

Nothing here is used by gen_opt.py / gen_glam.py. Every kernel prototype is a
subroutine with entry stack [ret] that permutes a multi-state Keccak state in
memory. A layout object describes how states map to memory words:

    layout.n        number of independent states per call
    layout.encode(states) -> {addr: word}   memory image of the input state
    layout.decode(mem)    -> states         read the permuted states back
    layout.setup(mem)     optional constant tables (iota tables etc.)

`check(gen, layout)` assembles the kernel behind a PUSH2/JUMP harness, runs it
on opt_evm.py against opt_ref.keccak_f for zero, all-ones, single-bit and
random states (each call mixes different states over the slots so that slot
or half mix-ups are caught), and returns gas per call with the same
convention as opt_selftest_glam.py (harness minus 15 gas), plus code size.
"""
from __future__ import annotations

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))

import opt_evm  # noqa: E402
import opt_ref  # noqa: E402
from opt_asm import Asm  # noqa: E402

M64 = opt_ref.M64
M256 = opt_ref.M256


def test_states(n, rng):
    """Lists of n states (25 lanes each) per call: zero / all-ones / single
    bits at asymmetric positions / random, mixed across slots."""
    calls = []
    zero = [0] * 25
    ones = [M64] * 25

    def single(lane, bit):
        s = [0] * 25
        s[lane] = 1 << bit
        return s
    singles = [single(l, b) for l, b in ((0, 0), (1, 63), (6, 1), (12, 31), (24, 32), (7, 62), (18, 33),
                                         (3, 17), (20, 5), (13, 50), (2, 40), (22, 9), (9, 0), (16, 63),
                                         (11, 30), (23, 47))]
    calls.append([zero] * n)
    calls.append([ones] * n)
    calls.append([zero if k % 2 else ones for k in range(n)])
    for c in range(0, len(singles), n):
        chunk = singles[c:c + n]
        calls.append(chunk + [zero] * (n - len(chunk)))
    for _ in range(3):
        calls.append([[rng.getrandbits(64) for _ in range(25)] for _ in range(n)])
    return calls


def build(gen, fork="osaka"):
    a = Asm()
    a.pushl("done")
    a.jump("kf")
    a.label("done")
    a.op("STOP")
    gen(a)
    code = a.assemble()
    size = len(code) - (a.labels["kf"])
    return code, size


def check(gen, layout, fork="osaka", seed=1, verbose=False):
    code, size = build(gen, fork)
    rng = random.Random(seed)
    gases = set()
    ncalls = 0
    for states in test_states(layout.n, rng):
        mem = bytearray(layout.mem_size)
        for addr, w in layout.encode(states).items():
            mem[addr:addr + 32] = w.to_bytes(32, "big")
        layout.setup(mem)
        r = opt_evm.run(code, b"", memory=mem, fork=fork)
        assert r["status"] == "stop" and r["stack"] == [], (r["status"], r["stack"][:4])
        got = layout.decode(r["memory"])
        exp = [opt_ref.keccak_f(s) for s in states]
        for k in range(layout.n):
            assert got[k] == exp[k], f"slot {k} mismatch: lanes {[i for i in range(25) if got[k][i] != exp[k][i]][:6]}"
        gases.add(r["gas_used"] - 15)
        ncalls += 1
    assert len(gases) == 1, gases
    gas = gases.pop()
    if verbose:
        print(f"  {ncalls} calls ok, {gas:,} gas per call, {gas / layout.n:,.0f} per state, {size:,} B")
    return gas, size, ncalls


# ── layouts ────────────────────────────────────────────────────────────────

def spread_stride(x, nbits, stride):
    r = 0
    for b in range(nbits):
        if (x >> b) & 1:
            r |= 1 << (stride * b)
    return r


def gather_stride(w, nbits, stride):
    r = 0
    for b in range(nbits):
        if (w >> (stride * b)) & 1:
            r |= 1 << b
    return r


def halves(x):
    """64-bit lane -> (even bits, odd bits) as 32-bit values."""
    e = o = 0
    for b in range(32):
        e |= ((x >> (2 * b)) & 1) << b
        o |= ((x >> (2 * b + 1)) & 1) << b
    return e, o


def unhalves(e, o):
    x = 0
    for b in range(32):
        x |= ((e >> b) & 1) << (2 * b) | ((o >> b) & 1) << (2 * b + 1)
    return x


def interleave8(vals32):
    """8 values of 32 bits -> word with bit b of value s at 8b + s."""
    return sum(spread_stride(v, 32, 8) << s for s, v in enumerate(vals32))


def deinterleave8(w):
    return [gather_stride(w >> s, 32, 8) for s in range(8)]
