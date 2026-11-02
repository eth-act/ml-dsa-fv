#!/usr/bin/env python3
"""Packing model for the kf4 schedule of gen_opt.py --version v4 (44, 65).

Each kf4 call runs one permutation in each of the four SIMD slots. A state
may pause (its slot is saved and later restored, possibly into another slot)
and the squeezed blocks of an ExpandA instance must end up in one lane of
one buffer, at block index 0..4. A buffer block is written by one call
(blk); blocks whose lanes come from two calls need a lane merge.

This script checks the timelines below (every slot busy at most once per
call, tr sequential and complete, mu after tr, every instance squeezed
exactly 5 times, a fixed lane per instance and buffer) and counts the calls,
idle slot-permutations, buffer blocks with more than one source (merges),
state moves and accumulation terms. Usage: python3 scripts/opt_pack_model.py
"""
from __future__ import annotations

import math
import sys

# timeline: list of calls; each call = 4 slot roles:
#   ('A', r, j)  ExpandA instance A[r][j]      ('tr',) tr = H(pk) permutation
#   ('c',)  H(c-tilde) squeeze                  ('mu',) mu squeeze
#   None    idle
# buffers: name -> {(r, j): lane}


def full(cols, rows=(0, 1, 2, 3), lanes=None):
    return [[('A', r, j) for r in rows] for j in cols]


def model44():
    T = []
    bufs = {}
    for j in (0, 1):                               # G0, G1: aligned groups
        T += [[('A', r, j) for r in range(4)]] * 5
        bufs[f"B{j}"] = {(r, j): r for r in range(4)}
    T += [[('tr',), ('A', 0, 2), ('A', 1, 2), ('A', 2, 2)]] * 5    # B2, tr in slot 0
    bufs["B2"] = {(r, 2): r + 1 for r in range(3)}
    A = lambda r, j: ('A', r, j)                    # noqa: E731
    T += [[('tr',), A(0, 3), A(1, 3), A(2, 3)]] * 3                # window: B3
    T += [[('tr',), A(0, 3), A(3, 3), A(3, 2)]] * 2                # A13, A23 paused; E
    T += [[('c',), ('mu',), A(3, 3), A(3, 2)]]
    T += [[A(1, 3), A(2, 3), A(3, 3), A(3, 2)]] * 2                # A13, A23 resumed in 0, 1
    bufs["E"] = {(3, 2): 3, (3, 3): 2}                             # Kronecker, row 3
    bufs["B3"] = {(0, 3): 1, (1, 3): 2, (2, 3): 3}
    return T, bufs, 10


def model65():
    A = lambda r, j: ('A', r, j)                    # noqa: E731
    T = []
    bufs = {}
    for j in (0, 1, 2):
        T += [[A(r, j) for r in range(4)]] * 5
        bufs[f"B{j}"] = {(r, j): r for r in range(4)}
    for r in (4, 5):                               # Kronecker rows 4, 5, columns 0..3
        T += [[A(r, 3), A(r, 2), A(r, 1), A(r, 0)]] * 5
        bufs[f"K{r}"] = {(r, j): 3 - j for j in range(4)}
    for j in (3, 4):                               # tr windows, rows 0..2
        T += [[('tr',), A(0, j), A(1, j), A(2, j)]] * 5
        bufs[f"T{j}"] = {(r, j): r + 1 for r in range(3)}
    # tail: P = A33 / A34 (Kronecker row 3) lockstep, X = A44, E = A54, tr
    T += [[A(4, 4), ('tr',), A(3, 4), A(3, 3)]] * 2
    T += [[('tr',), A(5, 4), A(3, 4), A(3, 3)]] * 2                # X paused, tr 1 -> 0, E fresh
    T += [[A(4, 4), A(5, 4), A(3, 4), A(3, 3)]]                     # tr paused, X back
    T += [[A(4, 4), A(5, 4), ('tr',), ('c',)]]
    T += [[A(4, 4), A(5, 4), ('mu',), ('c',)]]
    bufs["P"] = {(3, 3): 3, (3, 4): 2}
    bufs["KX"] = {(4, 4): 0, (5, 4): 1}
    return T, bufs, 15


def check(nn, T, bufs, trn):
    k, l = {44: (4, 4), 65: (6, 5)}[nn]
    inst = {}            # (r, j) -> [(call, slot)]
    trc, mu, c = [], [], []
    idle = 0
    for t, call in enumerate(T):
        assert len(call) == 4
        for s, role in enumerate(call):
            if role is None:
                idle += 1
            elif role[0] == 'A':
                inst.setdefault(role[1:], []).append((t, s))
            elif role[0] == 'tr':
                trc.append(t)
            elif role[0] == 'mu':
                mu.append(t)
            else:
                c.append(t)
    assert sorted(inst) == [(r, j) for r in range(k) for j in range(l)], "instances"
    assert all(len(v) == 5 for v in inst.values()), "5 squeezes"
    assert len(trc) == trn and len(set(trc)) == trn, "tr sequential"
    assert len(mu) == 1 and mu[0] > max(trc), "mu after tr"
    assert len(c) >= 1
    owner = {}
    for b, m in bufs.items():
        for ij, lane in m.items():
            assert ij not in owner
            owner[ij] = (b, lane)
    assert sorted(owner) == sorted(inst)
    for b, m in bufs.items():
        assert len(set(m.values())) == len(m), f"{b}: lanes"
    # sources per buffer block, slot moves per instance
    src = {}
    moves = 0
    lane_moves = 0
    for ij, perms in inst.items():
        b, lane = owner[ij]
        for i, (t, s) in enumerate(perms):
            src.setdefault((b, i), set()).add((t, s - lane))
            if i and (perms[i - 1][0] != t - 1 or perms[i - 1][1] != s):
                moves += 1
        if any(s != lane for _, s in perms):
            lane_moves += 1
    merges = sum(len(v) - 1 for v in src.values())
    shifted = sum(1 for v in src.values() for (_, d) in v if d)
    trmoves = 0
    last = None
    for t, call in enumerate(T):
        for s, role in enumerate(call):
            if role and role[0] == 'tr':
                if last is not None and (last[0] != t - 1 or last[1] != s):
                    trmoves += 1
                last = (t, s)
    perms = k * l * 5 + trn + 2
    return dict(calls=len(T), floor=math.ceil(perms / 4), idle=idle, c_squeezes=len(c),
                buffers=len(bufs), merges=merges, shifted_sources=shifted,
                instance_moves=moves, tr_moves=trmoves)


def measure(nn):
    """Per-region gas (valid empty-message vector) of v4 / glam without
    (OPT_V4_PACK=0) and with the packed schedule."""
    import functools
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import gen_glam
    import gen_opt
    import opt_evm
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    vec = {44: "calldata.txt", 65: "mldsa65/calldata.txt"}[nn]
    cd = bytes.fromhex(open(os.path.join(root, "vectors", vec)).readline().split()[0])
    for ver in ("v4", "glam") if nn == 44 else ("glam",):      # 65: glam only (v4 code size)
        res = []
        for pk in ("0", "1"):
            os.environ["OPT_V4_PACK"] = pk
            if ver == "glam":
                g, code = gen_glam.build(nn)
                run = functools.partial(opt_evm.run, fork=gen_glam.FORK)
            else:
                g = gen_opt.Gen(gen_opt.Layout(nn, ver))
                code = g.build()
                run = opt_evm.run
            r = run(code, cd, profile=True)
            rp = g.a.region_pcs + [(len(code), "END")]
            reg = {}
            for (x, n), (y, _) in zip(rp, rp[1:]):
                reg[n] = reg.get(n, 0) + sum(r["prof"][x:y])
            res.append((r["gas_used"], len(code), reg))
        os.environ.pop("OPT_V4_PACK")
        (g0, s0, r0), (g1, s1, r1) = res
        print(f"ML-DSA-{nn} {ver}: {g0:,} -> {g1:,} gas ({g1 - g0:+,}, {100 * (g1 - g0) / g0:+.2f}%), "
              f"code {s0:,} -> {s1:,} B")
        for n in sorted(set(r0) | set(r1), key=lambda n: r1.get(n, 0) - r0.get(n, 0)):
            d = r1.get(n, 0) - r0.get(n, 0)
            if d:
                print(f"  {n:16s} {d:+9,}")


def main():
    for nn, f in ((44, model44), (65, model65)):
        r = check(nn, *f())
        print(f"ML-DSA-{nn}: " + ", ".join(f"{k} {v}" for k, v in r.items()))
    if sys.argv[1:] == ["--measure"]:
        measure(44)
        measure(65)


if __name__ == "__main__":
    sys.exit(main())
