#!/usr/bin/env python3
"""Compare the subroutines (generator regions) of two gen_opt.py versions.

  python3 scripts/opt_diff.py [--from v2] [--to v3] [44|65|87 ...]

A region counts as unchanged when its instruction sequence is identical
modulo relocation: every 2-byte PUSH whose value is a JUMPDEST is compared
as (target region, offset inside that region) instead of its absolute value.
This is the notion of "byte-identical" that scripts/proofgen_port.py ports.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import gen_opt  # noqa: E402


def regions(nn, version):
    L = gen_opt.Layout(nn, version)
    g = gen_opt.Gen(L)
    code = g.build()
    a = g.a
    rp = a.region_pcs + [(len(code), "END")]
    spans = [(x, y, n) for (x, n), (y, _) in zip(rp, rp[1:])]

    def where(pc):
        for x, y, n in spans:
            if x <= pc < y:
                return n, pc - x
        return None

    # walk the assembler items: label pushes (PUSH2 of a JUMPDEST) are known
    # exactly, so data constants are never mistaken for code addresses
    reg_at = dict(a.regions)
    out = {}
    cur = None
    for idx, it in enumerate(a.items):
        if idx in reg_at:
            cur = reg_at[idx]
            out.setdefault(cur, [])
        if cur is None:
            continue
        kind = it[0]
        if kind == "op":
            out[cur].append((it[1],))
        elif kind == "push":
            out[cur].append(("PUSH", it[2], it[1]))
        elif kind == "pushl":
            out[cur].append(("PUSHL", where(a.labels[it[1]])))
    return out, len(code)


def main(argv):
    frm, to, sets = "v2", "v3", []
    it = iter(argv)
    for x in it:
        if x == "--from":
            frm = next(it)
        elif x == "--to":
            to = next(it)
        else:
            sets.append(int(x))
    for nn in sets or [44, 65, 87]:
        A, la = regions(nn, frm)
        B, lb = regions(nn, to)
        changed = [n for n in B if n in A and A[n] != B[n]]
        added = [n for n in B if n not in A]
        removed = [n for n in A if n not in B]
        same = [n for n in B if n in A and A[n] == B[n]]
        print(f"ML-DSA-{nn} {frm} -> {to}: {la} -> {lb} bytes")
        print(f"  changed: {', '.join(changed) or '-'}")
        print(f"  added:   {', '.join(added) or '-'}")
        print(f"  removed: {', '.join(removed) or '-'}")
        print(f"  unchanged ({len(same)}): {', '.join(same)}")


if __name__ == "__main__":
    main(sys.argv[1:])
