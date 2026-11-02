"""Baselines through the lab harness: v3/v4 kf4 (opt_keccak) and glam kf4
(opt_keccak_glam), 4 interleaved states, same KAT set as the prototypes."""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import lab  # noqa: E402
import opt_ref  # noqa: E402
from opt_keccak import gen_keccak_f, rc_table, COMPLEMENTED  # noqa: E402
from opt_keccak_glam import gen_keccak_stack  # noqa: E402


class Layout4:
    n = 4
    ST, BT, RCT = 0, 0x320, 0x640
    mem_size = 0x640 + 24 * 32

    def encode(self, states):
        out = {}
        for i in range(25):
            w = opt_ref.interleave([s[i] for s in states])
            out[self.ST + 32 * i] = w ^ (lab.M256 if i in COMPLEMENTED else 0)
        return out

    def setup(self, mem):
        for i, v in enumerate(rc_table(4)):
            mem[self.RCT + 32 * i:self.RCT + 32 * i + 32] = v.to_bytes(32, "big")

    def decode(self, mem):
        lanes = [int.from_bytes(mem[32 * i:32 * i + 32], "big") ^ (lab.M256 if i in COMPLEMENTED else 0)
                 for i in range(25)]
        d = [opt_ref.deinterleave(w) for w in lanes]
        return [[d[i][k] for i in range(25)] for k in range(4)]


def kf4(a):
    L = Layout4
    gen_keccak_f(a, "kf", L.ST, L.BT, L.RCT, 2, 4)


def kf4_glam(a):
    gen_keccak_stack(a, "kf", Layout4.ST, 4)


if __name__ == "__main__":
    for name, g, fork in (("kf4 (v3/v4)", kf4, "osaka"), ("kf4 glam", kf4_glam, "glamsterdam")):
        gas, size, n = lab.check(g, Layout4(), fork=fork)
        print(f"{name}: {gas:,} gas/call, {gas / 4:,.0f}/state, {size:,} B, {n} KAT calls ok")
