#!/usr/bin/env python3
"""Numeric sanity checks of the MlDsaOpt44 contract statements.

Runs MlDsaOpt/44/opt.hex on vectors (Python EVM, `scripts/opt_evm.py`),
stops at the first entry of each subroutine, runs the subroutine to its
return address, and checks the pre/post relations exactly as
`MlDsaOpt44/Fn/*.lean` and `MlDsaOpt44/Layout.lean` state them (lanes,
representations, exact gas). Not part of any proof: a quick filter for
false contract statements before anyone tries to prove them.

Usage: python3 scripts/proofgen_check.py [N]   (first N vectors, default 3)
"""
from __future__ import annotations

import hashlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_opt  # noqa: E402
import opt_evm  # noqa: E402
import opt_ref  # noqa: E402

Q = opt_ref.Q
M64 = (1 << 64) - 1
GAS = dict(kf4=40238, kf1=32571, blk=7836, ntt=99705, intt=119593, pass3=17780, pass3m=19318,
           pass3k4=25613, tbuild=28511, csum=69861, usehint=56089, pack=11107, dz=46156, spr=120,
           ginit=754, absorb17=1160)


def lane(x, k):
    return (x >> (64 * k)) & M64


def word(m, a):
    return int.from_bytes(m[a:a + 32], "big")


class Run:
    def __init__(self, code, cd, labels):
        self.code, self.cd, self.lab = code, cd, labels

    def at(self, name, nth=0):
        """State at the nth arrival at subroutine `name`'s entry."""
        mem, st, pc, used = None, [], 0, 0
        target = self.lab[name]
        for _ in range(nth + 1):
            r = opt_evm.run(self.code, self.cd, memory=mem, stack=st, start_pc=pc, stop_pc=target)
            assert r["status"] == "break", r["status"]
            mem, st = r["memory"], r["stack"]
            used += r["gas_used"]
            pc = target
            # step over the entry so the next search finds the next arrival
            if _ < nth:
                r = opt_evm.run(self.code, self.cd, memory=mem, stack=st, start_pc=pc, max_steps=1)
                mem, st, pc = r["memory"], r["stack"], r["pc"]
        return bytearray(mem), list(st)

    def call(self, name, nth=0, nret=0):
        """(memory before, stack before, memory after, stack after, gas) of one call."""
        m0, s0 = self.at(name, nth)
        nargs = {"kf4": 0, "kf1": 0, "blk": 2, "ntt": 1, "intt": 1, "pass3": 3, "pass3m": 4,
                 "pass3k4": 0, "tbuild": 2, "csum": 2, "usehint": 1, "pack": 3, "dz": 2, "spr": 1,
                 "ginit": 4, "absorb17": 1, "trabs": 5, "cext": 3, "sib": 0, "dhint": 0,
                 "gfix": 1, "fix": 1, "group": 3, "mu0": 1}[name]
        ret = s0[-1 - nargs]
        r = opt_evm.run(self.code, self.cd, memory=bytearray(m0), stack=list(s0),
                        start_pc=self.lab[name], stop_pc=ret)
        assert r["status"] == "break", (name, r["status"])
        return m0, s0, bytearray(r["memory"]), r["stack"], r["gas_used"]


def check(code, g, cd, verbose=True):
    L = g.L
    lab = g.a.labels
    R = Run(code, cd, lab)
    ok_all = True

    def report(name, cond):
        nonlocal ok_all
        ok_all &= bool(cond)
        if verbose or not cond:
            print(f"  {name:28s} {'ok' if cond else 'FAIL'}")

    # dz: lane k of ZH[t] = K - raw_k(t); flag word bits iff norm violation
    m0, s0, m1, s1, gas = R.call("dz")
    K = (1 << 17) + Q
    good = True
    for k in range(4):
        v = int.from_bytes(cd[L.Z0 + 576 * k:L.Z0 + 576 * (k + 1)], "little")
        for t in range(256):
            raw = (v >> (18 * t)) & ((1 << 18) - 1)
            good &= lane(word(m1, L.ZH + 32 * t), k) == K - raw
    report("dz lanes = K - raw", good)
    report("dz gas", gas == GAS["dz"])

    # ntt: lanes < 2^28, = ntt(lanes) mod q
    m0, s0, m1, s1, gas = R.call("ntt")
    good = True
    for k in range(4):
        x = [lane(word(m0, L.ZH + 32 * t), k) % Q for t in range(256)]
        y = opt_ref.ntt(x)
        for t in range(256):
            v = lane(word(m1, L.ZH + 32 * t), k)
            good &= v < (1 << 28) and v % Q == y[t]
    report("ntt congruence/bound", good)
    report("ntt gas", gas == GAS["ntt"])

    # intt: input lanes < 2^58; output lanes < 2^27, = nttInv(lanes) mod q
    m0, s0, m1, s1, gas = R.call("intt")
    good = True
    for k in range(4):
        xin = [lane(word(m0, L.ACC + 32 * t), k) for t in range(256)]
        good &= all(v < (1 << 58) for v in xin)
        y = opt_ref.intt([v % Q for v in xin])
        for t in range(256):
            v = lane(word(m1, L.ACC + 32 * t), k)
            good &= v < (1 << 27) and v % Q == y[t]
    report("intt congruence/bound", good)
    report("intt gas", gas == GAS["intt"])

    # tbuild: be16 at tt + 6142 - 8e - 2r = tEntry(t1_r, e)
    m0, s0, m1, s1, gas = R.call("tbuild")
    tt = L.TT
    good = True
    for r in range(4):
        v = int.from_bytes(cd[32 + 320 * r:32 + 320 * (r + 1)], "little")
        t1 = [(v >> (10 * i)) & 1023 for i in range(256)]
        for e in range(768):
            a = tt + 6142 - 8 * e - 2 * r
            f = m1[a] * 256 + m1[a + 1]
            want = t1[e - 256] if 256 <= e < 512 else 1023 - t1[e % 256]
            good &= f == want
    report("tbuild table layout", good)
    report("tbuild gas", gas == GAS["tbuild"])

    # csum: lane r of SP[t] = 2^13 S'_r(t) + nneg(t)
    _, inter = opt_ref.verify_model(44, cd)
    c = inter.get("c")
    m0, s0, m1, s1, gas = R.call("csum")
    if c is not None:
        cs = [0 if x == 0 else (1 if x == 1 else -1) for x in c]
        good = True
        for r in range(4):
            t1 = inter["t1"][r]
            for t in range(256):
                S = 0
                for p in range(256):
                    if cs[p]:
                        e = t + 256 - p + (256 if cs[p] < 0 else 0)
                        S += t1[e - 256] if 256 <= e < 512 else 1023 - t1[e % 256]
                nneg = sum(1 for p in range(256) if (p <= t and cs[p] < 0) or (p > t and cs[p] > 0))
                good &= lane(word(m1, L.SP + 32 * t), r) == (S << 13) + nneg
                # the meaning: 2^13 S' + nneg = 2^13 (c * t1)(t) mod q
                ct = sum(cs[p] * (t1[t - p] if p <= t else -t1[t - p + 256]) for p in range(256))
                good &= ((S << 13) + nneg - (ct << 13)) % Q == 0
        report("csum SP = 2^13 S' + nneg", good)
    report("csum gas", gas == GAS["csum"])

    # usehint: lane r of W'[t] = UseHint(h, W - SP)
    m0, s0, m1, s1, gas = R.call("usehint")
    good = True
    h = inter["h"]
    for r in range(4):
        for t in range(256):
            w = lane(word(m0, L.ACC + 32 * t), r)
            sp = lane(word(m0, L.SP + 32 * t), r)
            hb = lane(word(m0, L.HP + 32 * t), r)
            good &= hb == h[r][t]
            good &= lane(word(m1, L.ACC + 32 * t), r) == opt_ref.use_hint(hb, (w - sp) % Q, L.p["g2"])
    report("usehint lanes", good)
    report("usehint gas", gas == GAS["usehint"])

    # pack: FIN[8 + 24 r + j] = rep(LE64(w1Encode row r)[8j..])
    m0, s0, m1, s1, gas = R.call("pack")
    good = True
    for r in range(4):
        v = 0
        for t in range(256):
            v |= lane(word(m0, L.ACC + 32 * t), r) << (6 * t)
        enc = v.to_bytes(192, "little")
        for j in range(24):
            x = int.from_bytes(enc[8 * j:8 * j + 8], "little")
            good &= word(m1, L.FIN + 32 * (8 + 24 * r + j)) == x * gen_opt.REP
    report("pack layout", good)
    report("pack gas", gas == GAS["pack"])

    # final: w1 = UseHint results equal the FIPS w1
    if "w1" in inter:
        good = all(lane(word(m1, L.ACC + 32 * t), r) == inter["w1"][r][t] for r in range(4) for t in range(256))
        report("w1 (ACC after usehint)", good)

    # FIN mu lanes
    for name in ("kf4", "kf1", "blk", "pass3", "pass3m", "pass3k4", "spr", "ginit"):
        m0, s0, m1, s1, gas = R.call(name)
        report(f"{name} gas", gas == GAS[name])
    return ok_all


def main(argv):
    n = int(argv[0]) if argv else 3
    L = gen_opt.Layout(44)
    g = gen_opt.Gen(L)
    code = g.build()
    with open(os.path.join(HERE, "..", "MlDsaOpt", "44", "opt.hex")) as f:
        assert f.read().strip() == code.hex(), "stale artifact"
    lines = open(os.path.join(HERE, "..", "vectors", "calldata.txt")).read().split("\n")
    allok = True
    for i, line in enumerate(lines[:n]):
        if not line.strip():
            continue
        cd = bytes.fromhex(line.split()[0])
        if len(cd) < L.HDR:
            continue
        print(f"vector {i}: |cd| = {len(cd)}")
        allok &= check(code, g, cd, verbose=(i == 0))
    print("ALL OK" if allok else "FAILURES")


if __name__ == "__main__":
    main(sys.argv[1:])
