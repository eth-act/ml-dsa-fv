#!/usr/bin/env python3
"""Per-subroutine gas of MlDsaOpt/44/opt.hex, as the contracts state it.

A contract's gas is the cost from the entry JUMPDEST (executed) up to the
return JUMPDEST (not executed), i.e. including the final JUMP. Memory never
grows inside a subroutine, so this is the static opcode sum along the path.

* Constant-cost subroutines are measured by running them in the Python EVM
  (`scripts/opt_evm.py`) from their entry with a harness return address.
* Parametric ones (`trabs n4`, `cext n`) are measured at several parameters
  and checked to be affine.
* Data-dependent ones (`fix`, `gfix`, `sib`, `dhint`, `mu0`, `group`, the
  main regions) are bounded by the path-cost formulas printed below; the
  formulas are the ones `MlDsaOpt44/Gas.lean` states, and each constant is the
  static cost of one straight-line path (`seg`), cross-checked on crafted
  worst-case inputs.

Usage: python3 scripts/proofgen_gas.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_opt  # noqa: E402
sys.setrecursionlimit(100000)
import opt_evm  # noqa: E402
import opt_ref  # noqa: E402

Q = opt_ref.Q


def setup():
    L = gen_opt.Layout(44)
    g = gen_opt.Gen(L)
    code = g.build()
    with open(os.path.join(HERE, "..", "MlDsaOpt", "44", "opt.hex")) as f:
        assert f.read().strip() == code.hex(), "stale artifact"
    cd = bytes.fromhex(open(os.path.join(HERE, "..", "vectors", "calldata.txt")).readline().split()[0])
    base = opt_evm.run(code, cd)
    assert base["ret"][-1] == 1
    return L, g, code, cd, base


def main():
    L, g, code, cd, base = setup()
    lab = g.a.labels
    hcode = code + b"\x5b\x00"
    RET = len(code)
    mem0 = base["memory"]

    def put(m, a, v):
        m[a:a + 32] = (v & opt_ref.M256).to_bytes(32, "big")

    def call(name, args, memory=None, calldata=cd):
        m = bytearray(memory if memory is not None else mem0)
        r = opt_evm.run(hcode, calldata, memory=m, stack=[RET] + list(args), start_pc=lab[name],
                        stop_pc=RET)
        assert r["status"] == "break", (name, r["status"])
        return r

    out = {}
    out["kf4"] = call("kf4", [])["gas_used"]
    out["kf1"] = call("kf1", [])["gas_used"]
    out["blk"] = call("blk", [L.ABUF, L.FL])["gas_used"]
    out["ntt"] = call("ntt", [L.ZH])["gas_used"]
    # intt: inputs must respect the bound; use the ACC of a fresh run
    out["intt"] = call("intt", [L.ACC])["gas_used"]
    out["pass3"] = call("pass3", [L.ACC, L.ZH, 0])["gas_used"]
    out["pass3m"] = call("pass3m", [L.ACC, L.ZH, 128, (1 << 192) - 1])["gas_used"]
    out["pass3k4"] = call("pass3k4", [])["gas_used"]
    out["tbuild"] = call("tbuild", [32, L.TT])["gas_used"]
    out["csum"] = call("csum", [L.TT, L.SP])["gas_used"]
    out["usehint"] = call("usehint", [L.ACC])["gas_used"]
    out["pack"] = call("pack", [L.ACC, L.FIN + 256, 4])["gas_used"]
    out["dz"] = call("dz", [L.Z0, L.ZH])["gas_used"]
    out["spr"] = call("spr", [12345])["gas_used"]
    out["ginit"] = call("ginit", [0, 15, 0, 0])["gas_used"]
    out["absorb17"] = call("absorb17", [L.HDR])["gas_used"]
    # affine families
    tr = {n4: call("trabs", [0, 3, n4, (1 << 256) - (1 << 192), L.KS])["gas_used"] for n4 in (1, 2, 3, 5)}
    a = tr[2] - tr[1]
    assert tr[3] - tr[2] == a and tr[5] - tr[3] == 2 * a
    out["trabs(n4)"] = f"{tr[1] - a} + {a} * n4"
    cx = {n: call("cext", [L.CB, 0, n])["gas_used"] for n in (1, 2, 8, 17)}
    a = cx[2] - cx[1]
    assert cx[8] - cx[2] == 6 * a and cx[17] - cx[8] == 9 * a
    out["cext(n)"] = f"{cx[1] - a} + {a} * n"
    for k, v in out.items():
        print(f"{k:12s} {v}")


if __name__ == "__main__" and "--analyse" not in sys.argv:
    main()


# ── static path analysis ────────────────────────────────────────────────

class Paths:
    """Longest static-cost paths through the code between given pcs.

    `lp(start, stops)`: the maximum static gas of a path from `start`
    (instruction included) until it reaches a pc in `stops` (not included)
    or returns (dynamic JUMP, included). Conditional jumps take both
    branches; a static JUMP to a subroutine entry is a call costing
    `callee(pc_of_jump)` and continuing at the next instruction (its return
    JUMPDEST). Loops must be cut by `stops`.
    """

    def __init__(self, code, entries, callee):
        self.code = code
        self.entries = entries
        self.callee = callee
        self.ins = {}
        i = 0
        prev = None
        while i < len(code):
            o = code[i]
            w = o - 0x5F if 0x5F <= o <= 0x7F else 0
            imm = int.from_bytes(code[i + 1:i + 1 + w], "big") if w else None
            self.ins[i] = (o, imm, i + 1 + w, prev)
            prev = i
            i += 1 + w

    def gas(self, pc):
        o = self.ins[pc][0]
        if o == 0x5E:
            # MCOPY: the size is the third push before (PUSH size; PUSH src; PUSH dst; MCOPY)
            p = pc
            for _ in range(3):
                p = self.ins[p][3]
            size = self.ins[p][1] or 0
            return 3 + 3 * ((size + 31) // 32)
        return opt_evm.GAS[o]

    def target(self, pc):
        prev = self.ins[pc][3]
        if prev is not None and 0x60 <= self.code[prev] <= 0x7F:
            return self.ins[prev][1]
        return None

    def lp(self, start, stops):
        memo = {}
        onstack = set()

        def go(pc, first=False):
            if not first and pc in stops:
                return 0
            if not first and pc in memo:
                return memo[pc]
            if pc in onstack:
                raise ValueError(f"uncut loop at {pc}")
            onstack.add(pc)
            o, imm, nxt, _ = self.ins[pc]
            g = self.gas(pc)
            if o == 0x56:                                  # JUMP
                t = self.target(pc)
                if t is None:
                    r = g                                  # return
                elif t in self.entries:
                    r = g + self.callee(pc, t) + go(nxt)
                else:
                    r = g + go(t)
            elif o == 0x57:                                # JUMPI
                r = g + max(go(self.target(pc)), go(nxt))
            elif o in (0xF3, 0xFD, 0x00, 0xFE):
                r = g
            else:
                r = g + go(nxt)
            onstack.discard(pc)
            if not first:
                memo[pc] = r
            return r
        return go(start, True)


def analyse():
    """Worst-case budgets of the data-dependent routines and main regions."""
    L, g, code, cd, base = setup()
    lab = g.a.labels
    entries = {lab[n]: n for n in ("kf4", "kf1", "blk", "ntt", "intt", "pass3", "pass3m", "pass3k4",
                                   "tbuild", "csum", "usehint", "pack", "dz", "spr", "ginit",
                                   "absorb17", "trabs", "cext", "fix", "gfix", "group", "sib",
                                   "dhint", "mu0")}
    const = dict(kf4=40238, kf1=32571, blk=7836, ntt=99705, intt=119593, pass3=17780, pass3m=19318,
                 pass3k4=25613, tbuild=28511, csum=69861, usehint=56089, pack=11107, dz=46156,
                 spr=120, ginit=754, absorb17=1160)
    B = {}

    def pushes_before(P, pc, k):
        """Immediates of the k pushes before the call's target push."""
        vals = []
        p = P.ins[P.ins[pc][3]][3]          # skip `PUSH2 fn`
        while len(vals) < k:
            o, imm, _, prev = P.ins[p]
            if not (0x5F <= o <= 0x7F):
                return None
            vals.append(imm or 0)
            p = prev
        return list(reversed(vals))

    def callee(P, pc, t):
        n = entries[t]
        if n in const:
            return const[n]
        if n == "trabs":
            n4, lm, kp = pushes_before(P, pc, 3)
            return 55 + 826 * n4
        if n == "cext":
            k, = pushes_before(P, pc, 1)
            return 19 + 205 * k
        if n == "gfix":
            a = pushes_before(P, pc, 1)
            nact = bin(a[0]).count("1") if a else 4     # group passes amask = 15 via DUP
            return B["gfix0"] + nact * B["fixSlot"] + B["fixSq"] - B["fixCont"]
        return B[n]

    P = Paths(code, set(entries), lambda pc, t: callee(P, pc, t))
    lp = P.lp
    # fix
    f = lambda k: lab[k]
    B["fixPre"] = lp(lab["fix"], {f("fxf1_145")}) + 32 * lp(f("fxf1_145"), {f("fxf1_145"), f("fxf1d_146")}) \
        + lp(f("fxf1d_146"), {f("fxg_147")})
    B["fixGroup"] = lp(f("fxg_147"), {f("fxg_147"), f("fxe_150")})
    B["fixSq"] = lp(f("fxe_150") , {f("fxg_147"), f("fxf_151")})                  # 6th squeeze path
    B["fixCont"] = sum(P.gas(p) for p in P.ins if f("fxe_150") <= p <= 13582) \
        + sum(P.gas(p) for p in P.ins if f("fxc_153") <= p < f("fxd_152"))
    B["fixFail"] = sum(P.gas(p) for p in P.ins if f("fxe_150") <= p <= 13574) + lp(f("fxf_151"), set())
    B["fixBase"] = B["fixPre"] + 44 * B["fixGroup"] + B["fixFail"]
    B["fixSlot"] = B["fixBase"] + B["fixCont"]
    # gfix own instructions (fix calls cost 0 here), all 4 slots taking the call path
    save = dict(B)
    const["fix"] = 0
    B["gfix0"] = lp(lab["gfix"], set())
    del const["fix"]
    B["group"] = lp(lab["group"], set())
    B["mu0"] = lp(lab["mu0"], set())
    # sib
    s = lambda k: lab[k]
    acc_start = 7351 if False else None
    B["sibPre"] = lp(lab["sib"], {s("sibloop_84")})
    body = [p for p in P.ins if s("sibloop_84") <= p < s("sibskip_86")]
    jumpi_skip = max(p for p in body if code[p] == 0x57 and P.target(p) == s("sibskip_86"))
    acc0 = P.ins[jumpi_skip][2]
    B["sibRej"] = lp(s("sibloop_84"), {s("sibloop_84"), acc0})
    B["sibAcc"] = lp(s("sibloop_84"), {s("sibloop_84"), s("sibskip_86")})
    B["sib"] = B["sibPre"] + 226 * B["sibRej"] + 39 * B["sibAcc"]
    # dhint: 4 rows, 80 iterations of inner/trailing loops in total
    hil = [s(k) for k in ("hil_92", "hil_97", "hil_102", "hil_107")]
    hid = [s(k) for k in ("hid_93", "hid_98", "hid_103", "hid_108")]
    htl, htd = s("htl_110"), s("htd_111")
    it = max([lp(hil[i], {hil[i], hid[i]}) for i in range(4)] + [lp(htl, {htl, htd})])
    fixed = lp(lab["dhint"], {hil[0]}) + sum(lp(hid[i], {hil[i + 1]}) for i in range(3)) \
        + lp(hid[3], {htl}) + lp(htd, set())
    B["dhintIter"] = it
    B["dhint"] = fixed + 85 * it
    return L, g, code, P, B, lab, entries, callee


if __name__ == "__main__" and "--analyse" in sys.argv:
    L, g, code, P, B, lab, entries, callee = analyse()
    for k, v in B.items():
        print(f"{k:12s} {v}")


def schedule():
    """The public schedule's constants (|M| = mlen)."""
    L, g, code, P, B, lab, entries, callee = analyse()
    lp = P.lp
    X = 4648                                     # mu selection (after the last ExpandA group)
    seg = lambda a, b: sum(P.gas(p) for p in P.ins if a <= p <= b)
    S = {}
    # short calldata: 0 .. JUMPI (taken) + short block, memory 1 word
    jumpi0 = 8
    S["short"] = seg(0, jumpi0) + lp(lab["short"], set()) + opt_evm.mem_cost(1)
    S["P1"] = lp(0, {X})
    S["muShort"] = lp(X, {lab["mudone_69"], lab["mulong_68"]})
    S["muSel"] = seg(X, 4658)
    S["muLongPre"] = lp(lab["mulong_68"], {lab["muloop_70"]})
    S["muIter"] = lp(lab["muloop_70"], {lab["muloop_70"], lab["mudone_71"]})
    S["muPost"] = lp(lab["mudone_71"], {lab["mudone_69"]})
    S["P2"] = lp(lab["mudone_69"], {lab["fhloop_81"]})
    S["finBody"] = lp(lab["fhloop_81"], {lab["fhloop_81"], 6374})
    S["P3"] = lp(6374, set())
    S["mem"] = opt_evm.mem_cost(L.TOP // 32)
    return S, B


def total(S, mlen):
    if mlen < 70:
        mu = S["muShort"]
    else:
        mu = S["muSel"] + S["muLongPre"] + ((66 + mlen) // 136 + 1) * S["muIter"] + S["muPost"]
    return S["P1"] + mu + S["P2"] + 6 * S["finBody"] + S["P3"] + S["mem"]


if __name__ == "__main__" and "--schedule" in sys.argv:
    S, B = schedule()
    for k, v in S.items():
        print(f"{k:12s} {v}")
    for n in (0, 69, 70, 136, 1000):
        print(f"schedule(|M| = {n}) = {total(S, n):,}")


PHASES = [("init", 0, 992), ("zh", 992, 1085), ("tbl", 1085, 3068), ("ntt", 3068, 3078),
          ("rho", 3078, 3439), ("g0", 3439, 3452), ("g1", 3452, 3466), ("g234", 3466, 4648),
          ("sib", 5926, 5936), ("ct", 5936, 5963), ("w", 5963, 6001), ("fin", 6001, None)]


if __name__ == "__main__" and "--phases" in sys.argv:
    L, g, code, P, B, lab, entries, callee = analyse()
    for k, v in B.items():
        print(f"B {k:12s} {v}")
    for name, a, b in PHASES:
        stops = {b} if b is not None else set()
        print(f"phase {name:6s} {a:5d} -> {b}: {P.lp(a, stops)}")
