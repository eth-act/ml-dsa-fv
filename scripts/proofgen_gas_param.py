#!/usr/bin/env python3
"""Per-subroutine and per-segment gas of MlDsaOpt/{65,87}/opt.hex, as the
contracts of `MlDsaOpt65` / `MlDsaOpt87` state it (the ML-DSA-44 version is
`scripts/proofgen_gas.py`; same conventions).

A contract's gas is the cost from the entry JUMPDEST (executed) up to the
return JUMPDEST (not executed), i.e. including the final JUMP. Memory never
grows inside a subroutine, so this is the static opcode sum along the path.

* Constant-cost subroutines: run in the Python EVM (`scripts/opt_evm.py`)
  from their entry with a harness return address.
* Affine families (`trabs n4`, `cext n`): measured at several parameters and
  checked to be affine; `pack nr` is measured at the row counts used (2, 4).
* Data-dependent ones (`fix`, `gfix`, `sib`, `dhint`, `mu0`, `group`) and the
  main-flow segments: longest static paths (`proofgen_gas.Paths`), loop trip
  counts as documented in the `Budget.lean` / `Main/Base.lean` docstrings.

Usage: python3 scripts/proofgen_gas_param.py NN [--analyse] [--phases] [--schedule]
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
from proofgen_gas import Paths  # noqa: E402

VEC = {65: "vectors/mldsa65/calldata.txt", 87: "vectors/mldsa87/calldata.txt"}
TAU = {65: 49, 87: 60}
OMEGA = {65: 55, 87: 75}


def setup(nn):
    L = gen_opt.Layout(nn)
    g = gen_opt.Gen(L)
    code = g.build()
    with open(os.path.join(HERE, "..", "MlDsaOpt", str(nn), "opt.hex")) as f:
        assert f.read().strip() == code.hex(), "stale artifact"
    cd = bytes.fromhex(open(os.path.join(HERE, "..", VEC[nn])).readline().split()[0])
    base = opt_evm.run(code, cd)
    assert base["ret"][-1] == 1
    return L, g, code, cd, base


def lab_prefix(lab, prefix):
    """The unique label `prefix_<n>`."""
    c = [k for k in lab if k.startswith(prefix + "_") and k[len(prefix) + 1:].isdigit()]
    assert len(c) == 1, (prefix, c)
    return lab[c[0]]


def labs_prefix(lab, prefix):
    return sorted(lab[k] for k in lab if k.startswith(prefix + "_") and k[len(prefix) + 1:].isdigit())


def measure(nn):
    L, g, code, cd, base = setup(nn)
    lab = g.a.labels
    hcode = code + b"\x5b\x00"
    RET = len(code)
    mem0 = base["memory"]

    def call(name, args, memory=None, calldata=cd):
        m = bytearray(memory if memory is not None else mem0)
        r = opt_evm.run(hcode, calldata, memory=m, stack=[RET] + list(args), start_pc=lab[name],
                        stop_pc=RET)
        assert r["status"] == "break", (name, r["status"])
        return r["gas_used"]

    out = {}
    out["kf4"] = call("kf4", [])
    out["kf1"] = call("kf1", [])
    out["blk"] = call("blk", [L.ABUF, L.FL])
    out["ntt"] = call("ntt", [L.ZH])
    out["intt"] = call("intt", [L.ACC])
    out["pass3"] = call("pass3", [L.ACC, L.ZH, 0])
    if "pass3m" in lab:
        out["pass3m"] = call("pass3m", [L.ACC, L.ZH, 128, (1 << 192) - 1])
    if "pass3k14" in lab:
        out["pass3k14"] = call("pass3k14", [])
    out["tbuild"] = call("tbuild", [32, L.TT])
    out["csum"] = call("csum", [L.TT, L.SP])
    out["usehint"] = call("usehint", [L.ACC])
    out["dz"] = call("dz", [L.Z0, L.ZH])
    out["spr"] = call("spr", [12345])
    out["ginit"] = call("ginit", [0, 15, 0, 0])
    out["absorb17"] = call("absorb17", [L.HDR])
    tr = {n4: call("trabs", [0, 3, n4, (1 << 256) - (1 << 192), L.KS]) for n4 in (1, 2, 3, 5)}
    a = tr[2] - tr[1]
    assert tr[3] - tr[2] == a and tr[5] - tr[3] == 2 * a
    out["trabs(n4)"] = f"{tr[1] - a} + {a} * n4"
    cx = {n: call("cext", [L.CB, 0, n]) for n in (1, 2, 8, 17)}
    a = cx[2] - cx[1]
    assert cx[8] - cx[2] == 6 * a and cx[17] - cx[8] == 9 * a
    out["cext(n)"] = f"{cx[1] - a} + {a} * n"
    # pack skips rows >= nr by a branch per row: one constant per row count used
    for nr in (2, 4):
        out[f"pack{nr}"] = call("pack", [L.ACC, L.FIN + 256, nr])
    for k, v in out.items():
        print(f"{k:12s} {v}")
    return out


def analyse(nn, quiet=False):
    """Worst-case budgets of the data-dependent routines."""
    L, g, code, cd, base = setup(nn)
    lab = g.a.labels
    names = ("kf4", "kf1", "blk", "ntt", "intt", "pass3", "pass3m", "pass3k14", "tbuild", "csum",
             "usehint", "pack", "dz", "spr", "ginit", "absorb17", "trabs", "cext", "fix", "gfix",
             "group", "sib", "dhint", "mu0")
    entries = {lab[n]: n for n in names if n in lab}
    meas = measure(nn) if not quiet else None
    const = {k: v for k, v in (meas or measure(nn)).items() if isinstance(v, int)}
    B = {}

    def pushes_before(P, pc, k):
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
        if n == "pack":
            nr, = pushes_before(P, pc, 1)
            return const[f"pack{nr}"]
        if n == "gfix":
            a = pushes_before(P, pc, 1)
            nact = bin(a[0]).count("1") if a else 4
            return B["gfix0"] + nact * B["fixSlot"] + B["fixSq"] - B["fixCont"]
        return B[n]

    P = Paths(code, set(entries), lambda pc, t: callee(P, pc, t))
    lp = P.lp
    seg = lambda a, b: sum(P.gas(p) for p in P.ins if a <= p <= b)
    # fix (same structure as ML-DSA-44; labels renumbered)
    f1, f1d, fg = lab_prefix(lab, "fxf1"), lab_prefix(lab, "fxf1d"), lab_prefix(lab, "fxg")
    fe, ff, fc, fd = lab_prefix(lab, "fxe"), lab_prefix(lab, "fxf"), lab_prefix(lab, "fxc"), lab_prefix(lab, "fxd")
    B["fixPre"] = lp(lab["fix"], {f1}) + 32 * lp(f1, {f1, f1d}) + lp(f1d, {fg})
    B["fixGroup"] = lp(fg, {fg, fe})
    B["fixSq"] = lp(fe, {fg, ff})
    B["fixCont"] = seg(fe, fe + 17) + seg(fc, fd - 1)
    B["fixFail"] = seg(fe, fe + 9) + lp(ff, set())
    B["fixBase"] = B["fixPre"] + 44 * B["fixGroup"] + B["fixFail"]
    B["fixSlot"] = B["fixBase"] + B["fixCont"]
    const["fix"] = 0
    B["gfix0"] = lp(lab["gfix"], set())
    del const["fix"]
    B["group"] = lp(lab["group"], set())
    if "mu0" in lab:
        B["mu0"] = lp(lab["mu0"], set())
    # sib: 265 loop visits (positions 8 … 271 and the exit visit), at most tau accepted
    tau = TAU[nn]
    sl, ssk = lab_prefix(lab, "sibloop"), lab_prefix(lab, "sibskip")
    B["sibPre"] = lp(lab["sib"], {sl})
    if nn == 87:
        # the second H(c~) block is squeezed inside the loop at position 136 (once)
        snok = lab_prefix(lab, "sibnok")
        body = [p for p in P.ins if snok <= p < ssk]
        jumpi_skip = max(p for p in body if code[p] == 0x57 and P.target(p) == ssk)
        acc0 = P.ins[jumpi_skip][2]
        head = [p for p in P.ins if sl <= p < snok]
        jumpi_nok = max(p for p in head if code[p] == 0x57 and P.target(p) == snok)
        hd = seg(sl, jumpi_nok)
        B["sibRej"] = hd + lp(snok, {sl, acc0})
        B["sibAcc"] = hd + lp(snok, {sl, ssk})
        B["sibRefill"] = lp(P.ins[jumpi_nok][2], {snok})
        B["sib"] = B["sibPre"] + (265 - tau) * B["sibRej"] + tau * B["sibAcc"] + B["sibRefill"]
    else:
        body = [p for p in P.ins if sl <= p < ssk]
        jumpi_skip = max(p for p in body if code[p] == 0x57 and P.target(p) == ssk)
        acc0 = P.ins[jumpi_skip][2]
        B["sibRej"] = lp(sl, {sl, acc0})
        B["sibAcc"] = lp(sl, {sl, ssk})
        B["sib"] = B["sibPre"] + (265 - tau) * B["sibRej"] + tau * B["sibAcc"]
    # dhint: k rows, omega + k + 1 loop visits in total
    hil, hid = labs_prefix(lab, "hil"), labs_prefix(lab, "hid")
    htl, htd = lab_prefix(lab, "htl"), lab_prefix(lab, "htd")
    k = L.k
    assert len(hil) == k == len(hid)
    it = max([lp(hil[i], {hil[i], hid[i]}) for i in range(k)] + [lp(htl, {htl, htd})])
    fixed = lp(lab["dhint"], {hil[0]}) + sum(lp(hid[i], {hil[i + 1]}) for i in range(k - 1)) \
        + lp(hid[k - 1], {htl}) + lp(htd, set())
    B["dhintFixed"] = fixed
    B["dhintIter"] = it
    B["dhint"] = fixed + (OMEGA[nn] + k + 1) * it
    if not quiet:
        for kk, v in B.items():
            print(f"{kk:12s} {v}")
    return L, g, code, P, B, lab, entries, callee, const


def phases(nn, cuts):
    """Longest static path of each main-flow segment `(name, a, b)`."""
    L, g, code, P, B, lab, entries, callee, const = analyse(nn, quiet=True)
    out = {}
    for name, a, b in cuts:
        stops = set(b) if isinstance(b, (set, list, tuple)) else ({b} if b is not None else set())
        out[name] = P.lp(a, stops)
    return out, P, B, lab, L


# Main-flow segments `(name, start pc, end pc)`; the boundaries are the pcs of
# `Main/Inv.lean` (the end pc's instruction is not part of the segment). The
# μ segment and the final hash have loops and are costed by `schedule`.
SEGMENTS = {
    65: [("init", 0, 992), ("zh", 992, 1110), ("tbl", 1110, 3093), ("ntt", 3093, 3115),
         ("rho", 3115, 3565), ("g0", 3565, 3578), ("g1", 3578, 3592), ("g2", 3592, 3606),
         ("g3", 3606, 3620), ("g4", 3620, 3634), ("g5", 3634, 4074), ("g6", 4074, 4517),
         ("g7", 4517, 5029), ("g8", 5029, 5221), ("g9", 5221, 5236), ("sib", 6545, 6555),
         ("ct", 6555, 6610), ("w", 6610, 6688)],
    87: [("init", 0, 992), ("zh", 992, 1126), ("sib", 1126, 1135), ("tbl", 1135, 3118),
         ("ntt", 3118, 3140), ("rho", 3140, 3389), ("g0", 3389, 3402), ("g1", 3402, 3416),
         ("g2", 3416, 3430), ("g3", 3430, 3444), ("g4", 3444, 3458), ("g5", 3458, 3472),
         ("g6", 3472, 3486), ("g7", 3486, 3500), ("g8", 3500, 3515), ("g9", 3515, 3530),
         ("g10", 3530, 3963), ("g11", 3963, 4430), ("g12", 4430, 4898), ("g13", 4898, 5435),
         ("g14", 5435, 5593), ("ct", 6591, 6646), ("w", 6646, 6724)],
}
# start of the μ segment, end of μ (= start of the next segment), start of fin
MU = {65: (5236, 6545), 87: (5593, 6591)}
FIN = {65: 6688, 87: 6724}
SHORT_LEN = {65: 5261 + 70, 87: None}


def schedule(nn, quiet=False):
    """Segment budgets and the public schedule's constants (|M| = mlen)."""
    L, g, code, P, B, lab, entries, callee, const = analyse(nn, quiet=True)
    lp = P.lp
    seg = lambda a, b: sum(P.gas(p) for p in P.ins if a <= p <= b)
    S = {}
    for name, a, b in SEGMENTS[nn]:
        S["p_" + name] = lp(a, {b})
    mu0, mu1 = MU[nn]
    mloop = lab_prefix(lab, "muloop")
    if nn == 65:
        mlong = lab_prefix(lab, "mulong")
        mdl = labs_prefix(lab, "mudone")         # [mudone_95 (end), mudone_97 (loop exit)]
        mend, mexit = mu1, [x for x in mdl if x != mu1][0]
        jumpi = max(p for p in P.ins if mu0 <= p < mlong and code[p] == 0x57)
        S["muShort"] = lp(mu0, {mlong, mend})
        S["muSel"] = seg(mu0, jumpi)
        S["muLongPre"] = lp(mlong, {mloop})
        S["muIter"] = lp(mloop, {mloop, mexit})
        S["muPost"] = lp(mexit, {mend})
    else:
        mexit = lab_prefix(lab, "mudone")
        S["muLongPre"] = lp(mu0, {mloop})
        S["muIter"] = lp(mloop, {mloop, mexit})
        S["muPost"] = lp(mexit, {mu1})
    fh = lab_prefix(lab, "fhloop")
    back = max(p for p in P.ins if fh <= p and code[p] == 0x57 and P.target(p) == fh)
    S["finPre"] = lp(FIN[nn], {fh})
    S["finBody"] = lp(fh, {fh, P.ins[back][2]})
    S["finPost"] = lp(P.ins[back][2], set())
    # loop count of the final hash (data independent): visits of `fhloop` in a typical run
    L2, g2, code2, cd, base = setup(nn)
    r = opt_evm.run(code2, cd, profile=True)
    S["finIters"] = r["cnt"][fh]
    S["mem"] = opt_evm.mem_cost(L.TOP // 32)
    S["short"] = seg(0, 8) + lp(lab["short"], set()) + opt_evm.mem_cost(1)
    if not quiet:
        for k, v in S.items():
            print(f"{k:12s} {v}")
    return S, B


def total(nn, S, mlen):
    fixed = sum(v for k, v in S.items() if k.startswith("p_"))
    long_mu = S["muLongPre"] + ((66 + mlen) // 136 + 1) * S["muIter"] + S["muPost"]
    if nn == 65:
        mu = S["muShort"] if mlen <= 69 else S["muSel"] + long_mu
    else:
        mu = long_mu
    fin = S["finPre"] + S["finIters"] * S["finBody"] + S["finPost"]
    return fixed + mu + fin + S["mem"]


if __name__ == "__main__":
    nn = int(sys.argv[1])
    if "--schedule" in sys.argv:
        S, B = schedule(nn)
        for n in (0, 69, 70, 136, 1000):
            print(f"schedule(|M| = {n}) = {total(nn, S, n):,}")
    if "--analyse" in sys.argv:
        analyse(nn)
    elif "--phases" not in sys.argv and "--schedule" not in sys.argv:
        measure(nn)
