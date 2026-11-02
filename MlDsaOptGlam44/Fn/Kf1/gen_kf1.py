#!/usr/bin/env python3
"""Generate the `kf1` proof modules for the Glamsterdam ML-DSA-44 bytecode.

  python3 MlDsaOptGlam44/Fn/Kf1/gen_kf1.py [44|65|87]

As `Kf4/gen_kf4.py`, from the frozen bytes only. `kf1` keeps one state with
every lane replicated (`rep`), rotates by single left shifts (the windows of
valid bits decay by 63 per round) and re-replicates bits [192, 256) after
rounds 3, 6, …, 24, so:

* the co-simulation identifies a lane on the stack by its top 64 bits, which
  are valid in every window;
* the symbolic terms use `UInt256` shifts, and `rerepW o` for the
  re-replication `PUSH 192 SHR DUP(REP) MUL`;
* the model functions `gD x`, `gO i` (a round's outputs before
  re-replication) and `gL i` (the stored last round's) are proved equal to
  `MlDsaOpt44`'s `Dw (Cw c) x` and `outW c D rc i` up to commutativity, so its
  `round_step` (windows) and `rerep_toNat` give the rounds.
"""
from __future__ import annotations

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(HERE, "..", "Kf4"))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
if len(sys.argv) > 1 and sys.argv[1] in ("44", "65", "87"):
    os.environ["GLAM_SET"] = sys.argv[1]

import gen_kf4 as K  # noqa: E402
from opt_keccak import COMPLEMENTED, REP  # noqa: E402
from opt_ref import M64, RC  # noqa: E402

NS, P, TAIL_MAX, MEMW, SET, SHARED, TAC = K.NS, K.P, K.TAIL_MAX, K.MEMW, K.SET, K.SHARED, K.TAC
OUT = os.path.join(ROOT, NS, "Fn", "Kf1")
M256 = (1 << 256) - 1
RET = 0xDEAD
HEADER = K.HEADER


def cpl(i, v):
    return (~v & M64) if i in COMPLEMENTED else v


def cosim(ins, seed=2):
    rng = random.Random(seed)
    S = [rng.getrandbits(64) for _ in range(25)]
    states = [S]
    for r in range(24):
        states.append(K.kround(states[-1], r))
    top = [[cpl(i, s[i]) for i in range(25)] for s in states]   # expected top 64 bits
    st, mem, snaps = [RET], {32 * i: cpl(i, S[i]) * REP for i in range(25)}, []
    for (_, _, name, arg) in ins:
        K.step(st, mem, name, arg, K.CONC)
        snaps.append((name, list(st)))
    assert [mem[32 * i] for i in range(25)] == [t * REP for t in top[24]], "kf1 is not Keccak-f"
    assert snaps[-1][1] == [RET] and ins[-1][2] == "JUMP"
    mloads = [k for k, (n, _) in enumerate(snaps) if n == "MLOAD"]
    exch = [k for k, (n, _) in enumerate(snaps) if n == "EXCHANGE"]
    assert len(exch) == 24
    blocks = [("entry", None, None, 0, mloads[24])]
    cur = mloads[24] + 1
    dead = []
    REPV = snaps[1][1][-1]
    assert REPV == REP

    def lane_of(v, r):
        """Lane index if v is a lane word of round r (by its top 64 bits)."""
        t = v >> 192
        return top[r].index(t) if t in top[r] else None

    for r in range(24):
        e = exch[r]
        blocks.append(("theta", r, None, cur, e))
        dvals = set(snaps[e][1][-5:])
        cur = e + 1
        cur0 = cur
        for y in range(5):
            k = cur
            while True:
                name, stk = snaps[k]
                if r == 23:
                    nst = sum(1 for kk in range(cur0, k + 1) if snaps[kk][0] == "MSTORE")
                    done = name == "MSTORE" and nst == 5 * (y + 1)
                else:
                    ok = True
                    outs = set()
                    for v in stk:
                        if v in (RET, REPV) or v in dvals or v in dead:
                            continue
                        lo = lane_of(v, r + 1)
                        if lo is not None and (r % 3 != 2 or v == (v >> 192) * REP):
                            outs.add(lo)
                        elif lo is not None:
                            ok = False   # a round-3k output before its re-replication
                            break
                        elif lane_of(v, r) is None:
                            ok = False
                            break
                    done = ok and outs == set(range(5 * (y + 1)))
                if done:
                    break
                k += 1
            blocks.append(("plane", r, y, cur, k))
            cur = k + 1
        if r < 23:
            left = [v for v in snaps[cur - 1][1] if v in dvals]
            assert len(left) == 1, left
            dead.append(left[0])
    blocks.append(("exit", None, None, cur, len(ins) - 1))
    return blocks, top, snaps, dead, REPV



def mk(op):
    return lambda a, b: (op.lower(), a, b)


def sym_mul(a, b):
    if a == ("rep",) and b[0] == "shr" and b[1] == ("k", 192):
        return ("rerep", b[2])
    return ("mul", a, b)


SYM = {"const": lambda v: ("k", v), "AND": mk("AND"), "OR": mk("OR"), "XOR": mk("XOR"),
       "NOT": lambda a: ("not", a), "SHL": mk("SHL"), "SHR": mk("SHR"), "MUL": sym_mul,
       "MLOAD": lambda mem, a: ("load", a[1]), "MSTORE": lambda mem, a, v: mem.__setitem__(a[1], v)}


def subst_rc(t, rcv):
    if t == ("k", rcv):
        return ("rc",)
    if t[0] in ("xor", "and", "or", "shl", "shr", "mul"):
        return (t[0], subst_rc(t[1], rcv), subst_rc(t[2], rcv))
    if t[0] in ("not", "rerep"):
        return (t[0], subst_rc(t[1], rcv))
    return t


def lanes_of(t, acc):
    if t[0] == "c":
        acc.add(t[1])
    for u in t[1:]:
        if isinstance(u, tuple):
            lanes_of(u, acc)
    return acc


def lean(t):
    k = t[0]
    if k == "c":
        return f"(c {t[1]})"
    if k == "d":
        return f"d{t[1]}"
    if k == "rc":
        return "rc"
    if k == "rep":
        return "REPw"
    if k in ("xor", "and", "or"):
        f = {"xor": "UInt256.xor", "and": "UInt256.land", "or": "UInt256.lor"}[k]
        return f"({f} {lean(t[1])} {lean(t[2])})"
    if k == "not":
        return f"(UInt256.lnot {lean(t[1])})"
    if k in ("shl", "shr"):
        assert t[1][0] == "k"
        f = "UInt256.shiftLeft" if k == "shl" else "UInt256.shiftRight"
        return f"({f} {lean(t[2])} (UInt256.ofNat {t[1][1]}))"
    if k == "rerep":
        return f"(rerepW {lean(t[1])})"
    raise SystemExit(f"cannot print {t}")


def analyse():
    code = bytes.fromhex(open(K.HEX).read().strip())
    allins = K.disasm(code)
    lo, hi = K.region("kf1")
    ins = [x for x in allins if lo <= x[1] < hi]
    assert ins[0][2] == "JUMPDEST"
    blocks, top, snaps, dead, REPV = cosim(ins)
    rcs = [v * REP for v in RC]

    def label(v, r, d_of=None, outs=False):
        if v == RET:
            return ("ret",)
        if v == REPV:
            return ("rep",)
        if d_of and v in d_of:
            return ("d", d_of[v])
        if v in dead:
            return ("j", dead.index(v))
        t = v >> 192
        if outs and t in top[r + 1]:
            return ("o", top[r + 1].index(t))
        if t in top[r]:
            return ("c", top[r].index(t))
        raise SystemExit("unlabelled stack value")

    out = []
    gD, gO, gL = {}, {}, {}
    for (kind, r, y, a, b) in blocks:
        path = ins[a:b + 1]
        cost = sum(K.gas(x[2]) for x in path)
        before = snaps[a - 1][1] if a > 0 else [RET]
        rec = dict(kind=kind, r=r, y=y, idx=[x[0] for x in path], pc0=path[0][1],
                   pc1=(ins[b + 1][1] if b + 1 < len(ins) else None), cost=cost)
        if kind in ("entry", "exit"):
            out.append(rec)
            continue
        tend = next(bb for bb in blocks if bb[0] == "theta" and bb[1] == r)[4]
        dvals = snaps[tend][1][-5:]
        if kind == "theta":
            st = [label(v, r) for v in before]
            stk = list(st)
            mem = {}
            for x in path:
                K.step(stk, mem, x[2], x[3], SYM)
            d_of = {}
            for v, t in zip(dvals, stk[-5:]):
                cols = {i % 5 for i in lanes_of(t, set())}
                xcol = [x for x in range(5) if cols == {(x - 1) % 5, (x + 1) % 5}]
                assert len(xcol) == 1
                d_of[v] = xcol[0]
                assert gD.setdefault(xcol[0], t) == t, "theta differs between rounds"
            rec["in"] = st[::-1]
            rec["out"] = [("D", d_of[v]) for v in dvals[::-1]] + st[::-1]
            rec["d_of"] = d_of
        else:
            d_of = next(o for o in out if o["kind"] == "theta" and o["r"] == r)["d_of"]
            st = [label(v, r, d_of, outs=True) for v in before]
            stk = list(st)
            mem = {}
            for x in path:
                K.step(stk, mem, x[2], x[3], SYM)
            res = []
            rer = (r % 3 == 2)
            for v, t in zip(snaps[b][1], stk):
                if t[0] in ("c", "d", "j", "o", "ret", "rep"):
                    res.append(t)
                    continue
                assert r < 23
                i = top[r + 1].index(v >> 192)
                g = subst_rc(t, rcs[r])
                if rer:
                    assert g[0] == "rerep", (r, i)
                    g = g[1]
                assert gO.setdefault(i, g) == g, f"plane output {i} differs in round {r}"
                res.append(("R" if rer else "O", i))
            if r == 23:
                rec["stores_order"] = list(mem)
                for addr, t in mem.items():
                    g = subst_rc(t, rcs[r])
                    assert g[0] == "rerep"
                    assert gL.setdefault(addr // 32, g[1]) == g[1]
            rec["in"] = st[::-1]
            rec["out"] = res[::-1]
        out.append(rec)
    return out, gD, gO, gL, rcs


def binders(t):
    ds = " ".join(f"d{x}" if K.uses(t, ("d", x)) else f"_d{x}" for x in range(5))
    rc = "rc" if K.uses(t, ("rc",)) else "_rc"
    return f"(c : Nat → UInt256) ({ds} {rc} : UInt256)"


COMM = "u256_xor_comm, u256_land_comm, u256_lor_comm"


def emit_model(gD, gO, gL):
    L = [f"""import {SHARED}.Fn.Kf4.Ac
import MlDsaOpt44.Fn.Kf1.Main
/-! Generated by `Kf1/gen_kf1.py` from `MlDsaOpt/44/glam/opt.hex`; do not edit.

The word-level model of the stack-resident `kf1`, read off the bytes by
symbolic execution, in the exact operand order of the bytecode:

* `gD x c`: theta's D for column `x` from the round's lanes `c`;
* `gO i c d0 … d4 rc`: output `i` of a round before re-replication (the
  same terms in rounds 1–23; rounds 3, 6, …, 21 re-replicate it, `rerepW`);
* `gL i …`: the same for round 24 (stored, re-replicated).

`gD_eq`, `gO_eq`, `gL_eq` identify them with `MlDsaOpt44`'s `Dw (Cw c)` and
`roundW c rc` up to commutativity of xor / and / or. -/

namespace {P}.Kf1

open EvmSemantics
open MlDsaOpt44.Proofs.Kf1

""" + HEADER + "set_option maxRecDepth 100000\n"]
    for x in range(5):
        L.append(f"def gD{x} (c : Nat → UInt256) : UInt256 :=\n  {lean(gD[x])}\n")
    for nm, g in (("gO", gO), ("gL", gL)):
        for i in range(25):
            L.append(f"def {nm}{i} {binders(g[i])} : UInt256 :=\n  {lean(g[i])}\n")
    dargs = " ".join(f"(gD{x} c)" for x in range(5))
    for nm, wrap in (("gO", ""), ("gR", "rerepW "), ("gL", "rerepW ")):
        src = "gL" if nm == "gL" else "gO"
        L.append(f"def {nm}Round (c : Nat → UInt256) (rc : UInt256) (j : Nat) : UInt256 :=\n  match j with")
        for i in range(25):
            L.append(f"  | {i} => {wrap}({src}{i} c {dargs} rc)")
        L.append(f"  | _ => {wrap}(roundW c rc j)\n")
    pieces = "outW, chiW, Bw, srcLane, shf, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv"
    for x in range(5):
        L.append(f"theorem gD{x}_eq (c : Nat → UInt256) : gD{x} c = Dw (Cw c) {x} := by\n"
                 f"  simp only [gD{x}, Dw, Cw, sh1, {COMM}]\n")
    for nm, g in (("gO", gO), ("gL", gL)):
        for i in range(25):
            L.append(f"theorem {nm}{i}_shape (c D : Nat → UInt256) (rc : UInt256) :\n"
                     f"    {nm}{i} c (D 0) (D 1) (D 2) (D 3) (D 4) rc = outW c D rc {i} := by\n"
                     f"  simp only [{nm}{i}, {pieces}, {COMM}]\n")
            L.append(f"theorem {nm}{i}_eq (c : Nat → UInt256) (rc : UInt256) :\n"
                     f"    {nm}{i} c {dargs} rc = roundW c rc {i} := by\n"
                     f"  simp only [gD0_eq, gD1_eq, gD2_eq, gD3_eq, gD4_eq]\n"
                     f"  exact {nm}{i}_shape c (Dw (Cw c)) rc\n")
    L.append(f"end {P}.Kf1\n")
    return "\n".join(L)


RCS = None


def stack_term(t, r):
    k = t[0]
    if k == "c":
        return f"c {t[1]}"
    if k == "d":
        return f"d{t[1]}"
    if k == "j":
        return f"j{t[1]}"
    if k == "ret":
        return "wd ret"
    if k == "rep":
        return "REPw"
    if k == "D":
        return f"gD{t[1]} c"
    if k in ("o", "O", "R"):
        rer = (r % 3 == 2)
        nm = "gL" if r == 23 else "gO"
        body = f"{nm}{t[1]} c d0 d1 d2 d3 d4 (wd {RCS[r]})"
        return f"rerepW ({body})" if rer else body
    raise SystemExit(f"stack term {t}")


def stk(entries, r):
    assert entries[-1] == ("ret",)
    return " :: ".join([stack_term(t, r) for t in entries[:-1]] + ["wd ret :: tail"])


def emit_blocks(recs, group):
    files = {}
    prev = []
    for rec in recs:
        kind, r, y = rec["kind"], rec["r"], rec["y"]
        hyp = (f"{{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}\n"
               f"    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)\n"
               f"    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)")
        idx = ", ".join(map(str, rec["idx"]))
        if kind == "entry":
            post = " :: ".join(f"ldY M {32 * i}" for i in reversed(range(25))) + " :: REPw :: wd ret :: tail"
            files.setdefault("Entry", []).append(
                f"theorem kf1_entry {hyp} :\n"
                f"    Reach (callState s {rec['pc0']} (wd ret :: tail) M)\n"
                f"      (callState s {rec['pc1']} ({post}) M) {rec['cost']} := by\n"
                f"  {TAC}_rreach [{idx}] with [ldY, REPw]\n")
            continue
        if kind == "exit":
            last = next(x for x in recs if x["kind"] == "plane" and x["r"] == 23 and x["y"] == 4)
            js = " ".join(f"j{k}" for k in range(23))
            files.setdefault("Exit", []).append(
                f"""theorem kf1_exit {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ {TAIL_MAX}) (M : ByteArray) (c : Nat → UInt256)
    (d0 d1 d2 d3 d4 : UInt256) ({js} : UInt256)
    (hj : Decode.isValidJumpDest {NS}.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s {rec['pc0']} ({stk(last['out'], 23)}) M)
      (callState s ret tail M) {rec['cost']} := by
  {TAC}_reach [{idx}] with [hj]
""")
            continue
        name = f"r{r}_theta" if kind == "theta" else f"r{r}_p{y}"
        js = " ".join(f"j{k}" for k in range(r)) if r else ""
        vars_ = "(c : Nat → UInt256)"
        if kind == "plane":
            vars_ += " (d0 d1 d2 d3 d4 : UInt256)"
        if js:
            vars_ += f" ({js} : UInt256)"
        nm = "gL" if r == 23 else "gO"
        withs = [f"gD{x}" for x in range(5)]
        if kind == "plane":
            withs += [f"{nm}{i}" for i in range(25)]
        withs += ["REPw", "rerepW", "stY"]
        mem0, mem1 = "M", "M"
        if r == 23 and kind == "plane":
            for a in prev:
                mem0 = f"(stY {mem0} {a} ({stack_term(('O', a // 32), r)}))"
            prev = prev + rec["stores_order"]
            for a in prev:
                mem1 = f"(stY {mem1} {a} ({stack_term(('O', a // 32), r)}))"
            rec["stores_all"] = list(prev)
        files.setdefault(f"Blocks{r // group}", []).append(
            f"theorem {name} {hyp} {vars_} :\n"
            f"    Reach (callState s {rec['pc0']} ({stk(rec['in'], r)}) {mem0})\n"
            f"      (callState s {rec['pc1']} ({stk(rec['out'], r)}) {mem1}) {rec['cost']} := by\n"
            f"  {TAC}_rreach [{idx}] with [{', '.join(withs)}]\n")
    return files


def write_blocks(files):
    for key, stmts in files.items():
        with open(os.path.join(OUT, key + ".lean"), "w") as f:
            f.write(f"""import {NS}.Infra.Reflect
import {SHARED}.Fn.Kf1.Model
import MlDsaOpt44.Fn.Kf4.Model
/-! Generated by `Kf1/gen_kf1.py`: straight-line blocks of `kf1` ({key}). -/

namespace {P}.Kf1

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open {P}.Infra
open MlDsaOpt44.Proofs.Kf1 (REPw rerepW)
open MlDsaOpt44.Proofs.Kf4 (ldY stY)
open {SHARED}.Proofs.Kf1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + "\n" + "\n".join(stmts) + f"\nend {P}.Kf1\n")


def round_fn(r):
    return "gRRound" if r % 3 == 2 else "gORound"


def lanes_term(rec, cterm):
    out = []
    for t in rec["in"][:-1]:
        if t[0] == "c":
            out.append(f"{cterm} {t[1]}")
        elif t[0] == "j":
            out.append(f"j{t[1]}")
        elif t[0] == "rep":
            out.append("REPw")
        else:
            raise SystemExit(t)
    return " :: ".join(out + ["wd ret :: tail"])


def emit_rounds(recs, rcs):
    thetas = {r["r"]: r for r in recs if r["kind"] == "theta"}
    planes = {(r["r"], r["y"]): r for r in recs if r["kind"] == "plane"}
    hyp = (f"{{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}\n"
           f"    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)\n"
           f"    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)")
    L, deadx = [], []
    for r in range(23):
        th, nx = thetas[r], thetas[r + 1]
        js = " ".join(f"j{k}" for k in range(r))
        jb = f" ({js} : UInt256)" if r else ""
        dead = [t for t in planes[(r, 4)]["out"] if t[0] == "d"]
        assert len(dead) == 1
        deadx.append(dead[0][1])
        cost = th["cost"] + sum(planes[(r, y)]["cost"] for y in range(5))
        nxt = lanes_term(nx, f"{round_fn(r)} c (wd {rcs[r]})")
        nxt = " :: ".join((f"(gD{dead[0][1]} c)" if e == f"j{r}" else e) for e in nxt.split(" :: "))
        dargs = " ".join(f"(gD{x} c)" for x in range(5))
        jargs = (" " + js) if r else ""
        chain = f"(r{r}_theta hs htl haw hsz M c{jargs})"
        for y in range(5):
            chain = f"({chain}.trans\n      (r{r}_p{y} hs htl haw hsz M c {dargs}{jargs}))"
        L.append(f"""theorem round{r} {hyp} (c : Nat → UInt256){jb} :
    Reach (callState s {th['pc0']} ({lanes_term(th, 'c')}) M)
      (callState s {nx['pc0']} ({nxt}) M) {cost} :=
  {chain}
""")
    return "\n".join(L), deadx


def emit_main(recs, rcs, deadx, gas_total):
    planes = {(r["r"], r["y"]): r for r in recs if r["kind"] == "plane"}
    entry = next(r for r in recs if r["kind"] == "entry")
    J = lambda r: " ".join(f"(gD{deadx[k]} (lanesAt M {k}))" for k in range(r))
    rcarms = "\n".join(f"  | {r} => {rcs[r]}" for r in range(24))
    chain = "(kf1_entry hs htl haw hsz M)"
    for r in range(23):
        jj = (" " + J(r)) if r else ""
        chain = f"({chain}.trans\n    (round{r} hs htl haw hsz M (lanesAt M {r}){jj}))"
    d23 = " ".join(f"(gD{x} (lanesAt M 23))" for x in range(5))
    chain = f"({chain}.trans\n    (r23_theta hs htl haw hsz M (lanesAt M 23) {J(23)}))"
    for y in range(5):
        chain = f"({chain}.trans\n    (r23_p{y} hs htl haw hsz M (lanesAt M 23) {d23} {J(23)}))"
    stores = planes[(23, 4)]["stores_all"]
    mf = "M"
    for a in stores:
        mf = f"(stY {mf} {a} (rerepW (gL{a // 32} (lanesAt M 23) {d23} (wd {rcs[23]}))))"
    chain = f"({chain}.trans\n    (kf1_exit hs htl {mf} (lanesAt M 23) {d23} {J(23)} hj hret))"
    mfm = mf.replace("lanesAt M ", "lanesAt m ").replace("(stY M ", "(stY m ")
    frame = "(FrameExcept.refl m [(0, 800)])"
    for a in stores:
        frame = f"(MlDsaOptGlam44.Proofs.Kf4.frame_stY {frame} (a := {a}) (by norm_num) _)"
    return f"""import {NS}.Fn.Kf1.Rounds
import {NS}.Fn.Kf1.Entry
import {NS}.Fn.Kf1.Exit
import {SHARED}.Fn.Kf4.Algebra
/-! Generated by `Kf1/gen_kf1.py`: the `kf1` contract.

* `lanesAt M r`: the lanes on the stack after `r` rounds (re-replicated after
  rounds 3, 6, …);
* `lanesAt_rep`: after `3 k` rounds they are exactly `rep` of the stored
  lanes of the state after `3 k` rounds (`round_step` three times, then
  `rerep_toNat`);
* `kf1_run`: entry, rounds 1–23, round 24 (stores) and the exit, {gas_total} gas;
* `kf1_spec`: KS holds the state permuted, nothing outside KS is written,
  and the call costs {gas_total} gas. -/

namespace {P}.Kf1

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs (Call call_iff KS KS1 rep cpl laneOf)
open MlDsaOpt44.Proofs.Kf1
open MlDsaOpt44.Proofs.Kf4 (ldY stY ldY_stY_ne ldY_stY_same ldY_eq)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + f"""
/-- The round constants as the bytecode pushes them (replicated). -/
def rcLit : Nat → Nat
{rcarms}
  | _ => 0

theorem rcLit_rep {{r : Nat}} (hr : r < 24) : rcLit r = rep (Crypto.Keccak.RC[r]!).toNat := by
  interval_cases r <;> decide +kernel

theorem rcLit_win {{r : Nat}} (hr : r < 24) : WinU 0 256 (wd (rcLit r)) Crypto.Keccak.RC[r]! := by
  rw [rcLit_rep hr]
  exact win_rep _

/-- The lanes on the stack after `r` rounds. -/
def lanesAt (M : ByteArray) : Nat → Nat → UInt256
  | 0 => fun j => ldY M (32 * j)
  | r + 1 => if r % 3 = 2 then gRRound (lanesAt M r) (wd (rcLit r))
      else gORound (lanesAt M r) (wd (rcLit r))

theorem gORound_eq (c : Nat → UInt256) (rc : UInt256) : gORound c rc = roundW c rc := by
  funext j
  unfold gORound
  split <;> simp only [{', '.join(f'gO{i}_eq' for i in range(25))}]

theorem gRRound_eq (c : Nat → UInt256) (rc : UInt256) :
    gRRound c rc = fun j => rerepW (roundW c rc j) := by
  funext j
  unfold gRRound
  split <;> simp only [{', '.join(f'gO{i}_eq' for i in range(25))}]

theorem gLRound_eq (c : Nat → UInt256) (rc : UInt256) :
    gLRound c rc = fun j => rerepW (roundW c rc j) := by
  funext j
  unfold gLRound
  split <;> simp only [{', '.join(f'gL{i}_eq' for i in range(25))}]

theorem lanesAt_succ_O (M : ByteArray) {{r : Nat}} (h : r % 3 ≠ 2) :
    lanesAt M (r + 1) = roundW (lanesAt M r) (wd (rcLit r)) := by
  rw [lanesAt, if_neg h, gORound_eq]

theorem lanesAt_succ_R (M : ByteArray) {{r : Nat}} (h : r % 3 = 2) :
    lanesAt M (r + 1) = fun j => rerepW (roundW (lanesAt M r) (wd (rcLit r)) j) := by
  rw [lanesAt, if_pos h, gRRound_eq]

theorem rounds_size1 {{S : Array UInt64}} (hS : S.size = 25) : ∀ n, (rounds S n).size = 25
  | 0 => hS
  | n + 1 => by
    simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_size _ _ (rounds_size1 hS n)

/-- Three rounds from exact replicas: the windows decay to `[189, 256)` and the
re-replication restores exact replicas of the state after three rounds. -/
theorem three_rounds {{A : Nat → UInt256}} {{T : Array UInt64}} (hT : T.size = 25)
    (hA : ∀ j, j < 25 → A j = UInt256.ofNat (rep (cplU j T[j]!).toNat))
    {{r1 r2 r3 : UInt256}} {{l1 l2 l3 : UInt64}} (h1 : WinU 0 256 r1 l1) (h2 : WinU 0 256 r2 l2)
    (h3 : WinU 0 256 r3 l3) {{j : Nat}} (hj : j < 25) :
    rerepW (roundW (roundW (roundW A r1) r2) r3 j) =
      UInt256.ofNat (rep (cplU j (Crypto.Keccak.round (Crypto.Keccak.round
        (Crypto.Keccak.round T l1) l2) l3)[j]!).toNat) := by
  have w0 : ∀ j, j < 25 → WinU 0 256 (A j) (cplU j T[j]!) := fun j hj => by
    rw [hA j hj]; exact win_rep _
  have hT1 := round_size T l1 hT
  have hT2 := round_size _ l2 hT1
  have w1 := fun j (hj : j < 25) => round_step hT w0 h1 hj
  have w2 := fun j (hj : j < 25) => round_step hT1 w1 h2 hj
  have w3 := round_step hT2 w2 h3 hj
  rw [← ofNat_toNat (rerepW _), rerep_toNat w3 (by norm_num)]

theorem lanesAt_rep {{M : ByteArray}} {{S : Array UInt64}} (hS : S.size = 25) (hK : KS1 M S) :
    ∀ k, k ≤ 7 → ∀ j, j < 25 →
      lanesAt M (3 * k) j = UInt256.ofNat (rep (cplU j (rounds S (3 * k))[j]!).toNat)
  | 0, _, j, hj => by
    have h := hK j hj
    simp only [lanesAt, ldY_eq, Nat.mul_zero, rounds, List.range_zero, List.foldl_nil]
    rw [show KS = 0 from rfl, Nat.zero_add] at h
    rw [h, show laneOf S j = (S[j]!).toNat from rfl, ← cplU_toNat]
  | k + 1, hk, j, hj => by
    have ih := lanesAt_rep hS hK k (by omega)
    have e3 : lanesAt M (3 * (k + 1)) =
        fun j => rerepW (roundW (lanesAt M (3 * k + 2)) (wd (rcLit (3 * k + 2))) j) :=
      lanesAt_succ_R M (r := 3 * k + 2) (by omega)
    have e2 : lanesAt M (3 * k + 2) = roundW (lanesAt M (3 * k + 1)) (wd (rcLit (3 * k + 1))) :=
      lanesAt_succ_O M (r := 3 * k + 1) (by omega)
    have e1 : lanesAt M (3 * k + 1) = roundW (lanesAt M (3 * k)) (wd (rcLit (3 * k))) :=
      lanesAt_succ_O M (r := 3 * k) (by omega)
    rw [e3, e2, e1, show 3 * (k + 1) = 3 * k + 3 by ring, rounds_three]
    exact three_rounds (rounds_size1 hS _) ih (rcLit_win (by omega)) (rcLit_win (by omega))
      (rcLit_win (by omega)) hj

theorem kf1_run {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)
    (hj : Decode.isValidJumpDest {NS}.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s {entry['pc0']} (wd ret :: tail) M)
      (callState s ret tail {mf}) {gas_total} :=
  {chain}

/-- **`kf1`.** From a call with return address `ret` (a valid JUMPDEST, with
74 stack slots left), the frame returns to `ret` after exactly {gas_total} gas
with KS holding Keccak-f of the replicated, lane-complemented state, and no
memory outside KS changed. -/
theorem kf1_spec {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    ∃ m', (∀ S : MlDsa44.Fips202.SpongeState, S.size = 25 → KS1 m S →
        KS1 m' (Crypto.Keccak.permute S)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s {entry['pc0']} [] ret tail m [] m' {gas_total} := by
  have htl : tail.length ≤ {TAIL_MAX} := by have := hr.depth; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : {MEMW} ≤ s.activeWords.toNat := hs.sized
  refine ⟨{mfm}, ?_, ?_, ?_⟩
  · intro S hS hK x hx
    have key : ∀ i : Fin 25, ldY {mfm} (32 * i.val) = gLRound (lanesAt m 23) (wd (rcLit 23)) i.val := by
      intro i
      fin_cases i <;> simp (disch := omega) only [ldY_stY_ne, ldY_stY_same, Fin.reduceFinMk,
        Fin.val_ofNat, Nat.reduceMod, Nat.reduceMul] <;> rfl
    have e2 : lanesAt m 23 = roundW (lanesAt m 22) (wd (rcLit 22)) :=
      lanesAt_succ_O m (r := 22) (by decide)
    have e1 : lanesAt m 22 = roundW (lanesAt m 21) (wd (rcLit 21)) :=
      lanesAt_succ_O m (r := 21) (by decide)
    have hv : gLRound (lanesAt m 23) (wd (rcLit 23)) x =
        UInt256.ofNat (rep (cplU x (Crypto.Keccak.permute S)[x]!).toNat) := by
      rw [gLRound_eq, e2, e1, permute_eq, show 24 = 3 * 7 + 3 by rfl, rounds_three]
      exact three_rounds (rounds_size1 hS _) (lanesAt_rep hS hK 7 le_rfl) (rcLit_win (by decide))
        (rcLit_win (by decide)) (rcLit_win (by decide)) hx
    have h := (key ⟨x, hx⟩).trans hv
    rw [ldY_eq] at h
    have := congrArg UInt256.toNat h
    rw [toNat_ofNat_of_lt (word_lt _ _), toNat_ofNat_of_lt (rep_lt (UInt64.toNat_lt _)),
      cplU_toNat] at this
    rw [show KS = 0 from rfl, Nat.zero_add]
    exact this
  · simp only [KS]
    exact {frame}
  · rw [call_iff]
    exact kf1_run hs htl haw hsz m hr.jumpdest hr.small

end {P}.Kf1
"""


def split_main(text):
    """`Algebra.lean` (artifact-independent, written for 44 and shared) and
    `Main.lean` (`kf1_run`, `kf1_spec` of this set)."""
    head, rest = text.split("/-- The round constants as the bytecode pushes them", 1)
    alg_body, main_body = rest.split("theorem kf1_run", 1)
    hdr = head.split("\n")
    imports = [l for l in hdr if l.startswith("import ")]
    rest_hdr = "\n".join(l for l in hdr if not l.startswith("import ")).split("namespace", 1)[1]
    alg = (f"import {SHARED}.Fn.Kf1.Model\nimport {SHARED}.Fn.Kf4.Algebra\n"
           f"/-! Generated by `Kf1/gen_kf1.py`: the artifact-independent part of the `kf1` proof\n"
           f"(round constants, `lanesAt`, three rounds through the windows), shared by 44, 65 and 87. -/\n\nnamespace"
           + rest_hdr.replace(f" {P}.Kf1\n", f" {SHARED}.Proofs.Kf1\n", 1)
           + "/-- The round constants as the bytecode pushes them" + alg_body + f"end {SHARED}.Proofs.Kf1\n")
    main = ("\n".join(imports) + f"\nimport {SHARED}.Fn.Kf1.Algebra\n"
            + f"/-! Generated by `Kf1/gen_kf1.py`: the `kf1` contract of `{NS}`.\n\n"
            + "* `kf1_run`: entry, rounds 1–23, round 24 (stores) and the exit;\n"
            + "* `kf1_spec`: KS holds the state permuted, nothing outside KS is\n"
            + "  written, and the call's gas. -/\n\nnamespace" + rest_hdr
            + f"open {SHARED}.Proofs.Kf1\n\ntheorem kf1_run" + main_body)
    return alg, main


if __name__ == "__main__":
    recs, gD, gO, gL, rcs = analyse()
    RCS = rcs
    total = sum(r["cost"] for r in recs)
    print(len(recs), "blocks;", total, "gas")
    if SET == "44":
        with open(os.path.join(OUT, "Model.lean"), "w") as f:
            f.write(emit_model(gD, gO, gL))
    else:
        here = (gD, gO, gL)
        os.environ["GLAM_SET"] = "44"
        import importlib
        importlib.reload(K)
        globals().update(NS=K.NS, P=K.P, MEMW=K.MEMW)
        _, gD44, gO44, gL44, _ = analyse()
        assert (gD44, gO44, gL44) == here, "kernel differs from MlDsaOptGlam44's"
        os.environ["GLAM_SET"] = SET
        importlib.reload(K)
        globals().update(NS=K.NS, P=K.P, MEMW=K.MEMW)
    files = emit_blocks(recs, 3)
    write_blocks(files)
    rounds, deadx = emit_rounds(recs, rcs)
    with open(os.path.join(OUT, "Rounds.lean"), "w") as f:
        f.write("\n".join(f"import {NS}.Fn.Kf1.Blocks{k}" for k in range(8)) + f"""
/-! Generated by `Kf1/gen_kf1.py`: rounds 1–23 of `kf1` as `Reach` facts. -/

namespace {P}.Kf1

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Kf1 (REPw rerepW)
open MlDsaOpt44.Proofs.Kf4 (ldY stY)
open {SHARED}.Proofs.Kf1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + "\n" + rounds + f"\nend {P}.Kf1\n")
    alg, main = split_main(emit_main(recs, rcs, deadx, total))
    if SET == "44":
        with open(os.path.join(OUT, "Algebra.lean"), "w") as f:
            f.write(alg)
    with open(os.path.join(OUT, "Main.lean"), "w") as f:
        f.write(main)
