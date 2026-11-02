#!/usr/bin/env python3
"""Generate the `kf4` proof modules for the Glamsterdam ML-DSA-44 bytecode.

  python3 MlDsaOptGlam44/Fn/Kf4/gen_kf4.py [44|65|87]

Everything is derived from the frozen bytes (`MlDsaOpt/44/glam/opt.hex`, the
`kf4` region of `layout.txt`), not from the generator that produced them:

1. Concrete co-simulation of the region against the reference Keccak-f
   (four states, bit-interleaved, lanes `COMPLEMENTED` stored inverted) finds
   the block boundaries -- the 25 loads, then per round the theta (ending
   at its EXCHANGE) and the five planes (a plane ends at the first
   instruction after which its five outputs are on the stack and nothing but
   lanes, outputs, D's and dead D's is), the last round's planes ending at
   their fifth store, and the exit -- and the stack slot of every lane at
   every boundary.
2. Symbolic execution of each block over atoms (lanes `c i`, the round's
   D's `d0..d4`, dead D's `jk`, the round constant) gives its output terms,
   in the exact operand order of the bytecode. The theta outputs and the
   plane outputs of rounds 1-23 must not depend on the round beyond its
   constant, and the last round's likewise; they become the model functions
   `gD x`, `gO i`, `gL i` of `Model.lean`.

Writes, under `MlDsaOptGlam<N>/Fn/Kf4/`, Blocks*.lean (one `Reach` theorem per
block, proved by `{TAC}_rreach`), Entry/Rounds/Exit and Main, and prints the
per-block costs. For 44 it also writes the artifact-independent Model.lean and
Algebra.lean, which 65 and 87 import; for 65/87 it asserts their terms match.
"""
from __future__ import annotations

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from opt_keccak import COMPLEMENTED  # noqa: E402
from opt_ref import M64, RC, ROT, interleave, rotl64  # noqa: E402

M256 = (1 << 256) - 1
# The parameter set: `gen_kf4.py [44|65|87]` (or GLAM_SET). The model and the
# round algebra (`Model.lean`, `Algebra.lean`) are artifact-independent and
# live in MlDsaOptGlam44; 65 and 87 get their own blocks, rounds and contract,
# after checking that their kernel computes the same terms.
if len(sys.argv) > 1 and sys.argv[1] in ("44", "65", "87"):
    os.environ["GLAM_SET"] = sys.argv[1]
SET = os.environ.get("GLAM_SET", "44")
MEMWORDS = {"44": 2616, "65": 3384, "87": 2897}   # the entry MSTORE sizes memory
HEX = os.path.join(ROOT, "MlDsaOpt", SET, "glam", "opt.hex")
LAYOUT = os.path.join(ROOT, "MlDsaOpt", SET, "glam", "layout.txt")
NS = f"MlDsaOptGlam{SET}"
P = f"{NS}.Proofs"
SHARED = "MlDsaOptGlam44"
TAC = f"glam{SET}"
OUT = os.path.join(ROOT, NS, "Fn", "Kf4")
TAIL_MAX = 950          # `tail.length ≤ TAIL_MAX` in every block
MEMW = MEMWORDS[SET]    # `Ctx.sized`

OPN = {0x02: "MUL", 0x16: "AND", 0x17: "OR", 0x18: "XOR", 0x19: "NOT", 0x1B: "SHL",
       0x1C: "SHR", 0x50: "POP", 0x51: "MLOAD", 0x52: "MSTORE", 0x56: "JUMP", 0x5B: "JUMPDEST"}
GAS = {"MUL": 5, "POP": 2, "JUMP": 8, "JUMPDEST": 1}


def decode_single(x):
    assert x <= 90 or x >= 128
    return (x + 145) % 256


def decode_pair(x):
    assert x <= 81 or x >= 128
    q, r = divmod(x ^ 143, 16)
    return (q + 1, r + 1) if q < r else (r + 1, 29 - q)


def region(name):
    for line in open(LAYOUT):
        f = line.split()
        if len(f) >= 5 and f[1] == ".." and f[-1] == name:
            return int(f[0]), int(f[2])
    raise SystemExit(f"no region {name}")


def disasm(code):
    """All instructions of the artifact: (index, pc, name, arg)."""
    out = []
    i = 0
    while i < len(code):
        o = code[i]
        if 0x5F <= o <= 0x7F:
            w = o - 0x5F
            out.append((len(out), i, "PUSH0" if w == 0 else "PUSH", int.from_bytes(code[i + 1:i + 1 + w], "big")))
            i += 1 + w
        elif o in (0xE6, 0xE7, 0xE8):
            out.append((len(out), i, {0xE6: "DUPN", 0xE7: "SWAPN", 0xE8: "EXCHANGE"}[o], code[i + 1]))
            i += 2
        elif 0x80 <= o <= 0x8F:
            out.append((len(out), i, "DUP", o - 0x7F))
            i += 1
        elif 0x90 <= o <= 0x9F:
            out.append((len(out), i, "SWAP", o - 0x8F))
            i += 1
        else:
            out.append((len(out), i, OPN.get(o, f"0x{o:02x}"), None))
            i += 1
    return out


def gas(name):
    return GAS.get(name, 2 if name == "PUSH0" else 3)


def step(st, mem, name, arg, ops):
    """One instruction on a stack of values; `ops` gives the value algebra."""
    if name == "PUSH0":
        st.append(ops["const"](0))
    elif name == "PUSH":
        st.append(ops["const"](arg))
    elif name == "DUP":
        st.append(st[-arg])
    elif name == "SWAP":
        st[-1], st[-1 - arg] = st[-1 - arg], st[-1]
    elif name == "DUPN":
        st.append(st[-decode_single(arg)])
    elif name == "SWAPN":
        n = decode_single(arg)
        st[-1], st[-1 - n] = st[-1 - n], st[-1]
    elif name == "EXCHANGE":
        n, m = decode_pair(arg)
        st[-1 - n], st[-1 - m] = st[-1 - m], st[-1 - n]
    elif name in ("AND", "OR", "XOR", "SHL", "SHR", "MUL"):
        a = st.pop()
        b = st.pop()
        st.append(ops[name](a, b))
    elif name == "NOT":
        st.append(ops["NOT"](st.pop()))
    elif name == "POP":
        st.pop()
    elif name == "MLOAD":
        st.append(ops["MLOAD"](mem, st.pop()))
    elif name == "MSTORE":
        a = st.pop()
        v = st.pop()
        ops["MSTORE"](mem, a, v)
    elif name in ("JUMPDEST", "JUMP"):
        pass
    else:
        raise SystemExit(f"unsupported {name}")


CONC = {"const": lambda v: v, "AND": lambda a, b: a & b, "OR": lambda a, b: a | b,
        "XOR": lambda a, b: a ^ b, "NOT": lambda a: a ^ M256,
        "SHL": lambda a, b: (b << a) & M256 if a < 256 else 0,
        "SHR": lambda a, b: b >> a if a < 256 else 0, "MUL": lambda a, b: (a * b) & M256,
        "MLOAD": lambda mem, a: mem[a], "MSTORE": lambda mem, a, v: mem.__setitem__(a, v)}


def kround(a, rnd):
    c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
    d = [c[(x - 1) % 5] ^ rotl64(c[(x + 1) % 5], 1) for x in range(5)]
    a = [a[i] ^ d[i % 5] for i in range(25)]
    b = [0] * 25
    for x in range(5):
        for y in range(5):
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl64(a[x + 5 * y], ROT[x + 5 * y])
    a = [(b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)])) & M64
         for i in range(25)]
    a[0] ^= RC[rnd]
    return a


def words(S):
    def cpl(i, v):
        return (~v & M64) if i in COMPLEMENTED else v
    return [interleave([cpl(i, S[k][i]) for k in range(4)]) for i in range(25)]


RET = 0xDEAD


def cosim(ins, seed=1):
    """Block boundaries and lane slots, by concrete co-simulation."""
    rng = random.Random(seed)
    S = [[rng.getrandbits(64) for _ in range(25)] for _ in range(4)]
    states = [S]
    for r in range(24):
        states.append([kround(s, r) for s in states[-1]])
    W = [words(s) for s in states]
    st, mem, snaps = [RET], {32 * i: W[0][i] for i in range(25)}, []
    for (_, _, name, arg) in ins:
        step(st, mem, name, arg, CONC)
        snaps.append((name, list(st)))
    assert [mem[32 * i] for i in range(25)] == W[24], "kf4 does not compute Keccak-f"
    assert snaps[-1][1] == [RET] and ins[-1][2] == "JUMP"
    mloads = [k for k, (n, _) in enumerate(snaps) if n == "MLOAD"]
    exch = [k for k, (n, _) in enumerate(snaps) if n == "EXCHANGE"]
    assert len(exch) == 24
    blocks = [("entry", None, None, 0, mloads[24])]
    cur = mloads[24] + 1
    dead = []
    for r in range(24):
        e = exch[r]
        blocks.append(("theta", r, None, cur, e))
        dvals = set(snaps[e][1][-5:])
        cur = e + 1
        cur0 = cur
        allowed = set(W[r]) | dvals | set(W[r + 1]) | set(dead) | {RET}
        for y in range(5):
            want = {W[r + 1][x + 5 * y] for x in range(5)}
            k = cur
            while True:
                name, stk = snaps[k]
                if r == 23:
                    nst = sum(1 for kk in range(cur0, k + 1) if snaps[kk][0] == "MSTORE")
                    done = name == "MSTORE" and nst == 5 * (y + 1)
                else:
                    sv = set(stk)
                    done = want <= sv and sv <= allowed and all(
                        W[r + 1][x + 5 * yy] in sv for yy in range(y) for x in range(5))
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
    return blocks, W, snaps, dead


# ── symbolic terms ────────────────────────────────────────────────────────────
# ('c', i) lane, ('d', x) D, ('j', k) dead D, ('ret',), ('k', v) constant,
# ('o', i) a previous plane's output (atom), ('rc',) the round constant,
# (op, a, b) / ('not', a) / ('rot', x, n)

def mk(op):
    def f(a, b):
        if op in ("SHL", "SHR"):
            return (op.lower(), a, b)
        return (op.lower(), a, b)
    return f


def sym_or(a, b):
    # DUP1 PUSH 4n SHL SWAP1 PUSH (256-4n) SHR OR  ->  rot(x, n)
    if (a[0] == "shr" and b[0] == "shl" and a[2] == b[2] and a[1][0] == "k" and b[1][0] == "k"
            and a[1][1] + b[1][1] == 256 and b[1][1] % 4 == 0):
        return ("rot", a[2], b[1][1] // 4)
    return ("or", a, b)


SYM = {"const": lambda v: ("k", v), "AND": mk("AND"), "OR": sym_or, "XOR": mk("XOR"),
       "NOT": lambda a: ("not", a), "SHL": mk("SHL"), "SHR": mk("SHR"), "MUL": mk("MUL"),
       "MLOAD": lambda mem, a: ("load", a[1]), "MSTORE": lambda mem, a, v: mem.__setitem__(a[1], v)}


def subst_rc(t, rcv):
    if t == ("k", rcv):
        return ("rc",)
    if t[0] in ("xor", "and", "or", "shl", "shr", "mul"):
        return (t[0], subst_rc(t[1], rcv), subst_rc(t[2], rcv))
    if t[0] == "not":
        return ("not", subst_rc(t[1], rcv))
    if t[0] == "rot":
        return ("rot", subst_rc(t[1], rcv), t[2])
    return t


def lanes_of(t, acc):
    if t[0] == "c":
        acc.add(t[1])
    elif t[0] in ("xor", "and", "or", "shl", "shr", "mul"):
        lanes_of(t[1], acc)
        lanes_of(t[2], acc)
    elif t[0] in ("not", "rot"):
        lanes_of(t[1], acc)
    return acc


def lean(t, O="O"):
    k = t[0]
    if k == "c":
        return f"(c {t[1]})"
    if k == "d":
        return f"d{t[1]}"
    if k == "rc":
        return "rc"
    if k in ("xor", "and", "or"):
        return f"({O}.{k} {lean(t[1], O)} {lean(t[2], O)})"
    if k == "not":
        return f"({O}.not {lean(t[1], O)})"
    if k == "rot":
        return f"({O}.rot {lean(t[1], O)} {t[2]})"
    raise SystemExit(f"cannot print {t}")


def analyse():
    code = bytes.fromhex(open(HEX).read().strip())
    allins = disasm(code)
    lo, hi = region("kf4")
    ins = [x for x in allins if lo <= x[1] < hi]
    assert ins[0][2] == "JUMPDEST"
    blocks, W, snaps, dead = cosim(ins)
    rcs = [interleave([v] * 4) for v in RC]

    def label(v, r, d_of=None):
        if v == RET:
            return ("ret",)
        if v in W[r]:
            return ("c", W[r].index(v))
        if d_of and v in d_of:
            return ("d", d_of[v])
        if v in dead:
            return ("j", dead.index(v))
        raise SystemExit("unlabelled stack value")

    out = []
    gD, gO, gL = {}, {}, {}
    for (kind, r, y, a, b) in blocks:
        path = ins[a:b + 1]
        cost = sum(gas(x[2]) for x in path)
        before = snaps[a - 1][1] if a > 0 else [RET]
        rec = dict(kind=kind, r=r, y=y, idx=[x[0] for x in path], pc0=path[0][1],
                   pc1=(ins[b + 1][1] if b + 1 < len(ins) else None), cost=cost)
        if kind == "entry":
            rec["out"] = [("load", 32 * i) for i in range(25)][::-1]
        elif kind == "exit":
            rec["in"] = None
        else:
            # D's of this round: the theta's last five values, labelled by column
            tend = next(bb for bb in blocks if bb[0] == "theta" and bb[1] == r)[4]
            dvals = snaps[tend][1][-5:]
            st0 = [label(v, r) for v in snaps[tend - 0][1][:-5]]
            st = [label(v, r) for v in before] if kind == "theta" else None
            if kind == "theta":
                stk = list(st)
                mem = {}
                for x in path:
                    step(stk, mem, x[2], x[3], SYM)
                ds = stk[-5:]
                d_of = {}
                for v, t in zip(dvals, ds):
                    ls = lanes_of(t, set())
                    cols = {i % 5 for i in ls}
                    xcol = [x for x in range(5) if cols == {(x - 1) % 5, (x + 1) % 5}]
                    assert len(xcol) == 1
                    d_of[v] = xcol[0]
                    tt = gD.setdefault(xcol[0], t)
                    assert tt == t, "theta differs between rounds"
                rec["in"] = st[::-1]
                rec["out"] = [("D", d_of[v]) for v in dvals[::-1]] + st[::-1]
                rec["d_of"] = d_of
            else:
                d_of = next(o for o in out if o["kind"] == "theta" and o["r"] == r)["d_of"]

                def lab(v):
                    if v in W[r + 1] and v not in W[r]:
                        return ("o", W[r + 1].index(v))
                    return label(v, r, d_of)
                st = [lab(v) for v in before]
                stk = list(st)
                mem = {}
                for x in path:
                    step(stk, mem, x[2], x[3], SYM)
                after = snaps[b][1]
                res = []
                for v, t in zip(after, stk):
                    if r < 23 and v in W[r + 1] and t[0] != "o":
                        i = W[r + 1].index(v)
                        g = subst_rc(t, rcs[r])
                        gg = gO.setdefault(i, g)
                        assert gg == g, f"plane output {i} differs in round {r}"
                        res.append(("O", i))
                    else:
                        assert t[0] in ("c", "d", "j", "o", "ret"), (kind, r, y, t)
                        res.append(t)
                if r == 23:
                    rec["stores_order"] = list(mem)
                    for addr, t in mem.items():
                        i = addr // 32
                        g = subst_rc(t, rcs[r])
                        gg = gL.setdefault(i, g)
                        assert gg == g
                    rec["stores"] = sorted(mem)
                rec["in"] = st[::-1]
                rec["out"] = res[::-1]
        out.append(rec)
    return out, gD, gO, gL, rcs



HEADER = """set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
"""


def uses(t, k):
    """Does term t mention atom k (('d', x) or ('rc',))?"""
    if t == k:
        return True
    return any(uses(u, k) for u in t[1:] if isinstance(u, tuple))


def binders(t):
    ds = " ".join(f"d{x}" if uses(t, ("d", x)) else f"_d{x}" for x in range(5))
    rc = "rc" if uses(t, ("rc",)) else "_rc"
    return f"(O : Ops α) (c : Fin 25 → α) ({ds} {rc} : α)"


V3OUT = [f"out{i // 5}{i % 5}" for i in range(25)]


def emit_model(gD, gO, gL):
    L = [f"""import {SHARED}.Fn.Kf4.Ac
import MlDsaOpt44.Fn.Kf4.Main
/-! Generated by `Kf4/gen_kf4.py` from `MlDsaOpt/44/glam/opt.hex`; do not edit.

The word-level model of the stack-resident `kf4`, read off the bytes by
symbolic execution, in the exact operand order of the bytecode:

* `gD x c`: theta's D for column `x` from the round's lanes `c`;
* `gO i c d0 … d4 rc`: plane output `i` of rounds 1–23 from the lanes, the
  round's D's and its constant (the same terms in every such round);
* `gL i …`: the same for round 24, whose outputs are stored.

`gD_eq`, `gO_eq`, `gL_eq` identify them with the `MlDsaOpt44` round model
(`dO*`, `out*`) up to commutativity and associativity of xor / and / or, so
the round algebra of `MlDsaOpt44.Fn.Kf4` (`out*_W`, `slot*`) applies as is. -/

namespace {P}.Kf4

open EvmSemantics
open MlDsaOpt44.Proofs.Kf4

""" + HEADER + "set_option maxRecDepth 100000\n\nvariable {α : Type}\n"]
    for x in range(5):
        L.append(f"def gD{x} (O : Ops α) (c : Fin 25 → α) : α :=\n  {lean(gD[x])}\n")
    for i in range(25):
        L.append(f"def gO{i} {binders(gO[i])} : α :=\n  {lean(gO[i])}\n")
    for i in range(25):
        L.append(f"def gL{i} {binders(gL[i])} : α :=\n  {lean(gL[i])}\n")
    dargs = " ".join(f"(gD{x} O c)" for x in range(5))
    for nm in ("gO", "gL"):
        L.append(f"/-- The lanes after a {'round 1–23' if nm == 'gO' else 'last'} round. -/")
        L.append(f"def {nm}Round (O : Ops α) (c : Fin 25 → α) (rc : α) (i : Fin 25) : α :=\n  match i.val with")
        for i in range(25):
            L.append(f"  | {i} => {nm}{i} O c {dargs} rc")
        L.append("  | _ => c i\n")
    simps = ("gD0, gD1, gD2, gD3, gD4, dO0, dO1, dO2, dO3, dO4, colC, dL, dR, bv, bv0, "
             "Ops256_xor, Ops256_and, Ops256_or, Ops256_not, Ops256_rot")
    for x in range(5):
        L.append(f"theorem gD{x}_eq (c : Fin 25 → UInt256) : gD{x} Ops256 c = dO{x} Ops256 c := by\n"
                 f"  simp only [{simps}]\n")
    # the v3 output terms, with the D's kept abstract
    v3 = open(os.path.join(ROOT, "MlDsaOpt44", "Fn", "Kf4", "Model.lean")).read()
    shape = {}
    for i in range(25):
        o = V3OUT[i]
        k = v3.index(f"def {o} (O : Ops α)")
        body = v3[k:].split(":=\n", 1)[1].split("\n\n", 1)[0].strip()
        for x in range(5):
            body = body.replace(f"(dO{x} O c)", f"d{x}")
        shape[i] = body.replace("O ", "Ops256 ").replace(" rc", " rc")
    d256 = " ".join(f"(gD{x} Ops256 c)" for x in range(5))
    comm = "u256_xor_comm, u256_land_comm, u256_lor_comm"
    pieces = "bv, bv0, Ops256_xor, Ops256_and, Ops256_or, Ops256_not, Ops256_rot"
    for nm, g in (("gO", gO), ("gL", gL)):
        for i in range(25):
            o = V3OUT[i]
            ch = f"ch{i // 5}{i % 5}"
            L.append(f"theorem {nm}{i}_shape (c : Fin 25 → UInt256) (d0 d1 d2 d3 d4 rc : UInt256) :\n"
                     f"    {nm}{i} Ops256 c d0 d1 d2 d3 d4 rc = {shape[i]} := by\n"
                     f"  simp only [{nm}{i}, {ch}, {pieces}, {comm}]\n")
            L.append(f"theorem {nm}{i}_eq (c : Fin 25 → UInt256) (rc : UInt256) :\n"
                     f"    {nm}{i} Ops256 c {d256} rc = {o} Ops256 c rc := by\n"
                     f"  simp only [{nm}{i}_shape, gD0_eq, gD1_eq, gD2_eq, gD3_eq, gD4_eq, {o}]\n")
    L.append(f"end {P}.Kf4\n")
    return "\n".join(L)


def stack_term(t, r):
    """A stack entry in Lean (round r; c, d0..d4, j*, ret, previous outputs)."""
    k = t[0]
    if k == "c":
        return f"c {t[1]}"
    if k == "d":
        return f"d{t[1]}"
    if k == "j":
        return f"j{t[1]}"
    if k == "ret":
        return "wd ret"
    if k == "D":
        return f"gD{t[1]} Ops256 c"
    if k in ("o", "O"):
        nm = "gL" if r == 23 else "gO"
        return f"{nm}{t[1]} Ops256 c d0 d1 d2 d3 d4 (wd {RCS[r]})"
    if k == "load":
        return f"ldY M {t[1]}"
    raise SystemExit(f"stack term {t}")


def stk(entries, r):
    """Top-first entries, with the caller's `ret :: tail` below."""
    assert entries[-1] == ("ret",)
    return " :: ".join([stack_term(t, r) for t in entries[:-1]] + ["wd ret :: tail"])


RCS = None


def emit_blocks(recs, group):
    files = {}
    for rec in recs:
        kind, r, y = rec["kind"], rec["r"], rec["y"]
        if kind == "entry":
            name, key = "kf4_entry", "Entry"
        elif kind == "exit":
            name, key = "kf4_exit", "Exit"
        else:
            name = f"r{r}_theta" if kind == "theta" else f"r{r}_p{y}"
            key = f"Blocks{r // group}"
        js = " ".join(f"j{k}" for k in range(r)) if r else ""
        vars_ = "(c : Fin 25 → UInt256)"
        if kind == "plane":
            vars_ += " (d0 d1 d2 d3 d4 : UInt256)"
        if js:
            vars_ += f" ({js} : UInt256)"
        idx = ", ".join(map(str, rec["idx"]))
        hyp = (f"{{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}\n"
               f"    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)\n"
               f"    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)")
        if kind == "entry":
            pre = "wd ret :: tail"
            post = " :: ".join(f"ldY M {32 * i}" for i in reversed(range(25))) + " :: wd ret :: tail"
            stmt = (f"theorem {name} {hyp} :\n"
                    f"    Reach (callState s {rec['pc0']} ({pre}) M)\n"
                    f"      (callState s {rec['pc1']} ({post}) M) {rec['cost']} := by\n"
                    f"  {TAC}_rreach [{idx}] with [ldY]\n")
        elif kind == "exit":
            continue
        else:
            nm = "gL" if r == 23 else "gO"
            withs = [f"gD{x}" for x in range(5)] + ([f"{nm}{i}" for i in range(25)] if kind == "plane" else [])
            withs += ["Ops256", "rot256", "stY"]
            mem1 = "M"
            if rec.get("stores"):
                for a in rec["stores_all"]:
                    i = a // 32
                    mem1 = f"(stY {mem1} {a} ({stack_term(('O', i), r)}))"
            mem0 = "M"
            if rec.get("prev_stores"):
                for a in rec["prev_stores"]:
                    i = a // 32
                    mem0 = f"(stY {mem0} {a} ({stack_term(('O', i), r)}))"
            stmt = (f"theorem {name} {hyp} {vars_} :\n"
                    f"    Reach (callState s {rec['pc0']} ({stk(rec['in'], r)}) {mem0})\n"
                    f"      (callState s {rec['pc1']} ({stk(rec['out'], r)}) {mem1}) {rec['cost']} := by\n"
                    f"  {TAC}_rreach [{idx}] with [{', '.join(withs)}]\n")
        files.setdefault(key, []).append(stmt)
    return files


def write_blocks(files):
    for key, stmts in files.items():
        with open(os.path.join(OUT, key + ".lean"), "w") as f:
            f.write(f"""import {NS}.Infra.Reflect
import {SHARED}.Fn.Kf4.Model
/-! Generated by `Kf4/gen_kf4.py`: straight-line blocks of `kf4` ({key}). -/

namespace {P}.Kf4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open {P}.Infra
open MlDsaOpt44.Proofs.Kf4 (Ops256 rot256 ldY stY)
open {SHARED}.Proofs.Kf4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + "\n" + "\n".join(stmts) + f"\nend {P}.Kf4\n")


def emit_exit(recs):
    last = next(r for r in recs if r["kind"] == "plane" and r["r"] == 23 and r["y"] == 4)
    ex = next(r for r in recs if r["kind"] == "exit")
    js = " ".join(f"j{k}" for k in range(23))
    mem = "M"
    idx = ", ".join(map(str, ex["idx"]))
    return (f"""theorem kf4_exit {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ {TAIL_MAX}) (M : ByteArray) (c : Fin 25 → UInt256)
    (d0 d1 d2 d3 d4 : UInt256) ({js} : UInt256)
    (hj : Decode.isValidJumpDest {NS}.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s {ex['pc0']} ({stk(last['out'], 23)}) M)
      (callState s ret tail M) {ex['cost']} := by
  {TAC}_reach [{idx}] with [hj]
""")


def lanes_term(rec, r, cterm):
    """The theta input stack of round r with lanes `cterm i` and junk j*."""
    out = []
    for t in rec["in"][:-1]:
        if t[0] == "c":
            out.append(f"{cterm} {t[1]}")
        elif t[0] == "j":
            out.append(f"j{t[1]}")
        else:
            raise SystemExit(t)
    return " :: ".join(out + ["wd ret :: tail"])


def emit_rounds(recs, rcs):
    thetas = {r["r"]: r for r in recs if r["kind"] == "theta"}
    planes = {(r["r"], r["y"]): r for r in recs if r["kind"] == "plane"}
    hyp = (f"{{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}\n"
           f"    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)\n"
           f"    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)")
    L = []
    for r in range(23):
        th, nx = thetas[r], thetas[r + 1]
        js = " ".join(f"j{k}" for k in range(r))
        jb = f" ({js} : UInt256)" if r else ""
        # the dead D of this round: the one D left after plane 4
        dead = [t for t in planes[(r, 4)]["out"] if t[0] == "d"]
        assert len(dead) == 1
        cost = th["cost"] + sum(planes[(r, y)]["cost"] for y in range(5))
        nxt = lanes_term(nx, r + 1, f"gORound Ops256 c (wd {rcs[r]})").replace(
            f"j{r} ", f"(gD{dead[0][1]} Ops256 c) ").replace(f"j{r}\n", f"(gD{dead[0][1]} Ops256 c)\n")
        dargs = " ".join(f"(gD{x} Ops256 c)" for x in range(5))
        jargs = (" " + js) if r else ""
        chain = f"(r{r}_theta hs htl haw hsz M c{jargs})"
        for y in range(5):
            chain = f"({chain}.trans\n      (r{r}_p{y} hs htl haw hsz M c {dargs}{jargs}))"
        L.append(f"""theorem round{r} {hyp} (c : Fin 25 → UInt256){jb} :
    Reach (callState s {th['pc0']} ({lanes_term(th, r, 'c')}) M)
      (callState s {nx['pc0']} ({nxt}) M) {cost} :=
  {chain}
""")
    return "\n".join(L)


def emit_main(recs, rcs, gas_total):
    thetas = {r["r"]: r for r in recs if r["kind"] == "theta"}
    planes = {(r["r"], r["y"]): r for r in recs if r["kind"] == "plane"}
    entry = next(r for r in recs if r["kind"] == "entry")
    deadx = []
    for r in range(23):
        dead = [t for t in planes[(r, 4)]["out"] if t[0] == "d"]
        deadx.append(dead[0][1])
    J = lambda r: " ".join(f"(gD{deadx[k]} Ops256 (lanesAt M {k}))" for k in range(r))
    rcarms = "\n".join(f"  | {r} => {rcs[r]}" for r in range(24))
    chain = "(kf4_entry hs htl haw hsz M)"
    for r in range(23):
        jj = (" " + J(r)) if r else ""
        chain = f"({chain}.trans\n    (round{r} hs htl haw hsz M (lanesAt M {r}){jj}))"
    d23 = " ".join(f"(gD{x} Ops256 (lanesAt M 23))" for x in range(5))
    chain = f"({chain}.trans\n    (r23_theta hs htl haw hsz M (lanesAt M 23) {J(23)}))"
    for y in range(5):
        chain = f"({chain}.trans\n    (r23_p{y} hs htl haw hsz M (lanesAt M 23) {d23} {J(23)}))"
    stores = planes[(23, 4)]["stores_all"]
    mf = "M"
    for a in stores:
        mf = f"(stY {mf} {a} (gL{a // 32} Ops256 (lanesAt M 23) {d23} (wd {rcs[23]})))"
    chain = f"({chain}.trans\n    (kf4_exit hs htl {mf} (lanesAt M 23) {d23} {J(23)} hj hret))"
    reads = "\n".join(f"  · simp only [{', '.join('ldY_stY_ne _ _ (by omega)' for _ in range(0))}]" for _ in range(0))
    return f"""import {NS}.Fn.Kf4.Rounds
import {NS}.Fn.Kf4.Entry
import {NS}.Fn.Kf4.Exit
/-! Generated by `Kf4/gen_kf4.py`: the `kf4` contract.

* `gORound_W`, `gLRound_W`: a round of the model maps interleaved,
  lane-complemented states to the same of `Keccak.round` (through `gO_eq`,
  `gL_eq` and the `MlDsaOpt44` lemmas `out*_W`, `slot*`);
* `lanesAt M r`: the lanes on the stack after `r` rounds; `lanesAt_spec`:
  they are the states after `r` rounds;
* `kf4_run`: entry, rounds 1–23, round 24 (stores) and the exit, {gas_total} gas;
* `kf4_spec`: KS holds the four states permuted, nothing outside KS is
  written, and the call costs {gas_total} gas. -/

namespace {P}.Kf4

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto.Keccak
open MlDsaOptCommon
open MlDsaOpt44.Proofs (Call call_iff KS KS4 Sized4)
open MlDsaOpt44.Proofs.Kf4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + f"""
/-- The round constants as the bytecode pushes them (interleaved). -/
def rcLit : Nat → Nat
{rcarms}
  | _ => 0

theorem rcLit_il {{r : Nat}} (hr : r < 24) : rcLit r = MlDsaOpt44.Proofs.il fun _ => (RC[r]!).toNat := by
  interval_cases r <;> decide +kernel

theorem rcLit_W {{r : Nat}} (hr : r < 24) : wd (rcLit r) = W fun _ => RC[r]! := by
  unfold W wd
  rw [rcLit_il hr]

/-- The lanes on the stack after `r` rounds. -/
def lanesAt (M : ByteArray) : Nat → Fin 25 → UInt256
  | 0 => fun i => ldY M (32 * i.val)
  | r + 1 => gORound Ops256 (lanesAt M r) (wd (rcLit r))

/-- The states `S`, lane by lane in the interleaved, complemented form. -/
def Wv (S : Nat → Array UInt64) : Fin 25 → UInt256 := fun i => W fun k => cplU i.val (S k)[i.val]!

{emit_round_W("gO")}
{emit_round_W("gL")}
theorem lanesAt_spec {{M : ByteArray}} {{S : Nat → Array UInt64}} (hS : ∀ k, k < 4 → (S k).size = 25)
    (hA : KSW M 0 S) : ∀ r, r ≤ 23 → lanesAt M r = Wv fun k => rounds (S k) r
  | 0, _ => by
    funext i
    have := hA i.val i.isLt
    simpa [lanesAt, Wv, rounds] using this
  | r + 1, hr => by
    rw [lanesAt, lanesAt_spec hS hA r (by omega), rcLit_W (by omega),
      gORound_W _ (fun k hk => rounds_size (hS k hk) r)]
    funext i
    simp only [Wv, rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem kf4_run {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (htl : tail.length ≤ {TAIL_MAX}) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsz : {MEMW} ≤ s.activeWords.toNat) (M : ByteArray)
    (hj : Decode.isValidJumpDest {NS}.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s {entry['pc0']} (wd ret :: tail) M)
      (callState s ret tail {mf}) {gas_total} :=
  {chain}

theorem frame_stY {{M M' : ByteArray}} (h : FrameExcept M M' [(0, 800)]) {{a : Nat}}
    (ha : a + 32 ≤ 800) (v : UInt256) : FrameExcept M (stY M' a v) [(0, 800)] := by
  refine FrameExcept.mono (FrameExcept.trans h (FrameExcept.mstore M' a v.toNat)) ?_
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨(0, 800), by simp, le_rfl, le_rfl⟩
  · exact ⟨(0, 800), by simp, by simp, by simpa using ha⟩

/-- **`kf4`.** From a call with return address `ret` (a valid JUMPDEST, with
74 stack slots left), the frame returns to `ret` after exactly {gas_total} gas
with KS holding Keccak-f of each of the four interleaved, lane-complemented
states, and no memory outside KS changed. -/
theorem kf4_spec {{s : State}} (hs : Ctx s) {{ret : Nat}} {{tail : List UInt256}}
    (hr : RetOK 74 ret tail) (m : ByteArray) :
    ∃ m', (∀ S, Sized4 S → KS4 m S → KS4 m' fun k => permute (S k)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s {entry['pc0']} [] ret tail m [] m' {gas_total} := by
  have htl : tail.length ≤ {TAIL_MAX} := by have := hr.depth; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : {MEMW} ≤ s.activeWords.toNat := hs.sized
  refine ⟨{mf.replace("(lanesAt M ", "(lanesAt m ").replace(" M ", " m ").replace("(stY M ", "(stY m ")}, ?_, ?_, ?_⟩
  · intro S hS hK
    have hl := lanesAt_spec hS (ksw_of_ks4 hK) 23 le_rfl
    apply ks4_of_ksw
    intro x hx
    have key : ∀ i : Fin 25, ldY {mf.replace("(lanesAt M ", "(lanesAt m ").replace(" M ", " m ").replace("(stY M ", "(stY m ")} (32 * i.val) =
        gLRound Ops256 (lanesAt m 23) (wd (rcLit 23)) i := by
      intro i
      fin_cases i <;> simp (disch := omega) only [ldY_stY_ne, ldY_stY_same, Fin.reduceFinMk,
        Fin.val_ofNat, Nat.reduceMod, Nat.reduceMul] <;> rfl
    have h2 : gLRound Ops256 (lanesAt m 23) (wd (rcLit 23)) ⟨x, hx⟩ =
        W fun k => cplU x (permute (S k))[x]! := by
      rw [hl, rcLit_W (by omega), gLRound_W _ (fun k hk => rounds_size (hS k hk) 23)]
      simp only [Wv, permute_eq, rounds, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    simp only [Nat.zero_add]
    exact (key ⟨x, hx⟩).trans h2
  · simp only [KS]
    {frame_chain(stores)}
  · rw [call_iff]
    exact kf4_run hs htl haw hsz m hr.jumpdest hr.small

end {P}.Kf4
"""


def frame_chain(stores):
    t = "(FrameExcept.refl m [(0, 800)])"
    for a in stores:
        t = f"(frame_stY {t} (a := {a}) (by norm_num) _)"
    return "exact " + t


def split_main(text):
    """`Algebra.lean` (artifact-independent: round constants, `lanesAt`, the
    round algebra, `frame_stY`; written for 44 and shared) and `Main.lean`
    (`kf4_run`, `kf4_spec` of this set)."""
    head, rest = text.split("/-- The round constants as the bytecode pushes them", 1)
    alg_body, main_body = rest.split("theorem kf4_run", 1)
    frame, main_body = main_body.split("theorem frame_stY", 1)[0], main_body
    # move frame_stY (artifact-independent) into the algebra
    pre, post = main_body.split("theorem frame_stY", 1)
    fr, spec = post.split("/-- **`kf4`.**", 1)
    hdr_lines = head.split("\n")
    imports = [l for l in hdr_lines if l.startswith("import ")]
    rest_hdr = "\n".join(l for l in hdr_lines if not l.startswith("import ")).split("namespace", 1)[1]
    alg = (f"import {SHARED}.Fn.Kf4.Model\n/-! Generated by `Kf4/gen_kf4.py`: the artifact-independent part of the "
           f"`kf4` proof\n(round constants, `lanesAt`, the round algebra), shared by 44, 65 and 87. -/\n\nnamespace"
           + rest_hdr.replace(f"namespace {P}.Kf4", "").replace(f" {P}.Kf4\n", f" {SHARED}.Proofs.Kf4\n", 1)
           + "/-- The round constants as the bytecode pushes them" + alg_body
           + "theorem frame_stY" + fr + f"end {SHARED}.Proofs.Kf4\n")
    main = ("\n".join(imports) + f"\nimport {SHARED}.Fn.Kf4.Algebra\n"
            + f"/-! Generated by `Kf4/gen_kf4.py`: the `kf4` contract of `{NS}`.\n\n"
            + "* `kf4_run`: entry, rounds 1–23, round 24 (stores) and the exit;\n"
            + "* `kf4_spec`: KS holds the four states permuted, nothing outside KS is\n"
            + "  written, and the call's gas. -/\n\nnamespace" + rest_hdr
            + f"open {SHARED}.Proofs.Kf4\n\ntheorem kf4_run" + pre + "/-- **`kf4`.**" + spec)
    return alg, main


def emit_round_W(nm):
    arms = []
    for i in range(25):
        arms.append(f"  · show {nm}{i} Ops256 (Wv S) (gD0 Ops256 (Wv S)) (gD1 Ops256 (Wv S)) (gD2 Ops256 (Wv S)) "
                    f"(gD3 Ops256 (Wv S)) (gD4 Ops256 (Wv S)) (W fun _ => rc) = "
                    f"W fun k => cplU {i} (round (S k) rc)[{i}]!\n"
                    f"    rw [{nm}{i}_eq]\n    unfold Wv\n    rw [out{i // 5}{i % 5}_W]\n"
                    f"    exact W_congr fun k hk => slot{i // 5}{i % 5} (S k) (hS k hk) rc")
    return (f"theorem {nm}Round_W (S : Nat → Array UInt64) (hS : ∀ k, k < 4 → (S k).size = 25) (rc : UInt64) :\n"
            f"    {nm}Round Ops256 (Wv S) (W fun _ => rc) = Wv fun k => round (S k) rc := by\n"
            f"  funext i\n  fin_cases i\n" + "\n".join(arms) + "\n")


if __name__ == "__main__":
    recs, gD, gO, gL, rcs = analyse()
    RCS = rcs
    # last-round stores: cumulative per plane
    prev = []
    for rec in recs:
        if rec["kind"] == "plane" and rec["r"] == 23:
            rec["prev_stores"] = list(prev)
            prev = prev + [a for a in rec["stores_order"] if a not in prev]
            rec["stores_all"] = list(prev)
    print(len(recs), "blocks;", sum(r["cost"] for r in recs), "gas")
    if SET == "44":
        with open(os.path.join(OUT, "Model.lean"), "w") as f:
            f.write(emit_model(gD, gO, gL))
    else:
        # the kernel must compute the shared model's terms
        here = (gD, gO, gL)
        os.environ["GLAM_SET"] = "44"
        import importlib
        import gen_kf4 as K44
        importlib.reload(K44)
        _, gD44, gO44, gL44, _ = K44.analyse()
        assert (gD44, gO44, gL44) == here, "kernel differs from MlDsaOptGlam44's"
        os.environ["GLAM_SET"] = SET
    files = emit_blocks(recs, 3)
    files["Exit"] = [emit_exit(recs)]
    write_blocks(files)
    alg, main = split_main(emit_main(recs, rcs, sum(r["cost"] for r in recs)))
    if SET == "44":
        with open(os.path.join(OUT, "Algebra.lean"), "w") as f:
            f.write(alg)
    with open(os.path.join(OUT, "Main.lean"), "w") as f:
        f.write(main)
    with open(os.path.join(OUT, "Rounds.lean"), "w") as f:
        f.write("\n".join(f"import {NS}.Fn.Kf4.Blocks{k}" for k in range(8)) + f"""
/-! Generated by `Kf4/gen_kf4.py`: rounds 1–23 of `kf4` as `Reach` facts (theta
and the five planes chained); the lanes after round `r` are
`gORound Ops256 c (wd rc_r)`, and the round's dead D joins the junk. -/

namespace {P}.Kf4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Kf4 (Ops256 rot256 ldY stY)
open {SHARED}.Proofs.Kf4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
""" + HEADER + "\n" + emit_rounds(recs, rcs) + f"\nend {P}.Kf4\n")
