#!/usr/bin/env python3
"""Generate `MlDsaOpt87/Fn/Ball/V4Blocks.lean`.

The skip / accept blocks are the ML-DSA-44 v4 ones (`MlDsaOpt44/Fn/Ball/V4Blocks.lean`
at 072c843, the version before `sibz`) shifted to the 87 instruction indices (+693) and
pcs (+1573), with the 87 `IDX` / `BASES` addresses; the head, `sibnok` and the fail exit
are 87-specific. Indices and costs from `MlDsaOpt87/listing.tsv`.

Usage: python3 MlDsaOpt87/Fn/Ball/gen_v4blocks.py   (from the repository root)
"""
import re, os, subprocess

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
T44 = subprocess.run(["git", "show", "072c843:MlDsaOpt44/Fn/Ball/V4Blocks.lean"], cwd=ROOT,
                     check=True, capture_output=True, text=True).stdout

lst = {}
for l in open(os.path.join(ROOT, "MlDsaOpt87/listing.tsv")):
    f = l.rstrip("\n").split("\t")
    if f[0] == "index":
        continue
    lst[int(f[0])] = (int(f[1]), f[2])

def gas(op):
    n = op.split()[0]
    if n == "JUMPDEST": return 1
    if n in ("POP", "PUSH0"): return 2
    if n.startswith("PUSH") or n.startswith("DUP") or n.startswith("SWAP"): return 3
    if n in ("ADD", "SUB", "LT", "GT", "EQ", "ISZERO", "AND", "OR", "XOR", "NOT", "SHL", "SHR",
             "MLOAD", "MSTORE", "MSTORE8", "CALLDATALOAD"): return 3
    if n in ("MUL", "DIV", "MOD"): return 5
    if n == "JUMP": return 8
    if n == "JUMPI": return 10
    raise ValueError(op)

def cost(ix): return sum(gas(lst[i][1]) for i in ix)
def rng(a, b): return list(range(a, b + 1))
def L(ix): return "[" + ", ".join(map(str, ix)) + "]"

# 44 -> 87 shifts for the shared skip/accept part
DI, DP = 693, 1573
assert lst[2734 + DI][0] == 7292 + DP

start = T44.index("theorem b_skip_rej1")
end = T44.index("theorem b_ext1")
body = T44[start:end]

def fix_list(m):
    xs = [int(x) + DI for x in m.group(1).split(",")]
    return "opt87_reach " + L(xs)
body = re.sub(r"opt44_reach \[([0-9, ]*)\]", fix_list, body)
for a in [7604, 7578, 7470] + [7292 + 24 * r for r in range(1, 8)]:
    body = re.sub(r"\b%d\b" % a, str(a + DP), body)
body = re.sub(r"\b43008\b", "51200", body)
body = re.sub(r"\b40928\b", "49120", body)
body = body.replace("2616 ≤ s.activeWords.toNat", "2897 ≤ s.activeWords.toNat")
body = body.replace("MlDsaOpt44.optBytecode", "MlDsaOpt87.optBytecode")
# check the reach costs of the copied part against the listing
for m in re.finditer(r"\) (\d+) := by\n(?:.*\n)*?\s*opt87_reach (\[[0-9, ]*\])", body):
    xs = [int(x) for x in m.group(2)[1:-1].split(",")]
    assert cost(xs) == int(m.group(1)), (m.group(1), cost(xs), xs[0])

PRE = '''import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# `sib` (v4, ML-DSA-87): straight-line blocks of the scan

Generated (`MlDsaOpt44/Fn/Ball/V4Blocks.lean` with the ML-DSA-87 pcs, indices,
`IDX`/`BASES` and the `kf1` head). Loop head `sibloop` (pc 8745), stack
`o :: i :: signs :: ret :: tail` (`o = 32 x` for stream lane `x`): `o = 1088` fails
(`b_fail`), `o = 544` squeezes the second block (`Fn/Ball/V4Prologue.lean`), otherwise
`b_nok` goes to `sibnok` (pc 8838), which loads the lane word `KS[o mod 544]` and tests
byte 0. Byte `r ≥ 1` of the lane is tested at `skipPc r` with `z :: w :: o :: …`
(`w` the lane word, `z` the previous byte or return label). An accepted byte calls the
shared accept step (`A`, `B` when `j` holds a nonzero coefficient, then `C` back to the
return label or `D` when all `τ` are placed).
-/

namespace MlDsaOpt87.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

'''
hdr_start = T44.index("theorem beNat_lt")
hdr_end = T44.index("/-- Pc of the test of byte")
helpers = T44[hdr_start:hdr_end]

H = "{s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)"
HAW = "  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small\n"

defs = '''/-- Pc of the test of byte `r` (`1 ≤ r ≤ 7`; `r = 8`: the lane epilogue). -/
def skipPc (r : Nat) : Nat := 8865 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 8745 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- `sibnok`: the lane load and the test of byte 0. -/
abbrev nokSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 8838 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 9043 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

'''

nok = rng(3352, 3363)
nokrej = rng(3409, 3422)
nokacc = rng(3409, 3426)
fail = rng(3352, 3357) + rng(3662, 3668)
assert lst[3409][0] == 8838 and lst[3427][0] == 8865 and lst[3546][0] == 9043
assert lst[3662][0] == 9252

new = f'''theorem b_nok {H}
    (o i sg : Nat) (ho : o < 1088) (ho' : o ≠ 544) :
    Reach (headSt s ret tail o i sg M) (nokSt s ret tail o i sg M) {cost(nok)} := by
{HAW}  opt87_reach {L(nok)}

theorem b_nok_rej {H} (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) {cost(nokrej)} := by
{HAW}  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  opt87_reach {L(nokrej)} with [ofNat_mod_ofNat, hw, hj, skipPc]

theorem b_nok_acc {H} (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (accSt s ret tail j 8865 w o i sg M) {cost(nokacc)} := by
{HAW}  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  opt87_reach {L(nokacc)} with [ofNat_mod_ofNat, hw, hj]

'''

tailtxt = f'''/-- The fail exit (`o = 1088`): return `0`. -/
theorem b_fail {H}
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) {cost(fail)} := by
{HAW}  opt87_reach {L(fail)} with [hjd]

end MlDsaOpt87.Proofs.Ball4
'''

out = PRE + helpers + defs + new + body + tailtxt
open(os.path.join(ROOT, "MlDsaOpt87/Fn/Ball/V4Blocks.lean"), "w").write(out)
print("costs: nok", cost(nok), "nokrej", cost(nokrej), "nokacc", cost(nokacc), "fail", cost(fail))
print("sq pre", cost(rng(3352, 3387)), "sq post", cost(rng(3388, 3408)), "post", cost(rng(3325, 3351)))
