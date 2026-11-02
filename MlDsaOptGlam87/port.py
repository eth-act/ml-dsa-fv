#!/usr/bin/env python3
"""Re-port the v4 ML-DSA-87 proofs to the Glamsterdam bytes and apply the hand adjustments.

  python3 MlDsaOptGlam87/port.py

1. `scripts/proofgen_port.py --glam 87 --hand HAND FILES`: every v4 proof file of
   `MlDsaOpt87/` whose code is unchanged in `MlDsaOpt/87/glam/` (relocated indices
   and pcs, `glam65_rreach`, `MlDsaOptGlam87` namespaces; `MlDsaOpt44` names are
   kept) is written to `MlDsaOptGlam87/`;
2. the adjustments below.

The tree must be unchanged afterwards (the gate checks it). Files of
`MlDsaOptGlam87/` not listed in `FILES` are hand-written (`Layout`, `Budget`,
`Gas`, `Main.lean`, `Main/SegW.lean` (`intt` with UseHint fused, no `usehint`), `Main/S1/{Init,Tbl}` (glam 44's, no iota
tables, the 240-record table), the `Fn` wrappers `Keccak`, `Blk`, `Ntt`,
`Decode`, `Csum`) or generated (`Infra`, `Fn/Kf4`, `Fn/Kf1`).
"""
import os
import re
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
R = "MlDsaOptGlam87/"
# hand-written modules that replace a v4 module of the same name
HAND = r"Fn\.(?:Keccak|Blk|Ntt|Decode|Csum)|Main\.SegW|Main\.S1\.(?:Init|Tbl)|Gas|Main"

FILES = [
    "MlDsaOpt87/Fn/Ball.lean",
    "MlDsaOpt87/Fn/Ball/V4Blocks.lean",
    "MlDsaOpt87/Fn/Ball/V4Loop.lean",
    "MlDsaOpt87/Fn/Ball/V4Prologue.lean",
    "MlDsaOpt87/Fn/Ball/V4Proof.lean",
    "MlDsaOpt87/Fn/Ball/V4Scan.lean",
    "MlDsaOpt87/Fn/Decode/HintBlocks.lean",
    "MlDsaOpt87/Fn/Decode/HintLoop.lean",
    "MlDsaOpt87/Fn/Decode/HintMain.lean",
    "MlDsaOpt87/Fn/Fix.lean",
    "MlDsaOpt87/Fn/Fix/Blocks.lean",
    "MlDsaOpt87/Fn/Fix/GBlocks.lean",
    "MlDsaOpt87/Fn/Fix/Loop.lean",
    "MlDsaOpt87/Fn/Fix/Phase.lean",
    "MlDsaOpt87/Fn/Fix/Top.lean",
    "MlDsaOpt87/Fn/Ginit/Call.lean",
    "MlDsaOpt87/Fn/Ginit/Lanes.lean",
    "MlDsaOpt87/Fn/Group.lean",
    "MlDsaOpt87/Fn/GroupV4/Main.lean",
    "MlDsaOpt87/Fn/GroupV4/Squeeze.lean",
    "MlDsaOpt87/Fn/Hint.lean",
    "MlDsaOpt87/Fn/Hint/G5Pack.lean",
    "MlDsaOpt87/Fn/Hint/G5PackBlocks.lean",
    "MlDsaOpt87/Fn/Pass3f/P10.lean",
    "MlDsaOpt87/Fn/Pass3f/P14.lean",
    "MlDsaOpt87/Fn/Pass3f/P4.lean",
    "MlDsaOpt87/Fn/Pass3f/P6.lean",
    "MlDsaOpt87/Fn/Sponge.lean",
    "MlDsaOpt87/Fn/Sponge/Absorb.lean",
    "MlDsaOpt87/Fn/Sponge/Cext.lean",
    "MlDsaOpt87/Fn/Sponge/Spr.lean",
    "MlDsaOpt87/Fn/Sponge/TrabsRun.lean",
    "MlDsaOpt87/Fn/TBuild.lean",
    "MlDsaOpt87/Fn/TBuild/Blocks.lean",
    "MlDsaOpt87/Fn/TBuild/Run.lean",
    "MlDsaOpt87/Main/Base.lean",
    "MlDsaOpt87/Main/Exp/Acc.lean",
    "MlDsaOpt87/Main/Exp/Bound.lean",
    "MlDsaOpt87/Main/Exp/Compose.lean",
    "MlDsaOpt87/Main/Exp/G1013.lean",
    "MlDsaOpt87/Main/Exp/G1013/Defs.lean",
    "MlDsaOpt87/Main/Exp/G1013/Grp10.lean",
    "MlDsaOpt87/Main/Exp/G1013/Grp11.lean",
    "MlDsaOpt87/Main/Exp/G1013/Grp12.lean",
    "MlDsaOpt87/Main/Exp/G1013/Grp13.lean",
    "MlDsaOpt87/Main/Exp/G1013/Round.lean",
    "MlDsaOpt87/Main/Exp/G1013/Sponge.lean",
    "MlDsaOpt87/Main/Exp/G14.lean",
    "MlDsaOpt87/Main/Exp/Pure.lean",
    "MlDsaOpt87/Main/Exp/Round.lean",
    "MlDsaOpt87/Main/Exp/Sponge.lean",
    "MlDsaOpt87/Main/Frame.lean",
    "MlDsaOpt87/Main/Inv.lean",
    "MlDsaOpt87/Main/Mu/Blocks.lean",
    "MlDsaOpt87/Main/Mu/Proof.lean",
    "MlDsaOpt87/Main/Mu/Spec.lean",
    "MlDsaOpt87/Main/S1/Fin.lean",
    "MlDsaOpt87/Main/S1/FinBlocks.lean",
    "MlDsaOpt87/Main/S1/Rho.lean",
    "MlDsaOpt87/Main/S1/Tac.lean",
    "MlDsaOpt87/Main/SegCt.lean",
    "MlDsaOpt87/Main/SegExp.lean",
    "MlDsaOpt87/Main/SegFin.lean",
    "MlDsaOpt87/Main/SegInit.lean",
    "MlDsaOpt87/Main/SegMu.lean",
    "MlDsaOpt87/Main/SegNtt.lean",
    "MlDsaOpt87/Main/SegRho.lean",
    "MlDsaOpt87/Main/SegSib.lean",
    "MlDsaOpt87/Main/SegTbl.lean",
    "MlDsaOpt87/Main/SegZ.lean",
    "MlDsaOpt87/Main/SegZd.lean",
    "MlDsaOpt87/Main/Short.lean",
    "MlDsaOpt87/Main/Valid.lean",
]

subprocess.run([sys.executable, "scripts/proofgen_port.py", "--glam", "87", "--hand", HAND, *FILES],
               check=True, stdout=subprocess.DEVNULL)


def sub(path, old, new, count=1, regex=False):
    p = R + path
    s = open(p).read()
    if regex:
        s2, n = re.subn(old, new, s)
    else:
        n = s.count(old); s2 = s.replace(old, new)
    if n == 0 or (count and n != count):
        sys.exit(f'port.py: adjustment does not apply to {path}: {old[:60]!r} ({n})')
    open(p, 'w').write(s2)


# no iota tables: the init is the size check and the sizing store (0 … 15); the dz
# segment follows at 15, the 4 + 4 NTT's 240 records at 140 … 2059
sub('Main/Base.lean', """/-- `0 … 992`: size check, the sizing store and the `RC4` / `RC1` tables
(static cost; memory expansion to `memWords` is added by the trace). -/
def pInit : Nat := 658""", """/-- `0 … 15`: size check and the sizing store (static cost; memory expansion
to `memWords` is added by the trace).  -- glam: no iota tables -/
def pInit : Nat := 29""")
sub('Main/Base.lean', "def pTbl : Nat := 2232", "def pTbl : Nat := 2160  -- glam: the 240 records of the 4 + 4 NTT's table")

# UseHint is fused into `intt` (as v4 65): no `usehint` routine
p = R + 'Fn/Hint.lean'
t = open(p).read()
t = t.replace("import MlDsaOpt87.Fn.Hint.UseHint4\n", "")
i = t.index("/-- **usehint**")
j = t.index("/-- ", i + 10)
open(p, 'w').write(t[:i] + "-- glam: no `usehint` (UseHint is fused into `intt`)\n\n" + t[j:])

# iota tables are `True` here (glam 44's `RC4Table` / `RC1Table`)
TRIV = '  -- glam: no iota table'
for f in ['Main/Frame.lean', 'Fn/Fix/Top.lean']:
    sub(f, r"(RC[14]Table m' :=) fun i hi => by\n\s*rw \[[^\n]*\]; exact hr i hi",
        r"\1 trivial  -- glam: no iota table", count=0, regex=True)
sub('Fn/GroupV4/Squeeze.lean', "    RC4Table M' := fun i hi => by rw [FrameExcept.word h (ha i hi)]; exact hrc i hi",
    "    RC4Table M' := trivial  -- glam: no iota table")
for f, names in [('Main/Frame.lean', ['RC4Table.frame', 'RC1Table.frame']), ('Fn/Fix/Top.lean', ['rc4_frame']),
                 ('Fn/GroupV4/Squeeze.lean', ['rc4_frame'])]:
    for n in names:
        if f"-- glam: trivial table\ntheorem {n} " not in open(R + f).read():
            sub(f, f"theorem {n} ", f"set_option linter.unusedVariables false in  -- glam: trivial table\ntheorem {n} ")
# the sixth squeeze costs 282 + kf4 + blk (41122 here, 48362 in v4)
sub('Fn/Fix/Top.lean', '48362', '41122', count=0)
sub('Fn/Fix.lean', '(by unfold Gas.fixSq; omega)', '(by unfold Gas.fixSq Gas.kf4 Gas.blk; omega)', count=0)
# stack budgets with a 74-slot leaf: group = 266 (256 in v4)
sub('Fn/GroupV4/Main.lean', 'have e : Stack.group = 256 := by decide', 'have e : Stack.group = 266 := by decide', count=2)
sub('Fn/GroupV4/Main.lean', 'have htail : tail.length ≤ 768 := by', 'have htail : tail.length ≤ 758 := by', count=0)
# frame lemmas of the v4 predicates (`ZeroOn`, `CRep`, `SibFresh`, ...) by dot notation
sub('Main/Frame.lean', "import MlDsaOptGlam87.Main.Inv\n",
    "import MlDsaOptGlam87.Main.Inv\nimport MlDsaOpt87.Main.Frame  -- glam: frame lemmas of the shared v4 predicates\n"
    "import MlDsaOptGlam44.Main.Frame  -- glam: and of glam 44's tables (`TblAt`, `RC1Table`)\n")
# no `usehint` call: `pW` is provisional (the segment is package 2's, `Main/SegW.lean`)
sub('Main/Base.lean', "def pW : Nat := 120 + 2 * (intt + usehint + pack 4)",
    "def pW : Nat := 120 + 2 * (intt + pack 4)  -- glam: provisional, `intt` with UseHint fused")
# the final RETURN's pc
sub('Main/S1/Fin.lean', "    7560, [], M7, fun X hX hF", "    6497, [], M7, fun X hX hF")
sub('Fn/Ball/V4Proof.lean', r"(RC1Table M :=) fun i hi => by\n(?:  .*\n)*?  exact hrc i hi\n",
    r"\1 trivial  -- glam: no iota table\n", regex=True)
sub('Fn/Ball/V4Proof.lean', "theorem rc1_of_frame ",
    "set_option linter.unusedVariables false in  -- glam: trivial table\ntheorem rc1_of_frame ")
sub('Fn/Ball/V4Loop.lean', r"(  have hrc4 : RC1Table M4 :=) fun a ha => by\n    rw \[[^\n]*\]\n    exact hrc a ha\n",
    r"\1 trivial  -- glam: no iota table\n", regex=True)
sub('Fn/Ball/V4Scan.lean', r"\(fun a ha => by\n      rw \[f2\.word[^\n]*\n      exact hrc a ha\)",
    "trivial  -- glam: no iota table", regex=True)
