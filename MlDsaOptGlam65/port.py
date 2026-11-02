#!/usr/bin/env python3
"""Re-port the v4 ML-DSA-65 proofs to the Glamsterdam bytes and apply the hand adjustments.

  python3 MlDsaOptGlam65/port.py

1. `scripts/proofgen_port.py --glam 65 --hand HAND FILES`: every v4 proof file of
   `MlDsaOpt65/` whose code is unchanged in `MlDsaOpt/65/glam/` (relocated indices
   and pcs, `glam65_rreach`, `MlDsaOptGlam65` namespaces; `MlDsaOpt44` names are
   kept) is written to `MlDsaOptGlam65/`;
2. the adjustments below.

The tree must be unchanged afterwards (the gate checks it). Files of
`MlDsaOptGlam65/` not listed in `FILES` are hand-written (`Layout`, `Budget`,
`Gas`, `Main.lean`, `Main/SegExp.lean`, `Fn/Sponge/Mub.lean`, `Main/SegMu.lean` (v4's statements, open items),
`Main/S1/{Init,Tbl}` (glam 44's, no iota
tables, the 240-record table), the `Fn` wrappers `Keccak`, `Blk`, `Ntt`,
`Decode`, `Csum`) or generated (`Infra`, `Fn/Kf4`, `Fn/Kf1`).
"""
import os
import re
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
R = "MlDsaOptGlam65/"
# hand-written modules that replace a v4 module of the same name
HAND = r"Fn\.(?:Keccak|Blk|Ntt|Decode|Csum)|Fn\.Csum\.(?:Blocks|Iter)|Main\.SegExp|Fn\.Sponge\.Mub|Main\.SegMu|Main\.S1\.(?:Init|Tbl)|Gas|Main"

FILES = [
    "MlDsaOpt65/Fn/Csum/Main.lean",
    "MlDsaOpt65/Fn/Ball.lean",
    "MlDsaOpt65/Fn/Ball/V4Blocks.lean",
    "MlDsaOpt65/Fn/Ball/V4Loop.lean",
    "MlDsaOpt65/Fn/Ball/V4Proof.lean",
    "MlDsaOpt65/Fn/Ball/V4Run.lean",
    "MlDsaOpt65/Fn/Ball/V4Scan.lean",
    "MlDsaOpt65/Fn/Decode/HintBlocks.lean",
    "MlDsaOpt65/Fn/Decode/HintLoop.lean",
    "MlDsaOpt65/Fn/Decode/HintMain.lean",
    "MlDsaOpt65/Fn/Fix.lean",
    "MlDsaOpt65/Fn/Fix/Blocks.lean",
    "MlDsaOpt65/Fn/Fix/GBlocks.lean",
    "MlDsaOpt65/Fn/Fix/Loop.lean",
    "MlDsaOpt65/Fn/Fix/Phase.lean",
    "MlDsaOpt65/Fn/Fix/Top.lean",
    "MlDsaOpt65/Fn/Ginit/Call.lean",
    "MlDsaOpt65/Fn/Ginit/Lanes.lean",
    "MlDsaOpt65/Fn/Group.lean",
    "MlDsaOpt65/Fn/GroupV4/Main.lean",
    "MlDsaOpt65/Fn/GroupV4/Squeeze.lean",
    "MlDsaOpt65/Fn/Hint.lean",
    "MlDsaOpt65/Fn/Hint/G5Pack.lean",
    "MlDsaOpt65/Fn/Hint/G5PackBlocks.lean",
    "MlDsaOpt65/Fn/Sponge.lean",
    "MlDsaOpt65/Fn/Sponge/Absorb.lean",
    "MlDsaOpt65/Fn/Sponge/Cext.lean",
    "MlDsaOpt65/Fn/Sponge/Mub0.lean",
    "MlDsaOpt65/Fn/Sponge/Mub0Blocks.lean",
    "MlDsaOpt65/Fn/Sponge/Spr.lean",
    "MlDsaOpt65/Fn/Sponge/TrabsRun.lean",
    "MlDsaOpt65/Fn/TBuild.lean",
    "MlDsaOpt65/Fn/TBuild/Blocks.lean",
    "MlDsaOpt65/Fn/TBuild/Run.lean",
    "MlDsaOpt65/Main/Base.lean",
    "MlDsaOpt65/Main/Frame.lean",
    "MlDsaOpt65/Main/Inv.lean",
    "MlDsaOpt65/Main/Mu/Spec.lean",
    "MlDsaOpt65/Main/S1/Fin.lean",
    "MlDsaOpt65/Main/S1/FinBlocks.lean",
    "MlDsaOpt65/Main/S1/Rho.lean",
    "MlDsaOpt65/Main/SegCt.lean",
    "MlDsaOpt65/Main/SegFin.lean",
    "MlDsaOpt65/Main/SegInit.lean",
    "MlDsaOpt65/Main/SegNtt.lean",
    "MlDsaOpt65/Main/SegRho.lean",
    "MlDsaOpt65/Main/SegSib.lean",
    "MlDsaOpt65/Main/SegTbl.lean",
    "MlDsaOpt65/Main/SegW.lean",
    "MlDsaOpt65/Main/SegZ.lean",
    "MlDsaOpt65/Main/SegZd.lean",
    "MlDsaOpt65/Main/Short.lean",
    "MlDsaOpt65/Main/Valid.lean",
]

subprocess.run([sys.executable, "scripts/proofgen_port.py", "--glam", "65", "--hand", HAND, *FILES],
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
# segment follows at 15, the 4 + 4 NTT's 240 records at 124 … 2043
sub('Main/Base.lean', """/-- `0 … 992`: size check, the sizing store and the `RC4` / `RC1` tables
(static cost; memory expansion to `memWords` is added by the trace). -/
def pInit : Nat := 658""", """/-- `0 … 15`: size check and the sizing store (static cost; memory expansion
to `memWords` is added by the trace).  -- glam: no iota tables -/
def pInit : Nat := 29""")
sub('Main/Base.lean', """/-- `1101 … 3084`: the 248 NTT zeta records. -/
def pTbl : Nat := 2232""", """/-- `124 … 2043`: the 240 records of the 4 + 4 NTT's table.  -- glam -/
def pTbl : Nat := 2160""")
sub('Main/Base.lean', "def pExp : Nat := 3623550",
    "def pExp : Nat := 3623550  -- glam: provisional (v4's), until the 42-call schedule's `seg_exp`")

# v4's fused passes `pass3f4` (gone) and `pass3f8` (rewritten): their contracts are the
# 42-call schedule's (`Fn/Pack65.lean`, package 3); `FusedPass` and `bz*` stay here
sub('Fn/Group.lean', "import MlDsaOpt65.Fn.Pass3f.P4\nimport MlDsaOpt65.Fn.Pass3f.P8\n", "")
p = R + 'Fn/Group.lean'
t = open(p).read()
i = t.index("/-- `pass3f4`: row group 0, columns 0 … 4")
j = t.index("\nend MlDsaOptGlam65.Proofs")
open(p, 'w').write(t[:i].rstrip("\n") + "\n\n-- glam: v4's `pass3f4` / `pass3f8` contracts are replaced by `Fn/Pack65.lean`\n" + t[j:])

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
sub('Main/Frame.lean', "import MlDsaOptGlam65.Main.Inv\n",
    "import MlDsaOptGlam65.Main.Inv\nimport MlDsaOpt65.Main.Frame  -- glam: frame lemmas of the shared v4 predicates\n"
    "import MlDsaOptGlam44.Main.Frame  -- glam: and of glam 44's tables (`TblAt`, `RC1Table`)\n")
# the final RETURN's pc
sub('Main/S1/Fin.lean', "    7057, [], M7, fun X hX hF", "    6728, [], M7, fun X hX hF")

# csum: all τ = 49 window bases on the stack (`gen_csum.py 65` writes Fn/Csum/{Blocks,Iter})
p = R + 'Fn/Csum/Main.lean'
t = open(p).read()
i = t.index("theorem sW_toNat")
j = t.index("theorem wsum_cells")
es = "".join(f"  have e{x} : word m0 {49152 + 32 * x} = word M {49152 + 32 * x} := by simpa using hm0 {x} (by norm_num)\n"
             for x in range(49))
new = ("theorem sW_toNat (m0 M : ByteArray) (bu : Nat)  -- glam: all τ bases from the stack\n"
       "    (hm0 : ∀ i, i < 49 → word m0 (49152 + 32 * i) = word M (49152 + 32 * i)) :\n"
       "    (sW m0 M bu).toNat = wsum M bu 49 % 2 ^ 256 := by\n" + es +
       "  simp only [sW, ld0, ld1, ld2, bwOf, Nat.reduceMul, Nat.reduceAdd, "
       + ", ".join(f"e{x}" for x in range(49)) + "]\n"
       "  simp only [EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]\n"
       "  rw [wsum_tau]\n"
       "  simp only [W, Nat.reduceMul, Nat.reduceAdd]\n"
       "  apply congrArg (· % 2 ^ 256)\n"
       "  ring\n\n")
open(p, 'w').write(t[:i] + new + t[j:])
sub('Fn/Csum/Main.lean', "    ∀ i, i < 11 → word m (49152 + 32 * i) = word (stU m T S u).1 (49152 + 32 * i) := fun i hi => by",
    "    ∀ i, i < 49 → word m (49152 + 32 * i) = word (stU m T S u).1 (49152 + 32 * i) := fun i hi => by  -- glam")
sub('Fn/Csum/Main.lean', "have htail : tail.length ≤ 960 := by have := hr.depth",
    "have htail : tail.length ≤ 950 := by have := hr.depth")
sub('Fn/Csum/Main.lean', "only [csMem, word_mstore_disjoint, word_mstore]",
    "only [csMem, c4mem, word_mstore_disjoint, word_mstore]", count=4)
