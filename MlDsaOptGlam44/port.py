#!/usr/bin/env python3
"""Re-port the v4 ML-DSA-44 proofs to the Glamsterdam bytes and apply the hand adjustments.

  python3 MlDsaOptGlam44/port.py

1. `scripts/proofgen_port.py --glam 44 FILES`: every v4 proof file of `MlDsaOpt44/`
   whose code is unchanged in `MlDsaOpt/44/glam/` (relocated indices and pcs,
   `glam44_rreach`, `MlDsaOptGlam44` namespaces) is written to `MlDsaOptGlam44/`;
2. the adjustments below (no iota tables, the 74-slot stack leaf, the sixth
   squeeze's cost, main-flow boundaries next to rewritten code, the
   long-message switch's `FLAG` in the packed path's invariants).

The tree must be unchanged afterwards (the gate checks it). Files of
`MlDsaOptGlam44/` not listed in `FILES` are hand-written (`Layout`, `Budget`,
`Gas`, `Main.lean`, `Main/{Base,Valid,SegMu,SegSwitch}`, `Main/{Init,Tbl}/*`,
`Fn/{Keccak,Blk,Ntt,Decode,Ct,Ball}.lean`) or generated (`Infra`, `Fn/Kf4`, `Fn/Kf1`).
"""
import os
import re
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
R = "MlDsaOptGlam44/"

FILES = [
    "MlDsaOpt44/Fn/Ct/TBuildBlocks.lean",
    "MlDsaOpt44/Fn/Ct/TBuildMath.lean",
    "MlDsaOpt44/Fn/Ct/TBuildRun.lean",
    "MlDsaOpt44/Fn/Decode/HintBlocks.lean",
    "MlDsaOpt44/Fn/Decode/HintLoop.lean",
    "MlDsaOpt44/Fn/Decode/HintMain.lean",
    "MlDsaOpt44/Fn/Fix.lean",
    "MlDsaOpt44/Fn/Fix/Blocks.lean",
    "MlDsaOpt44/Fn/Fix/GBlocks.lean",
    "MlDsaOpt44/Fn/Fix/Loop.lean",
    "MlDsaOpt44/Fn/Fix/Phase.lean",
    "MlDsaOpt44/Fn/Fix/Top.lean",
    "MlDsaOpt44/Fn/Group.lean",
    "MlDsaOpt44/Fn/Group/Main.lean",
    "MlDsaOpt44/Fn/Group/Pass3f4.lean",
    "MlDsaOpt44/Fn/Group/Squeeze.lean",
    "MlDsaOpt44/Fn/Hint.lean",
    "MlDsaOpt44/Fn/Hint/PackBlocks.lean",
    "MlDsaOpt44/Fn/Hint/PackCode.lean",
    "MlDsaOpt44/Fn/Hint/PackIter.lean",
    "MlDsaOpt44/Fn/Hint/PackMain.lean",
    "MlDsaOpt44/Fn/Sponge.lean",
    "MlDsaOpt44/Fn/Sponge/Absorb.lean",
    "MlDsaOpt44/Fn/Sponge/Cext.lean",
    "MlDsaOpt44/Fn/Sponge/Ginit.lean",
    "MlDsaOpt44/Fn/Sponge/Kmove.lean",
    "MlDsaOpt44/Fn/Sponge/Lmerge.lean",
    "MlDsaOpt44/Fn/Sponge/Mub0.lean",
    "MlDsaOpt44/Fn/Sponge/Mub0Blocks.lean",
    "MlDsaOpt44/Fn/Sponge/Spr.lean",
    "MlDsaOpt44/Fn/Sponge/TrabsRun.lean",
    "MlDsaOpt44/Main/Ex/Round.lean",
    "MlDsaOpt44/Main/Fin/Blocks.lean",
    "MlDsaOpt44/Main/Fin/Proof.lean",
    "MlDsaOpt44/Main/Frame.lean",
    "MlDsaOpt44/Main/Inv.lean",
    "MlDsaOpt44/Main/Rho/Blocks.lean",
    "MlDsaOpt44/Main/Mu/Cext.lean",
    "MlDsaOpt44/Main/Mu/Long.lean",
    "MlDsaOpt44/Main/Mu/Proof.lean",
    "MlDsaOpt44/Main/SegCt.lean",
    "MlDsaOpt44/Main/SegFin.lean",
    "MlDsaOpt44/Main/SegG2.lean",
    "MlDsaOpt44/Main/SegGroups.lean",
    "MlDsaOpt44/Main/SegInit.lean",
    "MlDsaOpt44/Main/SegNtt.lean",
    "MlDsaOpt44/Main/SegRho.lean",
    "MlDsaOpt44/Main/SegSib.lean",
    "MlDsaOpt44/Main/SegTbl.lean",
    "MlDsaOpt44/Main/SegW.lean",
    "MlDsaOpt44/Main/SegWin.lean",
    "MlDsaOpt44/Main/SegZ.lean",
    "MlDsaOpt44/Main/SegZd.lean",
    "MlDsaOpt44/Main/Short.lean",
    "MlDsaOpt44/Main/Win/Math.lean",
    "MlDsaOpt44/Main/Win/PartB.lean",
    "MlDsaOpt44/Main/Win/PartC.lean",
    "MlDsaOpt44/Main/Win/PartD.lean",
    "MlDsaOpt44/Main/Win/PartE.lean",
    "MlDsaOpt44/Main/Win/States.lean",
]

subprocess.run([sys.executable, "scripts/proofgen_port.py", "--glam", "44", *FILES], check=True,
               stdout=subprocess.DEVNULL)

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
TRIV = '  -- glam: no iota table (`RC4Table` is `True`)\n'
# iota tables are `True` here
for f in ['Main/Frame.lean', 'Fn/Fix/Top.lean']:
    sub(f, r"(RC[14]Table m' :=) fun i hi => by\n\s*rw \[[^\n]*\]; exact hr i hi",
        r"\1 trivial  -- glam: no iota table", count=0, regex=True)
sub('Fn/Group/Squeeze.lean', "    RC4Table M' := fun i hi => by rw [FrameExcept.word h (ha i hi)]; exact hrc i hi",
    "    RC4Table M' := trivial  -- glam: no iota table")
for f, names in [('Main/Frame.lean', ['RC4Table.frame', 'RC1Table.frame']), ('Fn/Fix/Top.lean', ['rc4_frame']),
                 ('Fn/Group/Squeeze.lean', ['rc4_frame'])]:
    for n in names:
        if f"-- glam: trivial table\ntheorem {n} " not in open(R + f).read():
            sub(f, f"theorem {n} ", f"set_option linter.unusedVariables false in  -- glam: trivial table\ntheorem {n} ")
# frame lemmas of the v4 predicates (`ZeroOn`, `St4At`, `CRep`, `SibFresh`, ...) by dot notation
sub('Main/Frame.lean', "import MlDsaOptGlam44.Main.Inv\n",
    "import MlDsaOptGlam44.Main.Inv\nimport MlDsaOpt44.Main.Frame  -- glam: frame lemmas of the shared v4 predicates\n")
# the sixth squeeze costs 282 + kf4 + blk (41122 here, 48362 in v4)
sub('Fn/Fix/Top.lean', '48362', '41122', count=0)
sub('Fn/Fix.lean', '(by unfold Gas.fixSq; omega)', '(by unfold Gas.fixSq Gas.kf4 Gas.blk; omega)', count=0)
# stack budgets with a 74-slot leaf: group = 266 (256 in v4)
sub('Fn/Group/Main.lean', 'have e : Stack.group = 256 := by decide', 'have e : Stack.group = 266 := by decide', count=2)
sub('Fn/Group/Main.lean', 'have htail : tail.length ≤ 768 := by', 'have htail : tail.length ≤ 758 := by', count=0)
# ExpandA: the first two groups are shared; the long-message switch follows at 2436
sub('Main/SegGroups.lean', "(callState s 2452 [flag (b && okCol s.executionEnv.calldata 1)] m') Gas.pG1 := by",
    "(callState s 2436 [flag (b && okCol s.executionEnv.calldata 1)] m') Gas.pG1 := by  -- glam: switch at 2436")
# the shared code after ExpandA starts at `altj` (5081); the packed path reaches it from 3948
sub('Main/SegZd.lean', "callState s 3948 [flag b] m", "callState s 5081 [flag b] m", count=2)
sub('Main/SegZd.lean', "glam44_rreach [1347, 1702, 1703, 1704]", "glam44_rreach [1701, 1702, 1703, 1704]")
# the final RETURN's pc
sub('Main/Fin/Proof.lean', "bswapNet (word s.executionEnv.calldata 1312)), 6635, [], M7,",
    "bswapNet (word s.executionEnv.calldata 1312)), 6779, [], M7,")
# the long-message switch: the packed path's invariants carry `FLAG = 1`
def subonce(path, old, new):
    if new not in open(R + path).read():
        sub(path, old, new)
subonce('Main/Inv.lean', '''  tr : ∃ S : Nat → Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧ S 0 = absorbPre 136 (padPk cd) 5
''', '''  tr : ∃ S : Nat → Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧ S 0 = absorbPre 136 (padPk cd) 5
  /-- glam: the packed schedule (`|M| < 342`) is running. -/
  flag : word m FLAG = 1
''')
subonce('Main/Inv.lean', '''  sc : ScAt m cd
  zIdx : ZeroOn m IDX (IDX + 256)
  zNeg : ZeroOn m NNEG (NNEG + 64)

/-- After the side buffers are zeroed and the hints decoded. -/''', '''  sc : ScAt m cd
  zIdx : ZeroOn m IDX (IDX + 256)
  zNeg : ZeroOn m NNEG (NNEG + 64)
  /-- glam: the packed schedule (`|M| < 342`) ran. -/
  flag : word m FLAG = 1

/-- After the side buffers are zeroed and the hints decoded. -/''')
subonce('Main/Inv.lean', '''  fresh : SibFresh m
  fmu : FinMu m cd
''', '''  fresh : SibFresh m
  fmu : FinMu m cd
  /-- glam: the packed schedule (`|M| < 342`) ran. -/
  flag : word m FLAG = 1
''')
# seg_g2 starts after the switch stored FLAG = 1
subonce('Main/SegG2.lean', '''    (hI : InvG1 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG2 s.executionEnv.calldata m' ∧''', '''    (hI : InvG1 s.executionEnv.calldata m) (b : Bool) (hfl : word m FLAG = 1) :
    ∃ m', InvG2 s.executionEnv.calldata m' ∧''')
subonce('Main/SegG2.lean', "refine ⟨MachineState.writeBytes m7 (MachineState.readPadded m7 ABUF 8192) SB, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩",
    "refine ⟨MachineState.writeBytes m7 (MachineState.readPadded m7 ABUF 8192) SB, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩, ?_⟩")
subonce('Main/SegG2.lean', '''  · have hR := ((((((((hR1.trans hR2).trans hR3)''', '''  · -- glam: `FLAG`
    rw [word_frame (FrameExcept.trans hfB (FrameExcept.mcopy m7 ABUF SB 8192)) (lo := FLAG) (hi := FLAG + 32)
      (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl
  · have hR := ((((((((hR1.trans hR2).trans hR3)''')
subonce('Main/SegWin.lean', '''hI.zIdx.frame hfX (by avoids_tac), hI.zNeg.frame hfX (by avoids_tac)⟩, ?_⟩''',
    '''hI.zIdx.frame hfX (by avoids_tac), hI.zNeg.frame hfX (by avoids_tac),
    by rw [word_frame hfX (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
       exact hI.flag⟩, ?_⟩''')
subonce('Main/SegZd.lean', '''    hI.zNeg.frame hfr (by avoids_tac)⟩, ⟨hh1, hh2⟩,''', '''    hI.zNeg.frame hfr (by avoids_tac),
    by rw [word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
       exact hI.flag⟩, ⟨hh1, hh2⟩,''')
subonce('Main/SegSib.lean', '''      rw [this, hS0]; rfl)
    hI.fresh
''', '''      rw [this, hS0]; rfl)
    hI.fresh hI.flag
''')
# the boundary table in Glamsterdam pcs
p = R + 'Main/Inv.lean'; s = open(p).read()
i = s.find('| boundary | pc | stack | invariant |'); j = s.find('with `ok2 = (okZ ∧ okA) ∧ okH`')
if i >= 0 and 'switch' not in s[i:j]:
    s = s[:i] + """| boundary | pc | stack | invariant |
|---|---|---|---|
| sized (no iota tables) | 15 | `[]` | `Inv0` |
| z | 99 | `[okZ]` | `Inv1` |
| NTT records (4 + 4 table) | 2018 | `[okZ]` | `Inv2` |
| ẑ | 2028 | `[okZ]` | `Inv3` |
| ρ spread | 2389 | `[okZ]` | `Inv4` |
| group 0 (`CW` = column 0) | 2412 | `[okZ ∧ A·0]` | `InvG0` |
| group 1 (`HP` = column 1); the long-message switch | 2436 | `[… ∧ A·1]` | `InvG1` |
| packed: group 2 (`SB` = column 2, rows 0 … 2; tr) | 2850 | `[… ∧ A₀₋₂,2]` | `InvG2` |
| packed: Â ẑ, tr, c̃ stream, μ's / c's states | 3948 (→ 5081) | `[okZ ∧ okA]` | `InvW` |
| hints | 5183 | `[… ∧ okH]` | `InvH` |
| μ | 6020 | `[… ∧ okH]` | `Inv6` |
| c | 6030 | `[ok3]` | `Inv7` |
| c · t1 | 6057 | `[ok3]` | `Inv8` |
| w1Encode | 6084 | `[ok3]` | `Inv9` |

`InvG2`, `InvW` (and `InvH`), `Inv6` hold on the packed schedule (`|M| < 342`)
and carry `FLAG = 1` (glam); the long-message schedule reaches `Inv7` by its
own path (`seg_alt`).

""" + s[j:]
    s = s.replace('# Main-flow invariants (v4)', '# Main-flow invariants (v4, Glamsterdam pcs)')
    open(p, 'w').write(s)

# μ on the packed schedule: four blocks read `FLAG` (the bound `0x10fa − 0x220 · FLAG`, the
# `hash_mu` entry test); `FLAG = 1` comes from `InvH`
G = '  have hfl\' : word M 3936 = 1 := hfl  -- glam: `FLAG`\n'
sub('Main/Mu/Long.lean', """    (hl : 3802 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 5183 [flag b] M) (callState s 5486 [flag b] M) 24 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [1746, 1752, 1753, 1754, 1755, 1756]""", """    (hl : 3802 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 1) :
    Reach (callState s 5183 [flag b] M) (callState s 5486 [flag b] M) 41 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
""" + G + """  glam44_rreach [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756] with [hfl']""")
sub('Main/Mu/Long.lean', """    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5183 [flag b] M) (callState s 6020 [flag b] M') 195 := by
""", """    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) (hfl : word M FLAG = 1) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5183 [flag b] M) (callState s 6020 [flag b] M') 212 := by
""" + G)
sub('Main/Mu/Long.lean', "  · glam44_rreach [1746, 1752, 1753, 1754, 1755, 1756, 1757,",
    "  · glam44_rreach [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757,")
sub('Main/Mu/Long.lean', "] with [word_mstore_disjoint]\n    rfl", "] with [word_mstore_disjoint, hfl']\n    rfl")
sub('Main/Mu/Long.lean', """theorem mu_cpy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5486 [flag b] M) (callState s 5503 [wd KS, wd SC, wd 800, flag b] M) 9 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [1807, 1813, 1814, 1815] with [KS, SC]""", """theorem mu_cpy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 1) :
    Reach (callState s 5486 [flag b] M) (callState s 5503 [wd KS, wd SC, wd 800, flag b] M) 31 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
""" + G + """  glam44_rreach [1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815] with [KS, SC, hfl']""")
sub('Main/Mu/Long.lean', """theorem mu_abs1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5783 [flag b] M)
      (callState s 7000 [wd 3802, wd 5803, wd 3802, flag b] M) 20 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [1983, 1989, 1990, 1991, 1992]""", """theorem mu_abs1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 1) :
    Reach (callState s 5783 [flag b] M)
      (callState s 7000 [wd 3802, wd 5803, wd 3802, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
""" + G + """  glam44_rreach [1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992] with [hfl']""")
sub('Main/Mu/Long.lean', """    (hl : 3802 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 5803 [wd 3802, flag b] M)
      (callState s 5821 [wd (s.executionEnv.calldata.size - 3802), wd 3938, flag b] M) 15 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [1993, 1994, 1995, 1996, 2002, 2003]""", """    (hl : 3802 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 1) :
    Reach (callState s 5803 [wd 3802, flag b] M)
      (callState s 5821 [wd (s.executionEnv.calldata.size - 3802), wd 3938, flag b] M) 32 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
""" + G + """  glam44_rreach [1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003] with [hfl']""")
sub('Main/Mu/Proof.lean', """    {m : ByteArray} (hsc : ScAt m s.executionEnv.calldata) (hrc : RC1Table m)
    (hl : 3802 ≤ s.executionEnv.calldata.size) :""", """    {m : ByteArray} (hsc : ScAt m s.executionEnv.calldata) (hrc : RC1Table m)
    (hl : 3802 ≤ s.executionEnv.calldata.size) (hfl : word m FLAG = 1) :""")
sub('Main/Mu/Proof.lean', "wd (3802 + 136 * 1), flag b] M) (24 + 667 + Gas.cext 25 + Gas.absorb17) := by",
    "wd (3802 + 136 * 1), flag b] M) (41 + 723 + Gas.cext 25 + Gas.absorb17) := by")
sub('Main/Mu/Proof.lean', "  have r0 := mu_chk_long hs b m hfit hl\n  have r1 := mu_cpy hs b m\n",
    "  have r0 := mu_chk_long hs b m hfit hl hfl\n  have r1 := mu_cpy hs b m hfl\n")
sub('Main/Mu/Proof.lean', "  have r3 := mu_abs1 hs b m6\n", """  have hfl6 : word m6 FLAG = 1 := by  -- glam: `FLAG`
    rw [word_frame ((hf1.trans hf2).trans hAD.2) (lo := FLAG) (hi := FLAG + 32)
      (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl
  have r3 := mu_abs1 hs b m6 hfl6
""")
sub('Main/Mu/Proof.lean', "  have r4 := mu_head0 hs b m7 hfit hl\n", """  have hfl7 : word m7 FLAG = 1 := by  -- glam: `FLAG`
    rw [word_frame hf7 (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl6
  have r4 := mu_head0 hs b m7 hfit hl hfl7
""")
