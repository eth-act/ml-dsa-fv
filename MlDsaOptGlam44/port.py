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
    "MlDsaOpt44/Fn/Ct/Csum4Main.lean",
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

# csum: all 39 window bases on the stack (`Fn/Ct/gen_csum.py` writes the blocks and the loop)
sub('Fn/Ct/Csum4Main.lean', 'theorem s3_toNat (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256)\n    (hm0 : ∀ i, i < 11 → word m0 (40960 + 32 * i) = word M (40960 + 32 * i)) :\n    (s3 m0 M bu cw sp g).toNat = wsum M bu 39 % 2 ^ 256 := by\n  have e0 : word m0 40960 = word M 40960 := by simpa using hm0 0 (by norm_num)\n  have e1 : word m0 40992 = word M 40992 := by simpa using hm0 1 (by norm_num)\n  have e2 : word m0 41024 = word M 41024 := by simpa using hm0 2 (by norm_num)\n  have e3 : word m0 41056 = word M 41056 := by simpa using hm0 3 (by norm_num)\n  have e4 : word m0 41088 = word M 41088 := by simpa using hm0 4 (by norm_num)\n  have e5 : word m0 41120 = word M 41120 := by simpa using hm0 5 (by norm_num)\n  have e6 : word m0 41152 = word M 41152 := by simpa using hm0 6 (by norm_num)\n  have e7 : word m0 41184 = word M 41184 := by simpa using hm0 7 (by norm_num)\n  have e8 : word m0 41216 = word M 41216 := by simpa using hm0 8 (by norm_num)\n  have e9 : word m0 41248 = word M 41248 := by simpa using hm0 9 (by norm_num)\n  have e10 : word m0 41280 = word M 41280 := by simpa using hm0 10 (by norm_num)\n  simp only [s3, s2, s1, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]\n  simp only [c4s3, c4s2, c4s1, EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]\n  rw [wsum_39]\n  simp only [W, Nat.reduceMul, Nat.reduceAdd]\n  apply congrArg (· % 2 ^ 256)\n  ring\n\n', 'theorem s3_toNat (m0 M : ByteArray) (bu cw sp : Nat) (g : UInt256)\n    (hm0 : ∀ i, i < 39 → word m0 (40960 + 32 * i) = word M (40960 + 32 * i)) :\n    (s3 m0 M bu cw sp g).toNat = wsum M bu 39 % 2 ^ 256 := by\n  have e0 : word m0 40960 = word M 40960 := by simpa using hm0 0 (by norm_num)\n  have e1 : word m0 40992 = word M 40992 := by simpa using hm0 1 (by norm_num)\n  have e2 : word m0 41024 = word M 41024 := by simpa using hm0 2 (by norm_num)\n  have e3 : word m0 41056 = word M 41056 := by simpa using hm0 3 (by norm_num)\n  have e4 : word m0 41088 = word M 41088 := by simpa using hm0 4 (by norm_num)\n  have e5 : word m0 41120 = word M 41120 := by simpa using hm0 5 (by norm_num)\n  have e6 : word m0 41152 = word M 41152 := by simpa using hm0 6 (by norm_num)\n  have e7 : word m0 41184 = word M 41184 := by simpa using hm0 7 (by norm_num)\n  have e8 : word m0 41216 = word M 41216 := by simpa using hm0 8 (by norm_num)\n  have e9 : word m0 41248 = word M 41248 := by simpa using hm0 9 (by norm_num)\n  have e10 : word m0 41280 = word M 41280 := by simpa using hm0 10 (by norm_num)\n  have e11 : word m0 41312 = word M 41312 := by simpa using hm0 11 (by norm_num)\n  have e12 : word m0 41344 = word M 41344 := by simpa using hm0 12 (by norm_num)\n  have e13 : word m0 41376 = word M 41376 := by simpa using hm0 13 (by norm_num)\n  have e14 : word m0 41408 = word M 41408 := by simpa using hm0 14 (by norm_num)\n  have e15 : word m0 41440 = word M 41440 := by simpa using hm0 15 (by norm_num)\n  have e16 : word m0 41472 = word M 41472 := by simpa using hm0 16 (by norm_num)\n  have e17 : word m0 41504 = word M 41504 := by simpa using hm0 17 (by norm_num)\n  have e18 : word m0 41536 = word M 41536 := by simpa using hm0 18 (by norm_num)\n  have e19 : word m0 41568 = word M 41568 := by simpa using hm0 19 (by norm_num)\n  have e20 : word m0 41600 = word M 41600 := by simpa using hm0 20 (by norm_num)\n  have e21 : word m0 41632 = word M 41632 := by simpa using hm0 21 (by norm_num)\n  have e22 : word m0 41664 = word M 41664 := by simpa using hm0 22 (by norm_num)\n  have e23 : word m0 41696 = word M 41696 := by simpa using hm0 23 (by norm_num)\n  have e24 : word m0 41728 = word M 41728 := by simpa using hm0 24 (by norm_num)\n  have e25 : word m0 41760 = word M 41760 := by simpa using hm0 25 (by norm_num)\n  have e26 : word m0 41792 = word M 41792 := by simpa using hm0 26 (by norm_num)\n  have e27 : word m0 41824 = word M 41824 := by simpa using hm0 27 (by norm_num)\n  have e28 : word m0 41856 = word M 41856 := by simpa using hm0 28 (by norm_num)\n  have e29 : word m0 41888 = word M 41888 := by simpa using hm0 29 (by norm_num)\n  have e30 : word m0 41920 = word M 41920 := by simpa using hm0 30 (by norm_num)\n  have e31 : word m0 41952 = word M 41952 := by simpa using hm0 31 (by norm_num)\n  have e32 : word m0 41984 = word M 41984 := by simpa using hm0 32 (by norm_num)\n  have e33 : word m0 42016 = word M 42016 := by simpa using hm0 33 (by norm_num)\n  have e34 : word m0 42048 = word M 42048 := by simpa using hm0 34 (by norm_num)\n  have e35 : word m0 42080 = word M 42080 := by simpa using hm0 35 (by norm_num)\n  have e36 : word m0 42112 = word M 42112 := by simpa using hm0 36 (by norm_num)\n  have e37 : word m0 42144 = word M 42144 := by simpa using hm0 37 (by norm_num)\n  have e38 : word m0 42176 = word M 42176 := by simpa using hm0 38 (by norm_num)\n  simp only [s3, s2, s1, c4s3, c4s2, c4s1, bwOf, Nat.reduceMul, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38]\n  simp only [EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]\n  rw [wsum_39]\n  simp only [W, Nat.reduceMul, Nat.reduceAdd]\n  apply congrArg (· % 2 ^ 256)\n  ring\n\n')
sub('Fn/Ct/Csum4Main.lean', "∀ i, i < 11 → word m (40960 + 32 * i) = word (stU m u).1 (40960 + 32 * i)",
    "∀ i, i < 39 → word m (40960 + 32 * i) = word (stU m u).1 (40960 + 32 * i)")
sub('Fn/Ct/Csum4Main.lean', "only [csMem, word_mstore_disjoint, word_mstore]",
    "only [csMem, c4mem, word_mstore_disjoint, word_mstore]", count=4)
sub('Fn/Ct/Csum4Main.lean', "have htail : tail.length ≤ 960 := by have := hr.depth; simp only [Stack.csum, Stack.leaf] at this; omega",
    "have htail : tail.length ≤ 950 := by have := hr.depth; simp only [Stack.csum, Stack.leaf] at this; omega")

# glam (seg_alt): `seg_g0` / `seg_g1` keep `FLAG` (the long-message schedule needs `FLAG = 0`)
subonce('Main/SegGroups.lean', """    ∃ m', InvG0 s.executionEnv.calldata m' ∧
      Reach (callState s 2389""", """    ∃ m', InvG0 s.executionEnv.calldata m' ∧ word m' FLAG = word m FLAG ∧  -- glam: `FLAG` kept
      Reach (callState s 2389""")
subonce('Main/SegGroups.lean', """    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac), hc0⟩,
    hR.mono""", """    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac), hc0⟩,
    word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG groupFrame; avoids_tac) le_rfl le_rfl,
    hR.mono""")
subonce('Main/SegGroups.lean', """    ∃ m', InvG1 s.executionEnv.calldata m' ∧
      Reach (callState s 2412""", """    ∃ m', InvG1 s.executionEnv.calldata m' ∧ word m' FLAG = word m FLAG ∧  -- glam: `FLAG` kept
      Reach (callState s 2412""")
subonce('Main/SegGroups.lean', """    hI.c0.frame hfr (by unfold groupFrame; avoids_tac)⟩, hc1⟩,
    hR.mono""", """    hI.c0.frame hfr (by unfold groupFrame; avoids_tac)⟩, hc1⟩,
    word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG groupFrame; avoids_tac) le_rfl le_rfl,
    hR.mono""")
