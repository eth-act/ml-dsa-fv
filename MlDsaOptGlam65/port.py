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
`Gas`, `Main.lean`, `Main/SegExp.lean`, `Main/SegMu.lean` (v4's statements, open items),
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
HAND = r"Fn\.(?:Keccak|Blk|Ntt|Decode|Csum)|Fn\.Csum\.(?:Blocks|Iter)|Main\.SegExp|Main\.SegMu|Main\.S1\.(?:Init|Tbl)|Gas|Main"

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

# `mub` is unreachable in glam 65 (the 42-call schedule squeezes μ once: `mub0`, then
# `hash_mu` from the state image `MUIMG`): no `mub` contract
sub('Fn/Sponge.lean', "import MlDsaOpt65.Fn.Sponge.Mub\n", "")
p = R + 'Fn/Sponge.lean'
t = open(p).read()
i = t.index("/-- **mub**: `[136 k, sh, ret]`")
j = t.index("\nend MlDsaOptGlam65.Proofs")
open(p, 'w').write(t[:i].rstrip("\n") + "\n\n-- glam: no `mub` (unreachable in the 42-call schedule)\n" + t[j:])

# μ in the 42-call schedule: one squeeze (block 0, `mub0`); `MU` holds μ for one-block
# messages, the state image `MUIMG` (saved after the last call) has μ's sponge after block 0
sub('Main/Inv.lean', """/-- μ (8 lanes) in `MU` for messages of at most five blocks (v4: group 8's μ
slot, `mub`). -/
def MuAt (m : ByteArray) (cd : ByteArray) : Prop :=
  mlenOf cd ≤ 613 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)""",
    """/-- μ (8 lanes) in `MU` for one-block messages (`|M| ≤ 69`; the window's
`cext [MU, 2, 8]` after the last call).  -- glam -/
def MuAt (m : ByteArray) (cd : ByteArray) : Prop :=
  mlenOf cd ≤ 69 → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)""")
sub('Main/Inv.lean', """/-- For longer messages μ's sponge after blocks `0 … 4` is slot 2 of `KS`. -/
def MuKs (m : ByteArray) (cd : ByteArray) : Prop :=
  613 < mlenOf cd → ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ KS4 m S ∧
    S 2 = MlDsaOpt44.Proofs.absorbPre 136 (padMu cd) 5""",
    """/-- μ's sponge after block 0 is slot 2 of the state image at `MUIMG` (saved after
the 42-call schedule's last call; `hash_mu` restores it).  -- glam -/
def MuKs (m : ByteArray) (cd : ByteArray) : Prop :=
  ∃ S : Nat → MlDsa44.Fips202.SpongeState, Sized4 S ∧ MlDsaOpt44.Proofs.St4At m MUIMG S ∧
    S 2 = MlDsaOpt44.Proofs.absorbPre 136 (padMu cd) 1""")
sub('Main/SegZd.lean', """    fun hl => by
      obtain ⟨S, hS, hks, h2⟩ := hI.muks hl
      exact ⟨S, hS, fun x hx => by
        rw [word_frame hfr (lo := KS) (hi := KS + 800) (by avoids_tac) (by omega) (by omega)]
        exact hks x hx, h2⟩,""", """    by  -- glam: the state image at `MUIMG`
      obtain ⟨S, hS, hks, h2⟩ := hI.muks
      exact ⟨S, hS, fun x hx => by
        rw [word_frame hfr (lo := MUIMG) (hi := MUIMG + 800) (by unfold MUIMG; avoids_tac) (by omega) (by omega)]
        exact hks x hx, h2⟩,""")

# `fix` and `gfix` keep the flag words 0 … 34; `gfix` keeps the other slots' lanes of
# candidates 0 … 279 when block 4's tail already holds the kf4 state's words (the
# window's `gfix 12` before KX's `lmerge` and the copy of block 4)
for f in ['Fn/Fix.lean']:
    sub(f, """      KS4 m' S ∧ word m' HAVE6 = word m HAVE6 ∧ FrameExcept m m' fixRegions := by""",
        """      KS4 m' S ∧ word m' HAVE6 = word m HAVE6 ∧ FrameExcept m m' fixRegions ∧
      (∀ g, g < 35 → word m' (FL + 32 * g) = word m (FL + 32 * g)) := by  -- glam""")
    sub(f, """    fun sl' h1 h2 t _ => hl sl' h1 h2 t, Fix.ks4_frame hks hL.1 (by fx_av), hH, hL.1.mono ?_⟩""",
        """    fun sl' h1 h2 t _ => hl sl' h1 h2 t, Fix.ks4_frame hks hL.1 (by fx_av), hH, hL.1.mono ?_,
    fun g _ => hFL g⟩""")
    sub(f, """      KS4 m' S ∧ word m' HAVE6 = 1 ∧ FrameExcept m m' fixRegions := by""",
        """      KS4 m' S ∧ word m' HAVE6 = 1 ∧ FrameExcept m m' fixRegions ∧
      (∀ g, g < 35 → word m' (FL + 32 * g) = word m (FL + 32 * g)) := by  -- glam""")
    sub(f, "  refine ⟨fun sl' I' h1 h2 hp => ?_, hlo, ?_, hH, ?_⟩", "  refine ⟨fun sl' I' h1 h2 hp => ?_, hlo, ?_, hH, ?_, hFL⟩")
    sub(f, "obtain ⟨hpend, hlo, hks', hH, hfr⟩ := post_", "obtain ⟨hpend, hlo, hks', hH, hfr, hFLk⟩ := post_", count=3)
    sub(f, """        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      KS4 m' S ∧ (word m HAVE6 ≠ 0 → word m' HAVE6 ≠ 0) ∧""",
        """        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      (∀ g, g < 35 → word m' (FL + 32 * g) = word m (FL + 32 * g)) ∧  -- glam
      KS4 m' S ∧ (word m HAVE6 ≠ 0 → word m' HAVE6 ≠ 0) ∧""")
    sub(f, "hval, hpend, hlo, hks',", "hval, hpend, hlo, hFLk, hks',", count=3)
    sub(f, "omega), hpend, hlo, hks',", "omega), hpend, hlo, hFLk, hks',", count=2)
    sub(f, "obtain ⟨M', hval, hpend', hlanes', hks', hmono, hfr', hcl⟩ := fix_call",
        "obtain ⟨M', hval, hpend', hlanes', hfl', hks', hmono, hfr', hcl⟩ := fix_call", count=2)
sub('Fn/Fix.lean', """  keep : ∀ j, j < 4 → amask.testBit j = false → ∀ t', t' < 256 →
    lane (word M (ABUF + 32 * t')) j = lane (word m (ABUF + 32 * t')) j
""", """  keep : ∀ j, j < 4 → amask.testBit j = false → ∀ t', t' < 256 →
    lane (word M (ABUF + 32 * t')) j = lane (word m (ABUF + 32 * t')) j
  -- glam: with block 4's tail in place, inactive lanes of candidates < 280 and flag words < 35 kept
  keepB : ((∀ i, 32 ≤ i → i < 56 → word m (ABUF + 1792 * 4 + 32 * i) = pack4 fun k => cand (S k) i) ∧
      (∀ g, 4 ≤ g → g < 7 → word m (FL + 224 * 4 + 32 * g) = flagWord S g)) →
    (∀ j, j < 4 → amask.testBit j = false → ∀ t', t' < 280 →
      lane (word M (ABUF + 32 * t')) j = lane (word m (ABUF + 32 * t')) j) ∧
    ∀ g, g < 35 → word M (FL + 32 * g) = word m (FL + 32 * g)
""")
sub('Fn/Fix.lean', """        fun j h1 h2 a ha t' ht' => ?_, fun j hj hna t' ht' => ?_⟩, _, ((((hcallT (hc1 0 (by omega))).trans hcT).trans""",
    """        fun j h1 h2 a ha t' ht' => ?_, fun j hj hna t' ht' => ?_, fun hB4 => ?_⟩, _,
        ((((hcallT (hc1 0 (by omega))).trans hcT).trans""")
sub('Fn/Fix.lean', """        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' (by omega),
          hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
""", """        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' (by omega),
          hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
      · -- glam: `blkt` rewrites block 4's tail with the words already there
        obtain ⟨hc4, hf4⟩ := hpostT S hS hI.ks
        have hA : ∀ t', t' < 280 → word MT (ABUF + 32 * t') = word M (ABUF + 32 * t') := fun t' ht' => by
          by_cases hlt : t' < 256
          · exact hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
          · rw [show ABUF + 32 * t' = ABUF + 1792 * 4 + 32 * (t' - 224) by simp only [ABUF]; omega,
              hc4 _ (by omega) (by omega), hB4.1 _ (by omega) (by omega)]
        have hF : ∀ g, g < 35 → word MT (FL + 32 * g) = word M (FL + 32 * g) := fun g hg => by
          by_cases hlt : g < 32
          · exact hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
          · rw [show FL + 32 * g = FL + 224 * 4 + 32 * (g - 28) by simp only [FL]; omega,
              hf4 _ (by omega) (by omega), hB4.2 _ (by omega) (by omega)]
        refine ⟨fun j hj hna t' ht' => ?_, fun g hg => by rw [hfl' g hg, hF g hg]⟩
        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' ht', hA t' ht']
""")
sub('Fn/Fix.lean', """        fun j h1 h2 a ha t' ht' => ?_, fun j hj hna t' ht' => ?_⟩, _, ((hcallF (hc1 1 (by omega))).trans hcl).trans""",
    """        fun j h1 h2 a ha t' ht' => ?_, fun j hj hna t' ht' => ?_, fun hB4 => ?_⟩, _,
        ((hcallF (hc1 1 (by omega))).trans hcl).trans""")
sub('Fn/Fix.lean', """        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' (by omega)]
        exact hI.keep j hj hna t' ht'
""", """        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' (by omega)]
        exact hI.keep j hj hna t' ht'
      · -- glam
        refine ⟨fun j hj hna t' ht' => ?_, fun g hg => by rw [hfl' g hg]; exact (hI.keepB hB4).2 g hg⟩
        rw [hlanes' j hj (by rintro rfl; rw [hact] at hna; exact absurd hna (by decide)) t' ht']
        exact (hI.keepB hB4).1 j hj hna t' ht'
""")
sub('Fn/Fix.lean', "      fun j h1 h2 a ha t' ht' => ?_, hI.keep⟩, sk, ?_, ?_⟩",
    "      fun j h1 h2 a ha t' ht' => ?_, hI.keep, hI.keepB⟩, sk, ?_, ?_⟩")
sub('Fn/Fix.lean', """        fun j hj => absurd hj (by omega), fun _ _ _ _ _ => rfl⟩""",
    """        fun j hj => absurd hj (by omega), fun _ _ _ _ _ => rfl, fun _ => ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩⟩""")
sub('Fn/Fix.lean', """      (∀ sl, sl < 4 → amask.testBit sl = false → ∀ t, t < 256 →
        lane (word m' (ABUF + 32 * t)) sl = lane (word m (ABUF + 32 * t)) sl) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.gfix""", """      (∀ sl, sl < 4 → amask.testBit sl = false → ∀ t, t < 256 →
        lane (word m' (ABUF + 32 * t)) sl = lane (word m (ABUF + 32 * t)) sl) ∧
      -- glam: with block 4's tail in place, the inactive lanes of candidates `< 280` and the flag words `< 35`
      (((∀ i, 32 ≤ i → i < 56 → word m (ABUF + 1792 * 4 + 32 * i) = pack4 fun k => cand (S k) i) ∧
          (∀ g, 4 ≤ g → g < 7 → word m (FL + 224 * 4 + 32 * g) = flagWord S g)) →
        (∀ sl, sl < 4 → amask.testBit sl = false → ∀ t, t < 280 →
          lane (word m' (ABUF + 32 * t)) sl = lane (word m (ABUF + 32 * t)) sl) ∧
        ∀ g, g < 35 → word m' (FL + 32 * g) = word m (FL + 32 * g)) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.gfix""")
sub('Fn/Fix.lean', "    refine ⟨m, fun sl hsl hact => (hall sl hsl hact).2, hks, fun _ _ _ _ _ => rfl,",
    "    refine ⟨m, fun sl hsl hact => (hall sl hsl hact).2, hks, fun _ _ _ _ _ => rfl,\n"
    "      fun _ => ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩,")
sub('Fn/Fix.lean', "    refine ⟨M4, fun sl hsl hact => hI4.done sl hsl hact, hI4.ks, hI4.keep, hI4.fr, ?_⟩",
    "    refine ⟨M4, fun sl hsl hact => hI4.done sl hsl hact, hI4.ks, hI4.keep, hI4.keepB, hI4.fr, ?_⟩")
sub('Fn/GroupV4/Main.lean', "obtain ⟨m8, hpost8, -, hkeep8, hf8, hc8⟩ := MlDsaOptGlam65.Proofs.gfix_call",
    "obtain ⟨m8, hpost8, -, hkeep8, -, hf8, hc8⟩ := MlDsaOptGlam65.Proofs.gfix_call")

# μ in the 42-call schedule: one-block messages from `MU`, else `hash_mu` from block 1 (exact)
sub('Main/Base.lean', """/-- `5356 … 5843`: μ, from `MU` (`|M| ≤ 613`, 195) or by `kf1` from slot 2's
state (`hash_mu`): selection 24, setup (`cext 25`, replication, block 5) 6884,
one loop visit (`kf1` + `absorb17` + 88) per further 136 bytes plus one, the
final permutation (`kf1` + 202). -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 613 then 195
  else 24 + 6884 + ((mlen - 614) / 136 + 1) * (kf1 + absorb17 + 88) + (kf1 + 202)""",
    """/-- `5017 … 5843`: μ, from `MU` (`|M| ≤ 69`, 195) or by `kf1` from μ's sponge after
block 0, slot 2 of the state image `MUIMG` (`hash_mu`): selection 24, setup 6971
(`MCOPY` to `KS` 87, `cext 25` 5167, replication 522, block 1's `absorb17` 1195),
one loop visit (`kf1` + `absorb17` + 88) per further full block (`⌊(|M| + 66) / 136⌋ - 1`
of them), the padded last block and the final permutation (`kf1` + 225).  -- glam: exact -/
def pMu (mlen : Nat) : Nat :=
  if mlen ≤ 69 then 195
  else 24 + 6971 + (mlen - 70) / 136 * (kf1 + absorb17 + 88) + (kf1 + 225)""")

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
