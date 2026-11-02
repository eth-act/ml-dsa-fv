import MlDsaOpt87.Fn.Fix
import MlDsaOpt87.Fn.Ginit.Call
import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Fn.GroupV4.Squeeze
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Main.lean` by `scripts/proofgen_port.py 87` --path Fn/Group/=Fn/GroupV4/; hand adjustments are marked `-- port:`. -/
-- port: 87 = the 65 port relocated (group +728 pcs, +298 indices; callee entries); `amask`, `col < 8`, `rb < 2` symbolic (prologue and seeds from `Fn/Group/Seed.lean`,
-- `g1_b0` of the v3 port); inactive lanes kept by `gfix` (raw candidates below `2^23`).
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-65, v4): one pure ExpandA SIMD group

`HAVE6 := 0`, `ginit` with lane 4 computed in the prologue (`gL4`), five
`kf4` with `blk` (`blkh` for block 4), `gfix amask` (`SlotHead` from
`slotHead_of_blocks`; inactive lanes keep their raw candidates).
`group_call_aux` is `group_call` of `Fn/Group.lean`.
-/

namespace MlDsaOpt87.Proofs.GroupV4

open MlDsaOpt44.Proofs MlDsaOpt87.Proofs.GroupV4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt87.Proofs.Infra

theorem g_b0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 15188 (gB amask col rb ret tail) M)
      (callState s 13376 (wd (GroupP.gL4 amask col rb) :: wd 0 :: wd 15 :: wd 0 :: wd 15291 ::
        gB amask col rb ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have ha' : amask % 2 ^ 256 = amask := Nat.mod_eq_of_lt (by omega)
  have hc' : col % 2 ^ 256 = col := Nat.mod_eq_of_lt (by omega)
  have hr' : rb % 2 ^ 256 = rb := Nat.mod_eq_of_lt (by omega)
  opt87_reach [6813, 6814, 6815, 6816, 6817, 6818, 6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826,
    6827, 6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836, 6837, 6838, 6839, 6840, 6841, 6842,
    6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858,
    6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869] with [HAVE6, GroupP.gL4]

theorem g_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (15291 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 22277 (wd (15299 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6870, 6871, 6872, 6873]
  · opt87_reach [6880, 6881, 6882, 6883]
  · opt87_reach [6890, 6891, 6892, 6893]
  · opt87_reach [6900, 6901, 6902, 6903]
  · opt87_reach [6910, 6911, 6912, 6913]

theorem g_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 4 → ∀ M, Reach (callState s (15299 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 10992 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (15313 + 22 * b) ::
        gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6874, 6875, 6876, 6877, 6878, 6879] with [FL, ABUF]
  · opt87_reach [6884, 6885, 6886, 6887, 6888, 6889] with [FL, ABUF]
  · opt87_reach [6894, 6895, 6896, 6897, 6898, 6899] with [FL, ABUF]
  · opt87_reach [6904, 6905, 6906, 6907, 6908, 6909] with [FL, ABUF]

theorem g_L4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) : Reach (callState s (15299 + 22 * 4) (gB amask col rb ret tail) M)
      (callState s 12170 (wd (FL + 224 * 4) :: wd (ABUF + 1792 * 4) :: wd 15401 ::
        gB amask col rb ret tail) M) 21 := by
  opt87_reach [6914, 6915, 6916, 6917, 6918, 6919] with [FL, ABUF]

theorem g_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 15401 (gB amask col rb ret tail) M)
      (callState s 12966 (wd amask :: wd 15410 :: gB amask col rb ret tail) M) 18 := by
  opt87_reach [6920, 6921, 6922, 6923, 6924]

theorem g_E {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {amask col rb : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 15410 (ok :: gB amask col rb ret tail) M) (callState s ret (ok :: tail) M) 27 := by
  have := hr.depth
  have e : Stack.group = 256 := by decide
  have hret := hr.small
  have hj := hr.jumpdest
  opt87_reach [6925, 6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933] with [hj]

theorem pack4_lane {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] at hx ⊢
  omega

theorem pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

/-- Seed state of slot `k` of `group [amask, col, rb]`. -/
def gI (cd : ByteArray) (amask col rb k : Nat) : Fips202.SpongeState :=
  seedState 168 (aSeed cd (GroupP.gRow amask rb k) col)

/-- Raw candidate left in an inactive slot. -/
def gJunk (cd : ByteArray) (amask col rb r t : Nat) : Nat :=
  cand (permN (t / 56 + 1) (gI cd amask col rb r)) (t % 56)

theorem g_popcnt {amask : Nat} (ha : amask < 16) : popcnt amask ≤ 4 := by
  interval_cases amask <;> decide

theorem aI_gI {cd : ByteArray} (h32 : 32 ≤ cd.size) {amask col rb r : Nat}
    (hact : amask.testBit r = true) :
    MlDsaOpt44.Proofs.aI (gI cd amask col rb r) = aOf cd (4 * rb + r) col := by
  have h : MlDsaOpt44.Proofs.aI (seedState 168 (aSeed cd (4 * rb + r) col)) = aOf cd (4 * rb + r) col :=
    GroupP.aI_aSeed h32 (4 * rb + r) col
  have e : gI cd amask col rb r = seedState 168 (aSeed cd (4 * rb + r) col) := by
    unfold gI GroupP.gRow; rw [if_pos hact]
  rw [e]
  exact h

theorem g_slot {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb r : Nat) :
    (!amask.testBit r || (MlDsaOpt44.Proofs.aI (gI cd amask col rb r)).isSome) =
      (!amask.testBit r || (aOf cd (4 * rb + r) col).isSome) := by
  cases hact : amask.testBit r
  · simp only [Bool.not_false, Bool.true_or]
  · rw [aI_gI h32 hact]

theorem g_flag {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb : Nat) :
    ((List.range 4).all fun sl => !amask.testBit sl ||
        (MlDsaOpt44.Proofs.aI (gI cd amask col rb sl)).isSome) = gOk cd amask col rb := by
  unfold gOk
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.all_cons, List.all_nil, g_slot h32]

end MlDsaOpt87.Proofs.GroupV4

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt87.Proofs.Infra
open MlDsaOpt87.Proofs.GroupV4

/-- **group** (`group_call` of `Fn/Group.lean`; `gsFrame` is `groupFrame rb`). -/
theorem group_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (hamask : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => if amask.testBit r then
            ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t)) ∧
      FrameExcept m m' gsFrame ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group := by
  have htail : tail.length ≤ 768 := by
    have := hr.depth
    have e : Stack.group = 256 := by decide
    omega
  have hret := hr.small
  have h32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  clear hcd
  -- prologue: `HAVE6 := 0`, lane 4, `ginit`
  have hb0 := g_b0 hs (tail := tail) (by omega) hamask hcol hrb m (ret := ret)
  have hf1 := FrameExcept.mstore m HAVE6 0
  have h61 : word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) HAVE6 = 0 :=
    word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m2, hks2, hf2, hc2⟩ := MlDsaOpt87.Proofs.ginit_call hs (hr.callee (B' := Stack.ginit)
    (ret' := 15291) (extra := [wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide) (by simp only [isValidJumpDest_lit])
    (by norm_num))
    (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) (keep := 0) (amult := 15)
    (cmult := 0) (l4 := GroupP.gL4 amask col rb) (by norm_num) (by norm_num) (by norm_num)
    (GroupP.gL4_lt hamask hcol hrb)
  have hI : Sized4 (gI s.executionEnv.calldata amask col rb) := sized4_seedState 168 _
  have hinv0 : SqInv m m2 (gI s.executionEnv.calldata amask col rb) 0 := by
    refine ⟨fun x hx => ?_, rc4_frame hf2 (fun i hi => by grp_avoids)
      (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
      ?_, FrameExcept.of_avoid (hf1.trans hf2) (by grp_sub), fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩
    · rw [hks2 x hx, GroupP.gL4_eq hamask hcol hrb]
      exact GroupP.ginit_group (fun y hy => by
        rw [FrameExcept.word hf1 (by grp_avoids)]; exact hrho y hy)
        h32 (by omega) (fun k hk => Nat.lt_trans (GroupP.gRow_lt (amask := amask) hrb hk) (by norm_num)) hx
    · rw [FrameExcept.word hf2 (by grp_avoids)]; exact h61
  -- five squeezes
  obtain ⟨m6, hinv6, hR6⟩ := squeezes hs hr (amask := amask) (col := col) (rb := rb) hI hinv0
    (g_K hs (by omega)) (g_L hs (by omega))
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    4 le_rfl
  obtain ⟨m7, ⟨hks7, hrc7, h67, hfr7, hblk7⟩, hR7⟩ := squeeze_last hs hr (amask := amask) (col := col)
    (rb := rb) hI hinv6 (g_K hs (by omega) 4 (by omega) m6) (g_L4 hs (by omega))
    (by simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (by simp only [isValidJumpDest_lit])
  -- `gfix amask`
  obtain ⟨m8, hpost8, -, hkeep8, hf8, hc8⟩ := MlDsaOpt87.Proofs.gfix_call hs (hr.callee (B' := Stack.gfix)
    (ret' := 15410) (extra := [wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m7 hrc7 hamask 4 (g_popcnt hamask)
    (fun k => permN 5 (gI s.executionEnv.calldata amask col rb k)) (fun k hk => permN_size (hI k hk) 5) hks7
    (gI s.executionEnv.calldata amask col rb) h67
    (fun sl hsl _ => ⟨slotHead_of_blocks
      (St := fun b k => permN (b + 1) (gI s.executionEnv.calldata amask col rb k))
      hsl (fun _ _ => rfl) (fun b hb => (hblk7 b hb).1) (fun b hb => (hblk7 b hb).2), rfl⟩)
  rw [g_flag h32] at hc8
  refine ⟨m8, fun hall => ⟨gJunk s.executionEnv.calldata amask col rb,
    fun r t => cand_lt _ _, fun t ht => ?_⟩, FrameExcept.of_avoid (hfr7.trans hf8) (by grp_sub), ?_⟩
  · rw [← pack4_lane (word_lt m8 (ABUF + 32 * t))]
    apply pack4_congr
    intro r hr4
    by_cases hact : amask.testBit r = true
    · rw [if_pos hact]
      have hsome : (aOf s.executionEnv.calldata (4 * rb + r) col).isSome = true := by
        have h := List.all_eq_true.mp hall r (List.mem_range.mpr hr4)
        rw [hact] at h
        simpa using h
      obtain ⟨a, ha'⟩ := Option.isSome_iff_exists.mp hsome
      have hD : aD s.executionEnv.calldata (4 * rb + r) col = a := by unfold aD; rw [ha']; rfl
      rw [hD]
      exact hpost8 r hr4 hact a (by rw [aI_gI h32 hact]; exact ha') t ht
    · rw [if_neg hact, hkeep8 r hr4 (by simpa using hact) t ht]
      have hb : t / 56 < 5 := by omega
      rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
        (hblk7 _ hb).1 _ (Nat.mod_lt _ (by norm_num)) (by omega), lane_pack4_cand _ _ hr4]
      rfl
  · rw [call_iff, Entry.group]
    have h := (((((hb0.trans (call_iff.mp hc2)).trans hR6).trans hR7).trans
      (g_G hs (tail := tail) (by omega) m7)).trans (call_iff.mp hc8)).trans (g_E hs hr m8)
    refine (h.mono ?_).of_eq rfl rfl
    unfold Gas.group
    generalize Gas.ginit = a; generalize Gas.kf4 = b; generalize Gas.blk = c
    generalize Gas.blkh = d; generalize Gas.gfix 4 = e
    omega

end MlDsaOpt87.Proofs
