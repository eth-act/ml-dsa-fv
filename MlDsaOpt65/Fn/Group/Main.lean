import MlDsaOpt65.Fn.Group.Prologue
import MlDsaOpt65.Fn.Group.Blocks
import MlDsaOpt65.Fn.Group.Pass3
import MlDsaOpt65.Fn.Ginit.Call
import MlDsaOpt65.Fn.Fix
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-65): composition (WP G1)

Port of `MlDsaOpt44/Fn/Group/Main.lean` with `amask`, `col < 8`, `rb < 2`
symbolic: prologue (`g1_b0`, lane 4 `gL4`), `ginit` (`ginit_group` via `gL4_eq`),
five squeezes (`squeezes`), `gfix amask` (inactive lanes kept: raw candidates
below `2^23`), `pass3` at `ZH + 0x2000 (col / 4)`, `ACC + 0x2000 rb`, epilogue
and the returning `JUMP` (`reach_ret`).
-/

namespace MlDsaOpt65.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra
open MlDsa44

/-- Seed state of slot `k` of `group [amask, col, rb]`. -/
def g1I (cd : ByteArray) (amask col rb k : Nat) : Fips202.SpongeState :=
  seedState 168 (aSeed cd (gRow amask rb k) col)

/-- Raw candidate left in an inactive slot (lane `r` of `ABUF[t]` after the squeezes). -/
def g1Junk (cd : ByteArray) (amask col rb r t : Nat) : Nat :=
  cand (permN (t / 56 + 1) (g1I cd amask col rb r)) (t % 56)

theorem g1_popcnt {amask : Nat} (ha : amask < 16) : popcnt amask ≤ 4 := by
  interval_cases amask <;> decide

theorem g1_aI_active {cd : ByteArray} (h32 : 32 ≤ cd.size) {amask col rb r : Nat}
    (hact : amask.testBit r = true) :
    MlDsaOpt65.Proofs.aI (g1I cd amask col rb r) = aOf cd (4 * rb + r) col := by
  have h : MlDsaOpt44.Proofs.aI (seedState 168 (aSeed cd (4 * rb + r) col)) = aOf cd (4 * rb + r) col :=
    aI_aSeed h32 (4 * rb + r) col
  have e : g1I cd amask col rb r = seedState 168 (aSeed cd (4 * rb + r) col) := by
    unfold g1I gRow; rw [if_pos hact]
  rw [e]
  exact h

theorem g1_slot {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb r : Nat) :
    (!amask.testBit r || (MlDsaOpt65.Proofs.aI (g1I cd amask col rb r)).isSome) =
      (!amask.testBit r || (aOf cd (4 * rb + r) col).isSome) := by
  cases hact : amask.testBit r
  · simp only [Bool.not_false, Bool.true_or]
  · rw [g1_aI_active h32 hact]

theorem g1_flag {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb : Nat) :
    ((List.range 4).all fun sl => !amask.testBit sl ||
        (MlDsaOpt65.Proofs.aI (g1I cd amask col rb sl)).isSome) = gOk cd amask col rb := by
  unfold gOk
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.all_cons, List.all_nil, g1_slot h32]

theorem g1_pack4_lane {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] at hx ⊢
  omega

theorem g1_pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

/-- Prologue + `ginit`: the seeds are in `KS`, `HAVE6 = 0`. -/
theorem g1_init {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (ha : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (h32 : 32 ≤ s.executionEnv.calldata.size) :
    ∃ m2, SqInv m m2 (g1I s.executionEnv.calldata amask col rb) 0 ∧
      Reach (callState s 14256 (gB amask col rb ret tail) m)
        (callState s 14359 (gB amask col rb ret tail) m2) (179 + Gas.ginit) := by
  have htail : tail.length ≤ 768 := by
    have := hr.depth
    have e : Stack.group = 256 := by decide
    omega
  have hb0 := g1_b0 hs (tail := tail) (by omega) ha hcol hrb m (ret := ret)
  have hf1 := FrameExcept.mstore m HAVE6 0
  have h61 : word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) HAVE6 = 0 :=
    word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m2, hks2, hf2, hc2⟩ := MlDsaOpt65.Proofs.ginit_call hs (hr.callee (B' := Stack.ginit)
    (ret' := 14359) (extra := [wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide) (by simp only [isValidJumpDest_lit])
    (by norm_num))
    (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) (keep := 0) (amult := 15)
    (cmult := 0) (l4 := gL4 amask col rb) (by norm_num) (by norm_num) (by norm_num) (gL4_lt ha hcol hrb)
  refine ⟨m2, ⟨fun x hx => ?_, rc4_frame hf2 (fun i hi => by grp_avoids)
      (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
    ?_, FrameExcept.of_avoid (hf1.trans hf2) (by grp_sub), fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩,
    (hb0.trans hc2).of_eq rfl rfl⟩
  · rw [hks2 x hx, gL4_eq ha hcol hrb]
    exact ginit_group (fun y hy => by
      rw [FrameExcept.word hf1 (by grp_avoids)]; exact hrho.1 y hy)
      h32 (by omega) (fun k hk => Nat.lt_trans (gRow_lt (amask := amask) hrb hk) (by norm_num)) hx
  · rw [FrameExcept.word hf2 (by grp_avoids)]; exact h61

/-- The whole group: prologue, `ginit`, five squeezes, `gfix amask`, `pass3`, return. -/
theorem g1_group_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (ha : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ACC + 8192 * rb + 32 * t) =
          (word m (ACC + 8192 * rb + 32 * t) +
            pack4 (fun r => if amask.testBit r then
                ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t) *
              lane (word m (ZH + 8192 * (col / 4) + 32 * t)) (col % 4)) % 2 ^ 256) ∧
      FrameExcept m m' (groupFrame rb) ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group := by
  have htail : tail.length ≤ 768 := by
    have := hr.depth
    have e : Stack.group = 256 := by decide
    omega
  have hret := hr.small
  have h32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m2, hinv0, hR2⟩ := g1_init hs hr m hrc hrho ha hcol hrb h32
  have hI : Sized4 (g1I s.executionEnv.calldata amask col rb) := sized4_seedState 168 _
  -- five squeezes
  obtain ⟨m7, ⟨hks7, hrc7, h67, hfr7, hblk7⟩, hR7⟩ := squeezes hs hr (amask := amask) (col := col)
    (rb := rb) hI hinv0 (g1_K hs (by omega)) (g1_L hs (by omega))
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    5 le_rfl
  have hp := pending_of_blocks' (m := m7) (I := g1I s.executionEnv.calldata amask col rb)
    (fun b hb => (hblk7 b hb).1) (fun b hb => (hblk7 b hb).2) h67
  -- `gfix amask`
  obtain ⟨m8, hpost8, -, hkeep8, hf8, hc8⟩ := MlDsaOpt65.Proofs.gfix_call hs
    (hr.callee (B' := Stack.gfix) (ret' := 14478) (extra := [wd amask, wd col, wd rb, wd ret])
      (by simp only [List.length_cons, List.length_nil]; decide) (by simp only [isValidJumpDest_lit])
      (by norm_num)) m7 hrc7 ha 4 (g1_popcnt ha)
    (fun k => permN 5 (g1I s.executionEnv.calldata amask col rb k)) (fun k hk => permN_size (hI k hk) 5)
    hks7 (g1I s.executionEnv.calldata amask col rb) h67 (fun sl hsl _ => hp sl hsl)
  rw [g1_flag h32] at hc8
  have hfr8 : FrameExcept m m8 gsFrame := FrameExcept.of_avoid (hfr7.trans hf8) (by grp_sub)
  -- `pass3`
  obtain ⟨m9, hpost9, hf9, hc9⟩ := pass3_reach hs (hr.callee (B' := Stack.pass3) (ret' := 14512)
    (extra := [flag (gOk s.executionEnv.calldata amask col rb), wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m8 (k := col % 4)
    (zh := ZH + 8192 * (col / 4)) (acc := ACC + 8192 * rb) (Nat.mod_lt _ (by norm_num))
    (by unfold ZH ACC; omega) (by omega) (by unfold ACC HP; omega)
  refine ⟨m9, fun hall => ⟨g1Junk s.executionEnv.calldata amask col rb,
    fun r t => MlDsaOpt44.Proofs.cand_lt _ _, fun t ht => ?_⟩,
    FrameExcept.of_avoid (hfr8.trans hf9) (by grp_sub), ?_⟩
  · have hW : word m8 (ABUF + 32 * t) = pack4 (fun r => if amask.testBit r then
        ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat
        else g1Junk s.executionEnv.calldata amask col rb r t) := by
      rw [← g1_pack4_lane (word_lt m8 (ABUF + 32 * t))]
      apply g1_pack4_congr
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
        exact hpost8 r hr4 hact a (by rw [g1_aI_active h32 hact]; exact ha') t ht
      · rw [if_neg hact, hkeep8 r hr4 (by simpa using hact) t ht]
        have hb : t / 56 < 5 := by omega
        rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
          (hblk7 _ hb).1 _ (Nat.mod_lt _ (by norm_num)), lane_pack4_cand _ _ hr4]
        rfl
    rw [hpost9 t ht, FrameExcept.word hfr8 (a := ACC + 8192 * rb + 32 * t) (by grp_avoids),
      FrameExcept.word hfr8 (a := ZH + 8192 * (col / 4) + 32 * t) (by grp_avoids), hW]
  · rw [call_iff, Entry.group]
    have hfin := reach_ret hs 6404 m9 (pc := 14520)
      (tail := flag (gOk s.executionEnv.calldata amask col rb) :: tail)
      (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
      (by norm_num) hr.jumpdest hret (by simp only [List.length_cons]; omega)
    have h := ((((((hR2.trans hR7).trans (g1_G hs (tail := tail) (by omega) m7)).trans hc8).trans
      (g1_P hs (tail := tail) (by omega) hcol hrb m8)).trans hc9).trans
      (g1_E hs (tail := tail) (by omega) m9)).trans hfin
    refine (h.mono ?_).of_eq rfl rfl
    unfold Gas.group
    omega

end MlDsaOpt65.Proofs.GroupP
