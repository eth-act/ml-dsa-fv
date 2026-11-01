import MlDsaOpt44.Main.Mu.Blocks
import MlDsaOpt44.Main.Mu.Spec
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `seg_mu`: composition of the blocks with `kf1` and `absorb17` -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- Lanes at the loop head after `j` absorbed blocks: block `j`'s raw lanes xored in. -/
def muLanes (cd : ByteArray) (j x : Nat) : Nat :=
  laneOf (absorbPre 136 (muPad cd) j) x ^^^ (if x < 17 then le64 (muMsgW cd) (136 * j + 8 * x) else 0)

structure MuInv (cd m M : ByteArray) (j : Nat) : Prop where
  rc1 : RC1Table M
  fr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800)]
  ks : ∀ x, x < 25 → word M (KS + 32 * x) = rep (cpl x (muLanes cd j x))

theorem lane_case {W W' x v : Nat} (h1 : W' = W ^^^ rep v) (h2 : W = rep (cpl x 0))
    (hv : v < 2 ^ 64) : W' = rep (cpl x v) := by
  rw [h1, h2, rep_cpl_xor x (v := 0) (by norm_num) hv, Nat.zero_xor]

theorem lane8_eq (cd : ByteArray) :
    18446744073709486080 &&& lane (bswapNet (word cd 3730)) 3 = le64 (muMsgW cd) (8 * 8) := by
  rw [lane_bswapNet _ _ (by omega : 3 < 4), le64_muMsgW_64]

theorem muLanes_zero (cd : ByteArray) (x : Nat) :
    muLanes cd 0 x = if x < 17 then le64 (muMsgW cd) (8 * x) else 0 := by
  unfold muLanes
  rw [absorbPre_zero, laneOf_emptyState, Nat.zero_xor, Nat.mul_zero, Nat.zero_add]

set_option maxHeartbeats 2000000 in
/-- The setup (`4943 … 5727`) leaves the raw lanes of block 0. -/
theorem mu_setup {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m : ByteArray} (htr : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x))
    (hrc : RC1Table m) :
    ∃ M, MuInv s.executionEnv.calldata m M 0 ∧
      Reach (callState s 4943 [flag b] m)
        (callState s 5727 [wd (66 + (s.executionEnv.calldata.size - 3732)), wd 3802, flag b] M) 983 := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hl : 3732 ≤ s.executionEnv.calldata.size := hcd
  obtain ⟨M1, f1, fr1, r1⟩ := mu_L1 hs b m (fun x hx => by rw [htr x hx]; exact le64_lt _ _)
  have r2a := mu_L2a hs b M1
  obtain ⟨M2, f2, fr2, r2⟩ := mu_L2b hs b (bswapNet (word s.executionEnv.calldata 3730)) (bswapNet_lt _) M1
  have r3a := mu_L3a hs b M2
  obtain ⟨M3, f3, fr3, r3⟩ := mu_L3b hs b (bswapNet (word s.executionEnv.calldata 3762)) (bswapNet_lt _) M2
  have r4a := mu_L4a hs b M3
  obtain ⟨M4, f4, fr4, r4⟩ := mu_L4b hs b (bswapNet (word s.executionEnv.calldata 3794)) (bswapNet_lt _) M3 hfit hl
  have w2 : ∀ a, a + 32 ≤ KS + 256 ∨ KS + 384 ≤ a → word M2 a = word M1 a := fun a ha =>
    FrameExcept.word fr2 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
  have w3 : ∀ a, a + 32 ≤ KS + 384 ∨ KS + 512 ≤ a → word M3 a = word M2 a := fun a ha =>
    FrameExcept.word fr3 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
  have w4 : ∀ a, a + 32 ≤ KS + 512 ∨ KS + 544 ≤ a → word M4 a = word M3 a := fun a ha =>
    FrameExcept.word fr4 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
  have e1 : ∀ x, x < 25 → word M1 (KS + 32 * x) =
      rep (cpl x (if x < 8 then le64 (muMsgW s.executionEnv.calldata) (8 * x) else 0)) := by
    intro x hx
    rw [f1 x hx]
    split
    · rw [htr x (by omega), le64_muMsgW_lo _ (by omega)]
    · rfl
  have hfr : FrameExcept m M4 [(KS, KS + 800), (KB, KB + 800)] := by
    refine (((fr1.trans fr2).trans fr3).trans fr4).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, FIN]
  refine ⟨M4, ⟨hrc.frame hfr (by avoids_tac), hfr, fun x hx => ?_⟩, ?_⟩
  · rw [muLanes_zero]
    interval_cases x
    · rw [if_pos (by norm_num : (0 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 0 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (1 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 1 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (2 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 2 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (3 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 3 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (4 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 4 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (5 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 5 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (6 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 6 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (7 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 7 (by omega), if_pos (by omega)]
    · rw [if_pos (by norm_num : (8 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega)]
      refine (lane_case f2.1 ((e1 8 (by omega)).trans (by rw [if_neg (by omega)])) (mask48_lt64 _)).trans ?_
      rw [lane8_eq]
    · rw [if_pos (by norm_num : (9 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega)]
      refine (lane_case f2.2.1 ((e1 9 (by omega)).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 2 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 9)]
    · rw [if_pos (by norm_num : (10 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega)]
      refine (lane_case f2.2.2.1 ((e1 10 (by omega)).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 1 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 10)]
    · rw [if_pos (by norm_num : (11 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega)]
      refine (lane_case f2.2.2.2 ((e1 11 (by omega)).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 0 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 11)]
    · rw [if_pos (by norm_num : (12 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega)]
      refine (lane_case f3.1 (((w2 _ (by unfold KS; omega)).trans (e1 12 (by omega))).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 3 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 12)]
    · rw [if_pos (by norm_num : (13 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega)]
      refine (lane_case f3.2.1 (((w2 _ (by unfold KS; omega)).trans (e1 13 (by omega))).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 2 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 13)]
    · rw [if_pos (by norm_num : (14 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega)]
      refine (lane_case f3.2.2.1 (((w2 _ (by unfold KS; omega)).trans (e1 14 (by omega))).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 1 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 14)]
    · rw [if_pos (by norm_num : (15 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega)]
      refine (lane_case f3.2.2.2 (((w2 _ (by unfold KS; omega)).trans (e1 15 (by omega))).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 0 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 15)]
    · rw [if_pos (by norm_num : (16 : Nat) < 17)]
      refine (lane_case f4 ((((w3 _ (by unfold KS; omega)).trans (w2 _ (by unfold KS; omega))).trans (e1 16 (by omega))).trans (by rw [if_neg (by omega)])) (lane_lt64 _ _)).trans ?_
      rw [lane_bswapNet _ _ (by omega : 3 < 4), le64_muMsgW_hi _ (by omega : 66 ≤ 8 * 16)]
    · rw [if_neg (by norm_num : ¬ (17 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 17 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (18 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 18 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (19 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 19 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (20 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 20 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (21 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 21 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (22 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 22 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (23 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 23 (by omega), if_neg (by omega)]
    · rw [if_neg (by norm_num : ¬ (24 : Nat) < 17)]
      rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 24 (by omega), if_neg (by omega)]
  · exact ((((((r1.trans r2a).trans r2).trans r3a).trans r3).trans r4a).trans r4).mono (by norm_num)

theorem muLanes_lt (cd : ByteArray) (j x : Nat) : muLanes cd j x < 2 ^ 64 := by
  unfold muLanes
  apply Nat.xor_lt_two_pow (laneOf_lt _ _)
  split
  · exact le64_lt _ _
  · norm_num

theorem retOK_mu {B ret : Nat} {tail : List UInt256} (hB : B ≤ 1000) (htl : tail.length ≤ 8)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    RetOK B ret tail := retOK_main hB htl hj hret

/-- One loop visit absorbing the next full block. -/
theorem mu_iter {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m M : ByteArray} (j : Nat) (hj : 136 * (j + 1) ≤ (muMsgW s.executionEnv.calldata).size)
    (hI : MuInv s.executionEnv.calldata m M j) :
    ∃ M', MuInv s.executionEnv.calldata m M' (j + 1) ∧
      Reach (callState s 5727 [wd ((muMsgW s.executionEnv.calldata).size - 136 * j), wd (3802 + 136 * j), flag b] M)
        (callState s 5727 [wd ((muMsgW s.executionEnv.calldata).size - 136 * (j + 1)),
          wd (3802 + 136 * (j + 1)), flag b] M') (Gas.kf1 + Gas.absorb17 + 88) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hL := muMsgW_size s.executionEnv.calldata hcd
  set L := (muMsgW s.executionEnv.calldata).size
  have h1 := mu_loop1 hs b M (len := L - 136 * j) (off := 3802 + 136 * j) (by omega) (by omega)
  set S' := Fips202.xorBlock 136 (muPad s.executionEnv.calldata) (j * 136)
    (absorbPre 136 (muPad s.executionEnv.calldata) j)
  have hS' : S'.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M S' := fun x hx => by
    rw [hI.ks x hx, laneOf_xorBlock _ _ (absorbPre_size _ _ j) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad s.executionEnv.calldata =
        Fips202.pad 136 0x1F (muMsgW s.executionEnv.calldata) from rfl, le64_pad_full _ (by omega),
        show j * 136 + 8 * x = 136 * j + 8 * x by ring]
    · rw [if_neg (by omega), if_neg h, Nat.xor_zero]
  obtain ⟨M1, hk1, hf1, hc1⟩ := kf1_call hs (ret := 5743)
    (tail := [wd (L - 136 * j), wd (3802 + 136 * j), flag b])
    (retOK_mu (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M hI.rc1
  have hK1 : KS1 M1 (absorbPre 136 (muPad s.executionEnv.calldata) (j + 1)) := by
    rw [absorbPre_succ]; exact hk1 S' hS' hK
  have h2 := mu_loop2 hs b M1 (len := L - 136 * j) (off := 3802 + 136 * j)
  obtain ⟨M2, ha2, hf2, hc2⟩ := absorb17_call hs (ret := 5753)
    (tail := [wd (3802 + 136 * j), wd (L - 136 * j), flag b])
    (retOK_mu (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M1
    (off := 3802 + 136 * j) (by omega)
  have h3 := mu_loop3 hs b M2 (len := L - 136 * j) (off := 3802 + 136 * j) (by omega) (by omega)
  rw [show L - 136 * j - 136 = L - 136 * (j + 1) by omega,
    show 136 + (3802 + 136 * j) = 3802 + 136 * (j + 1) by ring] at h3
  rw [call_iff] at hc1 hc2
  have hfr : FrameExcept m M2 [(KS, KS + 800), (KB, KB + 800)] := by
    refine ((hI.fr.trans hf1).trans hf2).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, FIN]
  refine ⟨M2, ⟨(hI.rc1.frame hf1 (by avoids_tac)).frame hf2 (by avoids_tac), hfr, fun x hx => ?_⟩, ?_⟩
  · rw [ha2 x hx, hK1 x hx]
    unfold muLanes
    split
    · rw [rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_muMsgW_hi _ (a := 136 * (j + 1) + 8 * x) (by omega),
        show 3666 + (136 * (j + 1) + 8 * x) = 3802 + 136 * j + 8 * x by ring]
    · rw [Nat.xor_zero]
  · exact ((((h1.trans hc1).trans h2).trans hc2).trans h3).mono (by omega)

theorem mu_loop {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m M0 : ByteArray} (hI0 : MuInv s.executionEnv.calldata m M0 0) :
    ∀ j, 136 * j ≤ (muMsgW s.executionEnv.calldata).size →
      ∃ M, MuInv s.executionEnv.calldata m M j ∧
        Reach (callState s 5727 [wd (muMsgW s.executionEnv.calldata).size, wd 3802, flag b] M0)
          (callState s 5727 [wd ((muMsgW s.executionEnv.calldata).size - 136 * j),
            wd (3802 + 136 * j), flag b] M) (j * (Gas.kf1 + Gas.absorb17 + 88))
  | 0, _ => ⟨M0, hI0, by simpa using Reach.refl _⟩
  | j + 1, hj => by
    obtain ⟨M, hI, hR⟩ := mu_loop hs hcd b hI0 j (by omega)
    obtain ⟨M', hI', hR'⟩ := mu_iter hs hcd b j hj hI
    exact ⟨M', hI', (hR.trans hR').mono (by rw [Nat.succ_mul])⟩

theorem padLane_hi {r x : Nat} (hr : r < 136) (hx : 17 ≤ x) : padLane r x = 0 := by
  unfold padLane; rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero]

/-- Exit: padding, the final permutation and the copy of μ's lanes to `FIN`. -/
theorem mu_finish {s : State} (hs : Ctx s) (b : Bool)
    {m M : ByteArray}
    (hI : MuInv s.executionEnv.calldata m M ((muMsgW s.executionEnv.calldata).size / 136)) :
    ∃ M', FinMu M' s.executionEnv.calldata ∧ RC1Table M' ∧
      FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] ∧
      Reach (callState s 5727 [wd ((muMsgW s.executionEnv.calldata).size -
          136 * ((muMsgW s.executionEnv.calldata).size / 136)),
          wd (3802 + 136 * ((muMsgW s.executionEnv.calldata).size / 136)), flag b] M)
        (callState s 5926 [flag b] M') (23 + 100 + Gas.kf1 + 102) := by
  set cd := s.executionEnv.calldata with hcdef
  set L := (muMsgW cd).size
  set n := L / 136
  have hr : L - 136 * n = L % 136 := by omega
  have hr' : L % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have h1 := mu_exit hs b M (len := L - 136 * n) (off := 3802 + 136 * n) (by omega)
  obtain ⟨M5, f5, fr5, r5⟩ := mu_pad hs b M (len := L - 136 * n) (off := 3802 + 136 * n) (by omega)
  set S'' := Fips202.xorBlock 136 (muPad cd) (L / 136 * 136) (absorbPre 136 (muPad cd) n)
  have hS'' : S''.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M5 S'' := fun x hx => by
    rw [f5 x hx, hI.ks x hx, hr, rep_cpl_xor _ (muLanes_lt _ _ _) (padLane_lt _ _),
      laneOf_xorBlock _ _ (absorbPre_size _ _ n) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad cd =
        Fips202.pad 136 0x1F (muMsgW cd) from rfl, le64_pad_last _ h, Nat.xor_assoc,
        show 136 * n = L / 136 * 136 by ring]
    · rw [if_neg (by omega), if_neg h, Nat.xor_zero, padLane_hi hr' (by omega), Nat.xor_zero]
  obtain ⟨M6, hk6, hf6, hc6⟩ := kf1_call hs (ret := 5868) (tail := [flag b])
    (retOK_mu (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M5
    ((hI.rc1).frame fr5 (by avoids_tac))
  have hP : (muPad cd).size = (n + 1) * 136 := by
    rw [show muPad cd = Fips202.pad 136 0x1F (muMsgW cd) from rfl, pad_size _ _ (by norm_num)]
  have hK6 : KS1 M6 (Fips202.absorb 136 (muPad cd)) := by
    rw [absorb_eq _ _ (n + 1) (by norm_num) hP, absorbPre_succ,
      show n * 136 = L / 136 * 136 from rfl]
    exact hk6 S'' hS'' hK
  obtain ⟨M7, f7, fr7, r7⟩ := mu_copy hs b M6
  rw [call_iff] at hc6
  have hfr : FrameExcept m M7 [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] := by
    refine (((hI.fr.trans fr5).trans hf6).trans fr7).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, FIN]
  refine ⟨M7, fun x hx => ?_, ((hI.rc1.frame fr5 (by avoids_tac)).frame hf6 (by avoids_tac)).frame fr7
    (by avoids_tac), hfr, (((h1.trans r5).trans hc6).trans r7).mono (by omega)⟩
  rw [f7 x hx, hK6 x (by omega), le64_muOf_absorb cd hx]
  have hl := laneOf_lt (Fips202.absorb 136 (muPad cd)) x
  split
  · rename_i h
    exact not_rep_cpl (by rcases h with rfl | rfl <;> decide) hl
  · rename_i h
    unfold cpl
    rw [if_neg (by interval_cases x <;> simp_all [complemented])]

theorem seg_mu_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 4648 [flag b] m) (callState s 5926 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hl : 3732 ≤ s.executionEnv.calldata.size := hcd
  -- the invariant from any frame avoiding the Keccak state and `FIN`
  have inv6 : ∀ M', FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] →
      FinMu M' s.executionEnv.calldata → RC1Table M' → Inv6 s.executionEnv.calldata M' :=
    fun M' hfr hmu hrc =>
      { rc1 := hrc
        tbl := hI.tbl.frame hfr (by avoids_tac)
        hp := hI.hp.frame hfr (by avoids_tac)
        acc := hI.acc.frame hfr (by avoids_tac)
        cb := fun x hx => by
          rw [word_frame hfr (lo := CB) (hi := CB + 1088) (by avoids_tac) (by omega) (by omega)]
          exact hI.cb x hx
        fresh := hI.fresh.frame hfr (by avoids_tac) (by avoids_tac) (by avoids_tac)
        fmu := hmu }
  by_cases hsh : mlenOf s.executionEnv.calldata ≤ 69
  · have hlt : s.executionEnv.calldata.size < 3802 := by unfold mlenOf at hsh; omega
    obtain ⟨M', f, fr, r⟩ := mu_short hs b m hfit hlt (fun x hx => by
      rw [hI.mu hsh x hx]; exact le64_lt _ _)
    have hfr : FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] := by
      refine fr.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [KS, KB, FIN]
    refine ⟨M', inv6 M' hfr (fun x hx => by rw [f x hx, hI.mu hsh x hx])
      (hI.rc1.frame fr (by avoids_tac)), ?_⟩
    unfold Gas.pMu; rw [if_pos hsh]; exact r
  · have hlong : 3802 ≤ s.executionEnv.calldata.size := by unfold mlenOf at hsh; omega
    have r0 := mu_chk_long hs b m hfit hlong
    obtain ⟨M0, hI0, r1⟩ := mu_setup hs hcd b hI.trl hI.rc1
    have hL := muMsgW_size s.executionEnv.calldata hcd
    rw [← hL] at r1
    obtain ⟨M, hIn, r2⟩ := mu_loop hs hcd b hI0 ((muMsgW s.executionEnv.calldata).size / 136)
      (Nat.mul_div_le _ _)
    obtain ⟨M', hmu, hrc, hfr, r3⟩ := mu_finish hs b hIn
    refine ⟨M', inv6 M' hfr hmu hrc, (((r0.trans r1).trans r2).trans r3).mono ?_⟩
    unfold Gas.pMu
    rw [if_neg hsh, hL]
    unfold mlenOf
    rw [Nat.add_mul, Nat.one_mul]
    omega

end MlDsaOpt44.Proofs
