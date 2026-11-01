import MlDsaOpt44.Main.Fin.Blocks
import MlDsaOpt44.Main.Fin.Spec
import MlDsaOpt44.Fn.Keccak
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `seg_fin`: six absorbed blocks of `FIN`, the padded last block, the c̃ comparison -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- After `j` blocks: every well-formed `FIN` content `X` has been absorbed `j` times. -/
structure FinInv (m M : ByteArray) (j : Nat) : Prop where
  rc1 : RC1Table M
  fr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)]
  ks : ∀ X : ByteArray, X.size = 832 → FinAt m X →
    KS1 M (absorbPre 136 (Fips202.pad 136 0x1F X) j)

theorem retOK_fin {B ret : Nat} {tail : List UInt256} (hB : B ≤ 1000) (htl : tail.length ≤ 8)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    RetOK B ret tail := retOK_main hB htl hj hret

theorem fin_frame_word {m M : ByteArray} (h : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)])
    {a : Nat} (ha : FIN ≤ a) (ha' : a + 32 ≤ TOP) : word M a = word m a :=
  FrameExcept.word h (by simp only [avoids_cons, avoids_nil, and_true, KS, KB, KZ, FIN, TOP] at *; omega)

theorem fin_start {s : State} (hs : Ctx s) (b : Bool) {m : ByteArray} (hrc : RC1Table m) :
    ∃ M, FinInv m M 0 ∧ Reach (callState s 6001 [flag b] m) (callState s 6126 [wd 59648, flag b] M) 220 := by
  obtain ⟨M, f, fr, r⟩ := fin_init hs b m
  refine ⟨M, ⟨hrc.frame fr (by avoids_tac), fr.mono ?_, fun X _ _ x hx => ?_⟩, r⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp [KS, KB, KZ]
  · rw [f x hx, absorbPre_zero, laneOf_emptyState]

/-- One absorbing iteration, up to the return of `kf1`. -/
theorem fin_iter {s : State} (hs : Ctx s) (b : Bool) {m M : ByteArray} (j : Nat) (hj : j < 6)
    (hI : FinInv m M j) :
    ∃ M', FinInv m M' (j + 1) ∧
      Reach (callState s 6126 [wd (59648 + 544 * j), flag b] M)
        (callState s 6360 [wd (59648 + 544 * j), flag b] M') (466 + Gas.kf1) := by
  obtain ⟨M1, f1, fr1, r1⟩ := fin_abs hs b M (p := 59648 + 544 * j) (by omega) (by omega)
  obtain ⟨M2, hk2, hf2, hc2⟩ := kf1_call hs (ret := 6360) (tail := [wd (59648 + 544 * j), flag b])
    (retOK_fin (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M1
    (hI.rc1.frame fr1 (by avoids_tac))
  rw [call_iff] at hc2
  have hfr : FrameExcept m M2 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] := by
    refine ((hI.fr.trans fr1).trans hf2).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, KZ]
  refine ⟨M2, ⟨(hI.rc1.frame fr1 (by avoids_tac)).frame hf2 (by avoids_tac), hfr, fun X hX hF => ?_⟩,
    (r1.trans hc2).mono (by omega)⟩
  set St := absorbPre 136 (Fips202.pad 136 0x1F X) j
  set S' := Fips202.xorBlock 136 (Fips202.pad 136 0x1F X) (j * 136) St
  have hS' : S'.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M1 S' := fun x hx => by
    rw [laneOf_xorBlock _ _ (absorbPre_size _ _ j) (by norm_num) x]
    by_cases h : x < 17
    · rw [f1 x h, hI.ks X hX hF x hx, if_pos (by omega),
        fin_frame_word hI.fr (by unfold FIN; omega) (by unfold TOP; omega),
        show 32 * x + (59648 + 544 * j) = FIN + 32 * (17 * j + x) by unfold FIN; ring,
        hF _ (by omega), rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_pad_full _ (by rw [hX]; omega), show 8 * (17 * j + x) = j * 136 + 8 * x by ring]
    · rw [if_neg (by omega), ← hI.ks X hX hF x hx]
      exact FrameExcept.word fr1 (by simp only [avoids_cons, avoids_nil, and_true, KS]; omega)
  have := hk2 S' hS' hK
  rwa [← absorbPre_succ] at this

theorem fin_loop {s : State} (hs : Ctx s) (b : Bool) {m M0 : ByteArray} (hI0 : FinInv m M0 0) :
    ∀ j, j ≤ 5 → ∃ M, FinInv m M j ∧
      Reach (callState s 6126 [wd 59648, flag b] M0)
        (callState s 6126 [wd (59648 + 544 * j), flag b] M) (j * (495 + Gas.kf1))
  | 0, _ => ⟨M0, hI0, by simpa using Reach.refl _⟩
  | j + 1, hj => by
    obtain ⟨M, hI, hR⟩ := fin_loop hs b hI0 j (by omega)
    obtain ⟨M', hI', hR'⟩ := fin_iter hs b j (by omega) hI
    have hb := fin_back hs b M' (p := 59648 + 544 * j) (by omega)
    rw [show 544 + (59648 + 544 * j) = 59648 + 544 * (j + 1) by ring] at hb
    exact ⟨M', hI', ((hR.trans hR').trans hb).mono (by rw [Nat.succ_mul]; omega)⟩

/-- The last block of an 832-byte input: what `fin_pad` xors in. -/
theorem finTail_eq {m M : ByteArray} (hfr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)])
    {X : ByteArray} (hX : X.size = 832) (hF : FinAt m X) {x : Nat} (hx : x < 25) :
    finTail M x = rep (if x < 17 then le64 (Fips202.pad 136 0x1F X) (816 + 8 * x) else 0) := by
  have hl : ∀ x, x < 17 → le64 (Fips202.pad 136 0x1F X) (816 + 8 * x) =
      le64 X (816 + 8 * x) ^^^ padLane 16 x := fun x hx => by
    have := le64_pad_last X hx
    rwa [hX] at this
  have w0 : word M 62912 = rep (le64 X 816) := by
    rw [fin_frame_word hfr (by unfold FIN; omega) (by unfold TOP; omega),
      show (62912 : Nat) = FIN + 32 * 102 by rfl, hF 102 (by omega)]
  have w1 : word M 62944 = rep (le64 X 824) := by
    rw [fin_frame_word hfr (by unfold FIN; omega) (by unfold TOP; omega),
      show (62944 : Nat) = FIN + 32 * 103 by rfl, hF 103 (by omega)]
  have z : ∀ x, 2 ≤ x → le64 X (816 + 8 * x) = 0 := fun x hx => le64_beyond X (by omega)
  unfold finTail
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 16 ∨ (3 ≤ x ∧ x < 16) ∨ 17 ≤ x) with h | h | h | h | h | h
  · subst h
    rw [if_pos rfl, if_pos (by norm_num), hl 0 (by norm_num), w0]; unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), hl 1 (by norm_num), w1]
    unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), hl 2 (by norm_num),
      z 2 (by norm_num)]
    unfold padLane; norm_num
  · subst h
    rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl,
      if_pos (by norm_num), hl 16 (by norm_num), z 16 (by norm_num)]
    unfold padLane; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      hl x (by omega), z x (by omega)]
    unfold padLane
    rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero, rep_zero]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      rep_zero]

theorem rep_cpl_xor' (x : Nat) {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) :
    rep (cpl x v) ^^^ rep w = rep (cpl x (v ^^^ w)) := rep_cpl_xor x hv hw

/-- The last block, the final permutation. -/
theorem fin_last_block {s : State} (hs : Ctx s) (b : Bool) {m M : ByteArray} (hI : FinInv m M 6) :
    ∃ M', RC1Table M' ∧
      (∀ X : ByteArray, X.size = 832 → FinAt m X →
        KS1 M' (Fips202.absorb 136 (Fips202.pad 136 0x1F X))) ∧
      Reach (callState s 6374 [wd 62912, flag b] M) (callState s 6477 [flag b] M') (92 + Gas.kf1) := by
  obtain ⟨M3, f3, fr3, r3⟩ := fin_pad hs b M 62912
  obtain ⟨M4, hk4, hf4, hc4⟩ := kf1_call hs (ret := 6477) (tail := [flag b])
    (retOK_fin (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M3
    (hI.rc1.frame fr3 (by avoids_tac))
  rw [call_iff] at hc4
  refine ⟨M4, (hI.rc1.frame fr3 (by avoids_tac)).frame hf4 (by avoids_tac), fun X hX hF => ?_,
    (r3.trans hc4).mono (by omega)⟩
  set St := absorbPre 136 (Fips202.pad 136 0x1F X) 6
  set S'' := Fips202.xorBlock 136 (Fips202.pad 136 0x1F X) (6 * 136) St
  have hS'' : S''.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M3 S'' := fun x hx => by
    have hpl : padLane 16 x < 2 ^ 64 := padLane_lt _ _
    rw [f3 x hx, hI.ks X hX hF x hx, finTail_eq hI.fr hX hF hx,
      laneOf_xorBlock _ _ (absorbPre_size _ _ 6) (by norm_num) x]
    by_cases h : x < 17
    · rw [if_pos h, if_pos (by omega), rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _)]
    · rw [if_neg h, if_neg (by omega), rep_zero, Nat.xor_zero]
  have hP : (Fips202.pad 136 0x1F X).size = 7 * 136 := by rw [pad_size _ _ (by norm_num), hX]
  rw [absorb_eq _ _ 7 (by norm_num) hP, absorbPre_succ]
  exact hk4 S'' hS'' hK

theorem land_rep {v : Nat} (hv : v < 2 ^ 64) : 18446744073709551615 &&& rep v = v := by
  rw [land_M64, show (18446744073709551616 : Nat) = 2 ^ (64 * 0) * 2 ^ 64 by norm_num]
  have := lane_rep hv (k := 0) (by omega)
  simpa using this

theorem land_not_rep {v : Nat} (hv : v < 2 ^ 64) :
    18446744073709551615 &&& 115792089237316195423570985008687907853269984665640564039457584007913129639935 -
      rep (18446744073709551615 - v) = v := by
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat) =
    2 ^ 256 - 1 by norm_num, show (18446744073709551615 : Nat) - v = 2 ^ 64 - 1 - v by norm_num,
    not_rep (by omega), show 2 ^ 64 - 1 - (2 ^ 64 - 1 - v) = v by omega, land_rep hv]

theorem or4_eq (a : Nat → Nat) (h : ∀ k, k < 4 → a k < 2 ^ 64) :
    a 3 ||| (a 2 * 18446744073709551616 ||| (a 1 * 340282366920938463463374607431768211456 |||
      a 0 * 6277101735386680763835789423207666416102355444464034512896)) = pack4 fun k => a (3 - k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have hv : ∀ k, k < 4 → a (3 - k) < 2 ^ 64 := fun k hk => h _ (by omega)
  rw [show (18446744073709551616 : Nat) = 2 ^ 64 by norm_num,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 by norm_num,
    show (6277101735386680763835789423207666416102355444464034512896 : Nat) = 2 ^ 192 by norm_num]
  have hL : a 3 ||| (a 2 * 2 ^ 64 ||| (a 1 * 2 ^ 128 ||| a 0 * 2 ^ 192)) < 2 ^ 256 := by
    refine Nat.or_lt_two_pow (by omega) (Nat.or_lt_two_pow ?_ (Nat.or_lt_two_pow ?_ ?_))
    · calc a 2 * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
        _ ≤ 2 ^ 256 := by norm_num
    · calc a 1 * 2 ^ 128 < 2 ^ 64 * 2 ^ 128 := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ ≤ 2 ^ 256 := by norm_num
    · calc a 0 * 2 ^ 192 < 2 ^ 64 * 2 ^ 192 := Nat.mul_lt_mul_of_pos_right h0 (by positivity)
        _ ≤ 2 ^ 256 := by norm_num
  apply eq_of_testBit_lt hL (pack4_lt' hv)
  intro j hj
  rw [testBit_pack4 hv hj]
  simp only [Nat.testBit_or, Nat.testBit_mul_two_pow]
  have f : ∀ k i, k < 4 → 64 ≤ i → (a k).testBit i = false := fun k i hk hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h k hk) (Nat.pow_le_pow_right (by omega) hi))
  rcases (by omega : j < 64 ∨ (64 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 192) ∨ (192 ≤ j ∧ j < 256)) with
    hj' | hj' | hj' | hj'
  · rw [show j / 64 = 0 by omega, show j % 64 = j by omega]
    simp [show ¬ 64 ≤ j by omega, show ¬ 128 ≤ j by omega, show ¬ 192 ≤ j by omega]
  · rw [show j / 64 = 1 by omega, f 3 j (by omega) (by omega)]
    simp [show 64 ≤ j by omega, show ¬ 128 ≤ j by omega, show ¬ 192 ≤ j by omega,
      show j - 64 = j % 64 by omega]
  · rw [show j / 64 = 2 by omega, f 3 j (by omega) (by omega)]
    simp [show 64 ≤ j by omega, show 128 ≤ j by omega, show ¬ 192 ≤ j by omega,
      show j - 128 = j % 64 by omega, f 2 (j - 64) (by omega) (by omega)]
  · rw [show j / 64 = 3 by omega, f 3 j (by omega) (by omega)]
    simp [show 64 ≤ j by omega, show 128 ≤ j by omega, show 192 ≤ j by omega,
      show j - 192 = j % 64 by omega, f 2 (j - 64) (by omega) (by omega), f 1 (j - 128) (by omega) (by omega)]

/-- The compared word is the four squeezed lanes, first lane on top. -/
theorem finW_eq {M : ByteArray} {S : Fips202.SpongeState} (hK : KS1 M S) :
    finW M % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pack4 fun k => laneOf S (3 - k) := by
  have k0 := hK 0 (by omega); have k1 := hK 1 (by omega)
  have k2 := hK 2 (by omega); have k3 := hK 3 (by omega)
  simp only [KS, cpl, complemented] at k0 k1 k2 k3
  norm_num at k0 k1 k2 k3
  unfold finW
  rw [k0, k1, k2, k3]
  simp only [land_rep (laneOf_lt S _), land_not_rep (laneOf_lt S _)]
  rw [or4_eq (fun k => laneOf S k) (fun _ _ => laneOf_lt _ _)]
  exact Nat.mod_eq_of_lt (by have := pack4_lt' (v := fun k => laneOf S (3 - k)) (fun _ _ => laneOf_lt _ _); norm_num at this ⊢; exact this)

theorem seg_fin_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC1Table m) (b : Bool) :
    ∃ E : Bool, ∃ pc stk m',
      (∀ X : ByteArray, X.size = 832 → FinAt m X → E = (ctOf s.executionEnv.calldata == Fips204.H X 32)) ∧
      Reach (callState s 6001 [flag b] m)
        (finalState s pc stk m' (if (b && E) = true then 1 else 0)) Gas.pFin := by
  obtain ⟨M0, hI0, r0⟩ := fin_start hs b hrc
  obtain ⟨M5, hI5, r1⟩ := fin_loop hs b hI0 5 le_rfl
  obtain ⟨M6, hI6, r2⟩ := fin_iter hs b 5 (by omega) hI5
  have r3 := fin_last hs b M6 (p := 59648 + 544 * 5) (by norm_num)
  obtain ⟨M7, hrc7, hK7, r4⟩ := fin_last_block hs b hI6
  have r5 := fin_net hs b M7
  have r6 := fin_cmp hs b _ (bswapNet_lt (word s.executionEnv.calldata 1312)) M7
  refine ⟨decide (finW M7 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      bswapNet (word s.executionEnv.calldata 1312)), 6696, [], M7, fun X hX hF => ?_, ?_⟩
  · rw [finW_eq (hK7 X hX hF), bswapNet_word]
    exact cmp_eq _ X hcd
  · exact ((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r6).mono
      (by unfold Gas.pFin; omega)

end MlDsaOpt44.Proofs
