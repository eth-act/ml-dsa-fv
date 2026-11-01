N='115792089237316195423570985008687907853269984665640564039457584007913129639936'
cases=[]
for x in range(25):
    if x<8:
        t=f"rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 {x} (by omega), if_pos (by omega)]"
    elif x<=16:
        if x<12: i=x-8; base=3730; F='f2'; frames=f"rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega)]"
        elif x<16: i=x-12; base=3762; F='f3'; frames=f"rw [w4 _ (by unfold KS; omega)]"
        else: i=0; base=3794; F='f4'; frames=""
        k=3-i
        comp = F if F=='f4' else F+['.1','.2.1','.2.2.1','.2.2.2'][i]
        prev = {'f2':'(w := M1)', 'f3':'', 'f4':''}[F]
        # value W: word of the memory before the block at KS + 32x, expressed through e1 and frames
        if F=='f2': base_eq=f"(e1 {x} (by omega)).trans (by rw [if_neg (by omega)])"
        elif F=='f3': base_eq=f"((w2 _ (by unfold KS; omega)).trans (e1 {x} (by omega))).trans (by rw [if_neg (by omega)])"
        else: base_eq=f"(((w3 _ (by unfold KS; omega)).trans (w2 _ (by unfold KS; omega))).trans (e1 {x} (by omega))).trans (by rw [if_neg (by omega)])"
        if x==8:
            hv="(mask48_lt64 _)"; leq="rw [lane8_eq]"
        else:
            hv="(lane_lt64 _ _)"; leq=f"rw [lane_bswapNet _ _ (by omega : {k} < 4), le64_muMsg_hi _ (by omega : 66 ≤ 8 * {x})]"
        t=(f"{frames}\n      " if frames else "")+f"refine (lane_case {comp} ({base_eq}) {hv}).trans ?_\n      {leq}"
    else:
        t=f"rw [w4 _ (by unfold KS; omega), w3 _ (by unfold KS; omega), w2 _ (by unfold KS; omega), e1 {x} (by omega), if_neg (by omega)]"
    cases.append(t)
setup_cases='\n'.join(f"    · rw [{'if_pos' if x<17 else 'if_neg'} (by norm_num : {'' if x<17 else '¬ '}({x} : Nat) < 17)]\n      {c}" for x,c in enumerate(cases))
src=f'''import MlDsaOpt44.Main.Mu.Blocks
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
  laneOf (absorbPre 136 (muPad cd) j) x ^^^ (if x < 17 then le64 (muMsg cd) (136 * j + 8 * x) else 0)

structure MuInv (cd m M : ByteArray) (j : Nat) : Prop where
  rc1 : RC1Table M
  fr : FrameExcept m M [(KS, KS + 800), (KB, KB + 800)]
  ks : ∀ x, x < 25 → word M (KS + 32 * x) = rep (cpl x (muLanes cd j x))

theorem lane_case {{W W' x v : Nat}} (h1 : W' = W ^^^ rep v) (h2 : W = rep (cpl x 0))
    (hv : v < 2 ^ 64) : W' = rep (cpl x v) := by
  rw [h1, h2, rep_cpl_xor x (v := 0) (by norm_num) hv, Nat.zero_xor]

theorem lane8_eq (cd : ByteArray) :
    18446744073709486080 &&& lane (bswapNet (word cd 3730)) 3 = le64 (muMsg cd) (8 * 8) := by
  rw [lane_bswapNet _ _ (by omega : 3 < 4), le64_muMsg_64]

theorem muLanes_zero (cd : ByteArray) (x : Nat) :
    muLanes cd 0 x = if x < 17 then le64 (muMsg cd) (8 * x) else 0 := by
  unfold muLanes
  rw [absorbPre_zero, laneOf_emptyState, Nat.zero_xor, Nat.mul_zero, Nat.zero_add]

set_option maxHeartbeats 2000000 in
/-- The setup (`4943 … 5727`) leaves the raw lanes of block 0. -/
theorem mu_setup {{s : State}} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {{m : ByteArray}} (htr : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x))
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
      rep (cpl x (if x < 8 then le64 (muMsg s.executionEnv.calldata) (8 * x) else 0)) := by
    intro x hx
    rw [f1 x hx]
    split
    · rw [htr x (by omega), le64_muMsg_lo _ (by omega)]
    · rfl
  have hfr : FrameExcept m M4 [(KS, KS + 800), (KB, KB + 800)] := by
    refine (((fr1.trans fr2).trans fr3).trans fr4).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, FIN]
  refine ⟨M4, ⟨hrc.frame hfr (by avoids_tac), hfr, fun x hx => ?_⟩, ?_⟩
  · rw [muLanes_zero]
    interval_cases x
{setup_cases}
  · exact ((((((r1.trans r2a).trans r2).trans r3a).trans r3).trans r4a).trans r4).mono (by norm_num)

theorem muLanes_lt (cd : ByteArray) (j x : Nat) : muLanes cd j x < 2 ^ 64 := by
  unfold muLanes
  apply Nat.xor_lt_two_pow (laneOf_lt _ _)
  split
  · exact le64_lt _ _
  · norm_num

theorem retOK_mu {{B ret : Nat}} {{tail : List UInt256}} (hB : B ≤ 1000) (htl : tail.length ≤ 8)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    RetOK B ret tail := retOK_main hB htl hj hret

/-- One loop visit absorbing the next full block. -/
theorem mu_iter {{s : State}} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {{m M : ByteArray}} (j : Nat) (hj : 136 * (j + 1) ≤ (muMsg s.executionEnv.calldata).size)
    (hI : MuInv s.executionEnv.calldata m M j) :
    ∃ M', MuInv s.executionEnv.calldata m M' (j + 1) ∧
      Reach (callState s 5727 [wd ((muMsg s.executionEnv.calldata).size - 136 * j), wd (3802 + 136 * j), flag b] M)
        (callState s 5727 [wd ((muMsg s.executionEnv.calldata).size - 136 * (j + 1)),
          wd (3802 + 136 * (j + 1)), flag b] M') (Gas.kf1 + Gas.absorb17 + 88) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hL := muMsg_size s.executionEnv.calldata hcd
  set L := (muMsg s.executionEnv.calldata).size
  have h1 := mu_loop1 hs b M (len := L - 136 * j) (off := 3802 + 136 * j) (by omega) (by omega)
  set S' := Fips202.xorBlock 136 (muPad s.executionEnv.calldata) (j * 136)
    (absorbPre 136 (muPad s.executionEnv.calldata) j)
  have hS' : S'.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M S' := fun x hx => by
    rw [hI.ks x hx, laneOf_xorBlock _ _ (absorbPre_size _ _ j) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad s.executionEnv.calldata =
        Fips202.pad 136 0x1F (muMsg s.executionEnv.calldata) from rfl, le64_pad_full _ (by omega),
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
        le64_muMsg_hi _ (a := 136 * (j + 1) + 8 * x) (by omega),
        show 3666 + (136 * (j + 1) + 8 * x) = 3802 + 136 * j + 8 * x by ring]
    · rw [Nat.xor_zero]
  · exact ((((h1.trans hc1).trans h2).trans hc2).trans h3).mono (by omega)

theorem mu_loop {{s : State}} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {{m M0 : ByteArray}} (hI0 : MuInv s.executionEnv.calldata m M0 0) :
    ∀ j, 136 * j ≤ (muMsg s.executionEnv.calldata).size →
      ∃ M, MuInv s.executionEnv.calldata m M j ∧
        Reach (callState s 5727 [wd (muMsg s.executionEnv.calldata).size, wd 3802, flag b] M0)
          (callState s 5727 [wd ((muMsg s.executionEnv.calldata).size - 136 * j),
            wd (3802 + 136 * j), flag b] M) (j * (Gas.kf1 + Gas.absorb17 + 88))
  | 0, _ => ⟨M0, hI0, by simpa using Reach.refl _⟩
  | j + 1, hj => by
    obtain ⟨M, hI, hR⟩ := mu_loop hs hcd b hI0 j (by omega)
    obtain ⟨M', hI', hR'⟩ := mu_iter hs hcd b j hj hI
    exact ⟨M', hI', (hR.trans hR').mono (by rw [Nat.succ_mul])⟩
'''+open('MlDsaOpt44/Main/Wp11Gen/mu_tail.lean').read()
open('MlDsaOpt44/Main/Mu/Proof.lean','w').write(src)
