import MlDsaOptGlam44.Main.Alt.MuBlocks
import MlDsaOptGlam44.Main.Mu.Proof
import MlDsaOptGlam44.Main.Alt.Inv
import MlDsaOptGlam44.Gas
set_option maxHeartbeats 0
set_option warningAsError true
/-! # Long-message schedule, `5183 … 6020`: μ with `FLAG = 0`

`|M| ≤ 613` (calldata shorter than `0x10fa = 4346`): μ's lanes in `MU`
(`InvWA.mu`), replicated into `FIN[0, 8)`. Otherwise `hash_mu` jumps to
`muimg`: μ's sponge after blocks `0 … 4` is slot 1 of the kf4 state in `KS`
(`InvWA.muks`); it is extracted in place (`cext 25, 1, KS`), replicated for
`kf1`, block 5 (calldata 4346) is absorbed, and the `kf1` / `absorb17` loop of
`Main/Mu/Proof.lean` continues from `MuInv … 5`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

set_option maxHeartbeats 400000 in
/-- The long path's setup (`5183 … 5821`, `FLAG = 0`): μ's sponge after blocks
`0 … 4` from slot 1 of `KS`, as a `kf1` state, with block 5's raw lanes
absorbed. -/
theorem mu0_setup {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) (b : Bool)
    {m : ByteArray} {S : Nat → Fips202.SpongeState} (hK : KS4 m S)
    (hS1 : S 1 = absorbPre 136 (padMu s.executionEnv.calldata) 5) (hrc : RC1Table m)
    (hl : 4346 ≤ s.executionEnv.calldata.size) (hfl : word m FLAG = 0) :
    ∃ M, MuInv s.executionEnv.calldata m M 5 ∧
      Reach (callState s 5183 [flag b] m)
        (callState s 5821 [wd ((muMsgW s.executionEnv.calldata).size - 136 * 5),
          wd (3802 + 136 * 5), flag b] M) (41 + 637 + Gas.cext 25 + Gas.absorb17) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have r0 := mu0_chk_long hs b m hfit hl hfl
  have r1 := mu0_img hs b m hfl
  have r2 := mu_cext_pre hs b m
  obtain ⟨m2, hc2, hf2, hcall2⟩ := cext_inplace_call hs (ret := 5517) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (sh := 1) (n := 25) (by norm_num) (by norm_num) (by norm_num)
  have hv2 : ∀ x, x < 25 → word m2 (KS + 32 * x) = laneOf (S 1) x := fun x hx => by
    rw [hc2 x hx]; exact cext_lane hK (by norm_num) hx
  obtain ⟨m3, hA, rA⟩ := mu_repA hs b m2 (rep_hT hv2 (FrameExcept.refl _ []) (by norm_num)
    (fun _ _ _ => by simp))
  obtain ⟨m4, hB, rB⟩ := mu_repB hs b m3 (rep_hT hv2 hA.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAB := hA.trans hB (by norm_num) (by norm_num)
  obtain ⟨m5, hC, rC⟩ := mu_repC hs b m4 (rep_hT hv2 hAB.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAC := hAB.trans hC (by norm_num) (by norm_num)
  obtain ⟨m6, hD, rD⟩ := mu_repD hs b m5 (rep_hT hv2 hAC.2 (by norm_num)
    (fun x h1 _ => by simp only [avoids_cons, avoids_nil, and_true]; omega))
  have hAD := hAC.trans hD (by norm_num) (by norm_num)
  have hK1 : ∀ x, x < 25 → word m6 (KS + 32 * x) =
      rep (cpl x (laneOf (absorbPre 136 (muPad s.executionEnv.calldata) 5) x)) := fun x hx => by
    rw [hAD.1 x (Nat.zero_le _) hx, hv2 x hx, hS1]; rfl
  have hfl6 : word m6 FLAG = 0 := by
    rw [word_frame (hf2.trans hAD.2) (lo := FLAG) (hi := FLAG + 32)
      (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl
  have r3 := mu0_abs1 hs b m6 hfl6
  obtain ⟨m7, ha7, hf7, hc7⟩ := WP4.absorb17_call_aux hs (ret := 5803) (tail := [wd 4346, flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (off := 4346) (by norm_num)
  have hfl7 : word m7 FLAG = 0 := by
    rw [word_frame hf7 (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl6
  have r4 := mu0_head0 hs b m7 hfit hl hfl7
  have hL := muMsgW_size s.executionEnv.calldata hcd
  rw [show s.executionEnv.calldata.size - 4346 = (muMsgW s.executionEnv.calldata).size - 136 * 5 by
    omega, show (4482 : Nat) = 3802 + 136 * 5 by rfl] at r4
  rw [call_iff] at hcall2 hc7
  have hfr := ((hf2.trans hAD.2).trans hf7)
  refine ⟨m7, ⟨hrc.frame hfr (by avoids_tac), frame3_mono hfr (by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [KS]), fun x hx => ?_⟩, ?_⟩
  · rw [ha7 x hx, hK1 x hx]
    unfold muLanes
    split
    · rw [rep_cpl_xor _ (laneOf_lt _ _) (le64_lt _ _),
        le64_muMsgW_hi _ (a := 136 * 5 + 8 * x) (by omega),
        show 3666 + (136 * 5 + 8 * x) = 4346 + 8 * x by ring]
    · rw [Nat.xor_zero]
  · refine (((((((((r0.trans r1).trans r2).trans hcall2).trans rA).trans rB).trans
      rC).trans rD).trans r3).trans hc7).trans r4 |>.mono ?_
    unfold Gas.cext
    generalize Gas.absorb17 = g
    omega

theorem seg_muA {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvHA s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6A s.executionEnv.calldata m' ∧
      Reach (callState s 5183 [flag b] m) (callState s 6020 [flag b] m')
        (Gas.pMuA (mlenOf s.executionEnv.calldata)) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hl : 3732 ≤ s.executionEnv.calldata.size := hcd
  -- the invariant from any frame avoiding the Keccak buffers and `FIN`
  have inv6 : ∀ M', FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] →
      FinMu M' s.executionEnv.calldata → RC1Table M' → Inv6A s.executionEnv.calldata M' :=
    fun M' hfr hmu hrc =>
      { rc1 := hrc
        tbl := hI.tbl.frame hfr (by avoids_tac)
        hp := hI.hp.frame hfr (by avoids_tac)
        acc := hI.acc.frame hfr (by avoids_tac)
        cb := fun x hx => by
          rw [word_frame hfr (lo := CB) (hi := CB + 1088) (by avoids_tac) (by omega) (by omega)]
          exact hI.cb x hx
        fresh := SibFresh.frame ⟨hI.zCw, hI.zIdx, hI.zNeg⟩ hfr (by avoids_tac) (by avoids_tac)
          (by avoids_tac)
        fmu := hmu
        flag0 := by
          rw [word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
          exact hI.flag0 }
  by_cases hsh : mlenOf s.executionEnv.calldata ≤ 613
  · have hlt : s.executionEnv.calldata.size < 4346 := by unfold mlenOf at hsh; omega
    obtain ⟨M', f, fr, r⟩ := mu0_short hs b m hfit hlt (fun x hx => by
      rw [hI.mu hsh x hx]; exact le64_lt _ _) hI.flag0
    have hfr : FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (FIN, FIN + 256)] := by
      refine fr.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [KS, KB, KZ, FIN]
    refine ⟨M', inv6 M' hfr (fun x hx => by rw [f x hx, hI.mu hsh x hx])
      (hI.rc1.frame fr (by avoids_tac)), ?_⟩
    unfold Gas.pMuA; rw [if_pos hsh]; exact r
  · have hlong : 4346 ≤ s.executionEnv.calldata.size := by unfold mlenOf at hsh; omega
    obtain ⟨S, -, hK, hS1⟩ := hI.muks (by omega)
    obtain ⟨M0, hI0, r1⟩ := mu0_setup hs hcd b hK hS1 hI.rc1 hlong hI.flag0
    have hL := muMsgW_size s.executionEnv.calldata hcd
    set L := (muMsgW s.executionEnv.calldata).size with hLdef
    have hn5 : 5 ≤ L / 136 := by omega
    obtain ⟨M, hIn, r2⟩ := mu_loop hs hcd b hI0 (L / 136 - 5)
      (by rw [show 5 + (L / 136 - 5) = L / 136 by omega]; exact Nat.mul_div_le _ _)
    rw [show 5 + (L / 136 - 5) = L / 136 by omega] at hIn r2
    obtain ⟨M', hmu, hrc, hfr, r3⟩ := mu_finish hs b hIn
    refine ⟨M', inv6 M' hfr hmu hrc, ((r1.trans r2).trans r3).mono ?_⟩
    have hk : (mlenOf s.executionEnv.calldata - 614) / 136 = L / 136 - 5 := by
      unfold mlenOf; omega
    unfold Gas.pMuA
    rw [if_neg hsh, hk]
    generalize (L / 136 - 5) * (Gas.kf1 + Gas.absorb17 + 88) = P
    generalize Gas.kf1 = k1
    generalize Gas.absorb17 = a17
    generalize Gas.cext 25 = c25
    omega

end MlDsaOptGlam44.Proofs
