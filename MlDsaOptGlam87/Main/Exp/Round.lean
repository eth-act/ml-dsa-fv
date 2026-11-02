import MlDsaOptGlam87.Main.Exp.Sponge
import MlDsaOptGlam87.Fn.Keccak
import MlDsaOptGlam87.Fn.Blk
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Exp/Round.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Rounds of the ExpandA SIMD groups (ML-DSA-87, v4)

* `kb_round`: glue, `kf4`, glue, `blk b` (`b < 4`); `kbh_round`: the same with
  `blkh` (block 4).

Entry points: `kf4` 22277, `blk` 10992, `blkh` 12170.
-/

namespace MlDsaOptGlam87.Proofs.Exp

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs hiding ACC AccAt AccAt.frame BASES BK CB CRep CRep.frame CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN FinAt FinMu FinMu.frame H0 HDR HP HPAt HPAt.frame IDX Inv0 Inv1 Inv2 Inv3 Inv4 Inv6 Inv7 Inv8 Inv9 InvH InvW KZ MU RC1Table.frame RC4Table.frame RHO1 RetOK Rho1At Rho1At.frame SP SibFresh SibFresh.frame TOP TRL TTable TblAt.frame Z0 ZAt ZAt.frame ZHatAt ZHatAt.frame ZeroOn.frame ZeroOn.mono aD aOf azRow baseOf cD cOf cStream cStream_size codeOf csum_congr ctOf finBytes finBytes_le64_mu finBytes_le64_w1 ginitWord hintBitUnpack_range hintD hintOf memWords mlenOf msgOf muOf nNeg negCount nttInv_congr nttInv_range ntt_zLane ok2 ok3 okA okC okCol okH okZ optAccepts padPk pkOf rawZ rejNTTPoly_range rhoOf sPrime sampleInBallOf_coeffs sigOf spOff t1Of t1v tEntry trOf useHint_emod useHint_range w1Of wRow word_frame zHat zHi zLane zLo zPolys
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs
open MlDsaOptGlam87.Proofs.Infra

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b < 4)
    (g1 : Reach (callState s pc0 stk m) (callState s 41770 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 10846 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ HBlocks m' St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * b, ABUF + 1792 * b + 1792),
        (FL + 224 * b, FL + 224 * b + 224)] ∧
      Reach (callState s pc0 stk m) (callState s r2 [fb] m') (c1 + Gas.kf4 + c2 + Gas.blk) := by
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := [fb])
    (retOK_main (by decide) (by simp) hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blk_call hs (ret := r2) (tail := [fb])
    (retOK_main (by decide) (by simp) hj2 hr2) m1 (abp := ABUF + 1792 * b) (flp := FL + 224 * b)
    (by unfold KS ABUF; omega) (by unfold TOP ABUF; omega) (by unfold KS FL; omega)
    (by unfold TOP FL; omega) (by unfold ABUF FL; omega)
  obtain ⟨hA, hF⟩ := hbk _ (sized4_permute hS) hks1
  have ha2 : Avoids [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS, ABUF, FL]; omega
  have hB1 := hB.frame hf1 (by avoids_tac) (by avoids_tac)
  refine ⟨m2, KS4.frame hks1 hf2 ha2, fun b' hb' => ?_, RC4Table.frame (RC4Table.frame hrc hf1
      (by avoids_tac)) hf2 (by simp only [avoids_cons, avoids_nil, and_true, RC4, ABUF, FL]; omega),
    FrameExcept.trans hf1 hf2, ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = b
  · subst hbb
    exact ⟨fun i hi _ => by rw [hA i hi]; exact pack4_congr fun k hk => by rw [hSt k hk],
      fun g hg _ => by rw [hF g hg]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · exact (hB1.frame hf2 (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)) b' (by omega)

/-- The last squeeze of a group: glue, `kf4`, glue, `blkh` (block 4). -/
theorem kbh_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 : Nat}
    (g1 : Reach (callState s pc0 stk m) (callState s 41770 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 10852 [wd (FL + 224 * 4), wd (ABUF + 1792 * 4), wd r2, fb] m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m St 4)
    (hSt : ∀ k, k < 4 → St 4 k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ HBlocks m' St 5 ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * 4, ABUF + 1792 * 4 + 1024),
        (FL + 224 * 4, FL + 224 * 4 + 128)] ∧
      Reach (callState s pc0 stk m) (callState s r2 [fb] m') (c1 + Gas.kf4 + c2 + Gas.blkh) := by
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := [fb])
    (retOK_main (by decide) (by simp) hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blkh_call hs (ret := r2) (tail := [fb])
    (retOK_main (by decide) (by simp) hj2 hr2) m1 (abp := ABUF + 1792 * 4) (flp := FL + 224 * 4)
    (by unfold KS ABUF; omega) (by unfold TOP ABUF; omega) (by unfold KS FL; omega)
    (by unfold TOP FL; omega) (by unfold ABUF FL; omega)
  obtain ⟨hA, hF⟩ := hbk _ (sized4_permute hS) hks1
  have ha2 : Avoids [(ABUF + 1792 * 4, ABUF + 1792 * 4 + 1024), (FL + 224 * 4, FL + 224 * 4 + 128)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS, ABUF, FL]; omega
  have hB1 := hB.frame hf1 (by avoids_tac) (by avoids_tac)
  refine ⟨m2, KS4.frame hks1 hf2 ha2, fun b' hb' => ?_, RC4Table.frame (RC4Table.frame hrc hf1
      (by avoids_tac)) hf2 (by simp only [avoids_cons, avoids_nil, and_true, RC4, ABUF, FL]; omega),
    FrameExcept.trans hf1 hf2, ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = 4
  · subst hbb
    exact ⟨fun i _ hh => by rw [hA i (by omega)]; exact pack4_congr fun k hk => by rw [hSt k hk],
      fun g _ hh => by rw [hF g (by omega)]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · exact (hB1.frame hf2 (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)) b' (by omega)

end MlDsaOptGlam87.Proofs.Exp
