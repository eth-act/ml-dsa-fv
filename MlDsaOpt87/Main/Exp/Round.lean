import MlDsaOpt87.Main.Exp.Sponge
import MlDsaOpt87.Fn.Keccak
import MlDsaOpt87.Fn.Blk
set_option warningAsError true
/-!
# Rounds of the ExpandA SIMD groups (ML-DSA-87, v4)

* `kb_round`: glue, `kf4`, glue, `blk b` (`b < 4`); `kbh_round`: the same with
  `blkh` (block 4).

Entry points: `kf4` 22277, `blk` 10992, `blkh` 12170.
-/

namespace MlDsaOpt87.Proofs.Exp

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b < 4)
    (g1 : Reach (callState s pc0 stk m) (callState s 22277 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 10992 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
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
    (g1 : Reach (callState s pc0 stk m) (callState s 22277 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 12170 [wd (FL + 224 * 4), wd (ABUF + 1792 * 4), wd r2, fb] m') c2)
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

end MlDsaOpt87.Proofs.Exp
