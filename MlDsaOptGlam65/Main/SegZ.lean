import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Decode
import MlDsaOpt65.Math
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegZ.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `992 … 1101`: `dz` twice (`ZH`, `ZH2`), the norm-flag check (v4: no `dhint`).

`dz [ZH, Z0]` (`g = 0`), `OR` into the flag accumulator, `dz [ZH2, Z0 + 2560]` (`g = 1`),
its flag word masked to lane 0 (`z_4`), `OR`; `zBits` test (`ISZERO`): `okZ` by
`okZ_iff_zNormOk` (`ℓ = 5`). -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

/-- The flag test of segment zh: `zBits` against `f₀ ||| (f₁ &&& M64)`. -/
theorem S2.zflag_iff (f0 f1 : Nat) :
    (28269553878952482623322749181768732747635340874398564060972924832428589056 &&&
        (18446744073709551615 &&& f1 ||| f0)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 ↔
    (∀ j, j < 4 → f0 &&& zFlagBit j = 0) ∧ f1 &&& zFlagBit 0 = 0 := by
  have hz : (28269553878952482623322749181768732747635340874398564060972924832428589056 : Nat) =
      zFlagBit 0 ||| zFlagBit 1 ||| zFlagBit 2 ||| zFlagBit 3 := by unfold zFlagBit; decide
  have h0 : zFlagBit 0 &&& 18446744073709551615 = zFlagBit 0 := by unfold zFlagBit; decide
  have h1 : zFlagBit 1 &&& 18446744073709551615 = 0 := by unfold zFlagBit; decide
  have h2 : zFlagBit 2 &&& 18446744073709551615 = 0 := by unfold zFlagBit; decide
  have h3 : zFlagBit 3 &&& 18446744073709551615 = 0 := by unfold zFlagBit; decide
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by norm_num)), hz]
  simp only [Nat.and_or_distrib_right, Nat.and_or_distrib_left, Nat.or_eq_zero_iff,
    ← Nat.and_assoc, h0, h1, h2, h3, Nat.zero_and]
  simp only [Nat.and_comm _ f0, Nat.and_comm _ f1]
  constructor
  · intro H
    refine ⟨fun j hj => ?_, by tauto⟩
    interval_cases j <;> tauto
  · rintro ⟨h, ha⟩
    have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega); have := h 3 (by omega)
    tauto

theorem S2.allOnes_and (f : Nat) (hf : f < 2 ^ 256) :
    UInt256.ofNat (115792089237316195423570985008687907853269984665640564039457584007913129639935 &&&
      f ||| 0) = UInt256.ofNat f := by
  have hall : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat) =
      2 ^ 256 - 1 := by norm_num
  rw [hall, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hf, Nat.or_zero]

theorem S2.zh_b2 {s : State} (hs : Ctx s) {m : ByteArray} {f : Nat} (hf : f < 2 ^ 256) :
    Reach (callState s 29 [wd f, wd 0] m)
      (callState s Entry.dz [wd (ZH + 0x2000 * 1), wd (Z0 + 2560 * 1), wd 78, wd f] m) 30 := by
  glam65_rreach [14, 15, 16, 17, 18, 19, 20, 21, 22] with [ZH, Z0, Entry.dz]
  exact S2.allOnes_and f hf

theorem S2.zh_b3 {s : State} (hs : Ctx s) {m : ByteArray} {f0 f1 : Nat} {b : Bool}
    (hb : (∀ j, j < 4 → f0 &&& zFlagBit j = 0) ∧ f1 &&& zFlagBit 0 = 0 ↔ b = true) :
    Reach (callState s 78 [wd f1, wd f0] m) (callState s 124 [flag b] m) 19 := by
  glam65_rreach [23, 24, 25, 26, 27, 28, 29] with [flag]
  simp only [S2.zflag_iff, hb]

theorem seg_z {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv0 m) :
    ∃ m', Inv1 s.executionEnv.calldata m' ∧
      Reach (callState s 15 [] m) (callState s 124 [flag (okZ s.executionEnv.calldata)] m')
        Gas.pZ := by
  have hb1 : Reach (callState s 15 [] m)
      (callState s Entry.dz [wd (ZH + 0x2000 * 0), wd (Z0 + 2560 * 0), wd 29, wd 0] m) 22 := by
    glam65_rreach [8, 9, 10, 11, 12, 13] with [ZH, Z0, Entry.dz]
  obtain ⟨m1, f0, hf0, hfz0, hz0, hfr1, hc1⟩ := dz_call hs (ret := 29) (tail := [wd 0])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (g := 0) (by norm_num)
  have hb2 := S2.zh_b2 hs (m := m1) hf0
  obtain ⟨m2, f1, hf1, hfz1, hz1, hfr2, hc2⟩ := dz_call hs (ret := 78) (tail := [wd f0])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (g := 1) (by norm_num)
  have hok : (∀ j, j < 4 → f0 &&& zFlagBit j = 0) ∧ f1 &&& zFlagBit 0 = 0 ↔
      okZ s.executionEnv.calldata = true := by
    rw [okZ_iff_zNormOk _ hcd, show P.l = 5 from rfl]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hfz0 hfz1
    constructor
    · rintro ⟨h0, h1⟩ k hk
      by_cases h4 : k < 4
      · exact (hfz0 k h4).mp (h0 k h4)
      · rw [show k = 4 by omega]
        exact (hfz1 0 (by norm_num)).mp h1
    · intro h
      exact ⟨fun j hj => (hfz0 j hj).mpr (h _ (by omega)), (hfz1 0 (by norm_num)).mpr (h _ (by omega))⟩
  have hb3 := S2.zh_b3 hs (m := m2) hok
  have hzat : ZAt m2 s.executionEnv.calldata := by
    intro t ht
    have e0 := hz0 t ht
    have e1 := hz1 t ht
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one] at e0 e1
    constructor
    · rw [word_frame hfr2 (lo := ZH) (hi := ZH + 8192) (by avoids_tac) (by omega) (by omega), e0]
    · rw [show ZH2 + 32 * t = ZH + 8192 + 32 * t by unfold ZH2 ZH; omega, e1]
  refine ⟨m2, ⟨RC4Table.frame (RC4Table.frame hI.rc4 hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    RC1Table.frame (RC1Table.frame hI.rc1 hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    hzat,
    ZeroOn.frame (ZeroOn.frame (ZeroOn.mono hI.zero (le_refl _) (by unfold ZH TOP; omega))
      hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    ZeroOn.frame (ZeroOn.frame
      (ZeroOn.mono hI.zero (by unfold MISC BASES; omega) (by unfold FIN TOP; omega))
      hfr1 (by avoids_tac)) hfr2 (by avoids_tac)⟩, ?_⟩
  have := (((hb1.trans hc1).trans hb2).trans hc2).trans hb3
  exact this.mono (by unfold Gas.pZ; omega)
end MlDsaOptGlam65.Proofs
