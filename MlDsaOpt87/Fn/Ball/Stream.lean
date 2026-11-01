import MlDsaOpt87.Layout
import MlDsaOpt44.Math.SpongeSeed
set_option warningAsError true
/-!
# `sib` (ML-DSA-87): the SampleInBall stream as two squeezed `kf1` blocks

`H(c̃)` (272 bytes, `cStream`) is lane-wise the two permutations of the single-block seed
state of the 64-byte `c̃` (`seedState 136 (ctOf cd)`, lanes `laneOf_ctSeed`). The
ML-DSA-87 counterparts of `MlDsaOpt44/Math/SpongeSeed.lean` (`laneOf_ctSeed`) and
`MlDsaOpt44/Math/SpongeG234.lean` (`le64_cStream`).
-/

namespace MlDsaOpt87.Proofs.Ball

open MlDsaOpt44.Proofs (seedState laneOf_seedState absorb_single le64_shake256 byteAt_pad1
  byteAt_extract le64_congr le64_eq)
open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon

theorem ctOf_size {cd : ByteArray} (hcd : Z0 ≤ cd.size) : (ctOf cd).size = 64 := by
  unfold ctOf Z0 CTOFF at *; simp [ByteArray.size_extract]; omega

theorem byteAt_padCt {cd : ByteArray} (hcd : Z0 ≤ cd.size) {i : Nat} (hi : i < 136) :
    byteAt (MlDsa44.Fips202.pad 136 0x1F (ctOf cd)) i =
      if i < 64 then byteAt cd (2592 + i) else if i = 64 then 31 else if i = 135 then 128
      else 0 := by
  rw [byteAt_pad1 136 _ (by rw [ctOf_size hcd]; omega) i hi, ctOf_size hcd]
  by_cases h : i < 64
  · rw [if_pos h, if_pos h]; unfold ctOf
    rw [byteAt_extract _ _ _ _ (by unfold Z0 at hcd; exact hcd), if_pos (by unfold Z0 CTOFF; omega)]
    rfl
  · rw [if_neg h, if_neg h]
    split_ifs <;> first | rfl | omega

/-- Lanes of the SampleInBall seed state of `c̃` (ML-DSA-87: eight lanes). -/
theorem laneOf_ctSeed {cd : ByteArray} (hcd : Z0 ≤ cd.size) {x : Nat} (hx : x < 25) :
    laneOf (seedState 136 (ctOf cd)) x =
      if x < 8 then le64 cd (CTOFF + 8 * x) else if x = 8 then 31
      else if x = 16 then 2 ^ 63 else 0 := by
  rw [laneOf_seedState (by norm_num)]
  have hb := fun i (hi : i < 136) => byteAt_padCt hcd (i := i) hi
  by_cases h8 : x < 8
  · rw [if_pos (by norm_num; omega), if_pos h8]
    apply le64_congr
    intro k hk
    rw [hb _ (by omega), if_pos (by omega), CTOFF, Nat.add_assoc]
  rw [if_neg h8]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), le64_eq]
    by_cases hx8 : x = 8
    · subst hx8
      simp only [hb _ (by norm_num : 64 < 136), hb _ (by norm_num : 64 + 1 < 136),
        hb _ (by norm_num : 64 + 2 < 136), hb _ (by norm_num : 64 + 3 < 136),
        hb _ (by norm_num : 64 + 4 < 136), hb _ (by norm_num : 64 + 5 < 136),
        hb _ (by norm_num : 64 + 6 < 136), hb _ (by norm_num : 64 + 7 < 136)]
      norm_num
    · by_cases hx16 : x = 16
      · subst hx16
        simp only [hb _ (by norm_num : 128 < 136), hb _ (by norm_num : 128 + 1 < 136),
          hb _ (by norm_num : 128 + 2 < 136), hb _ (by norm_num : 128 + 3 < 136),
          hb _ (by norm_num : 128 + 4 < 136), hb _ (by norm_num : 128 + 5 < 136),
          hb _ (by norm_num : 128 + 6 < 136), hb _ (by norm_num : 128 + 7 < 136)]
        norm_num
      · have hz : ∀ k, k < 8 → byteAt (MlDsa44.Fips202.pad 136 0x1F (ctOf cd)) (8 * x + k) = 0 :=
          fun k hk => by
            rw [hb _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [show 8 * x = 8 * x + 0 from rfl, hz 0 (by omega), hz 1 (by omega), hz 2 (by omega),
          hz 3 (by omega), hz 4 (by omega), hz 5 (by omega), hz 6 (by omega), hz 7 (by omega),
          if_neg hx8, if_neg hx16]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega)]

/-- The SampleInBall stream: lanes of the first two squeezed blocks of `c̃`'s seed state. -/
theorem le64_cStream {cd : ByteArray} (hcd : Z0 ≤ cd.size) {j x : Nat} (hj : j < 2)
    (hx : x < 17) :
    le64 (cStream cd) (8 * (17 * j + x)) = laneOf (permN (j + 1) (seedState 136 (ctOf cd))) x := by
  unfold cStream MlDsa.Fips204.H MlDsa44.Fips202.shake256
  rw [le64_shake256 _ hx (by unfold MlDsa.Fips204.sampleInBallLimit; omega),
    absorb_single (by norm_num) (by rw [ctOf_size hcd]; omega)]
  unfold permN
  rw [Function.iterate_succ_apply]

end MlDsaOpt87.Proofs.Ball
