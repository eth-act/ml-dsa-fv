import MlDsaOpt44.Fn.Sponge.Defs
import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt65.Fn.Mu0.Defs
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/MuMath.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568 --sub 12633=13221 --sub 12653=13242 --sub 12675=13265 --sub 12697=13288 --sub 12719=13311 --sub 12741=13334 --sub 12763=13357 --sub 12785=13380 --sub 12844=13439 --sub 12870=13465 --sub 12905=13500 --path Fn/Sponge/=Fn/Mu0/; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: imports `Fn/Mu0/Defs` (`muBlock` with the 65 `msgOf`); `--sub` relocates HDR 3732 → 5261, TRL 0xfd00 → 0x15d00
set_option warningAsError true
/-!
# Bytes and lanes of μ's single padded block (`mu0`)

`le64_muBlock`: lane `x < 17` of `muBlock tr cd` is the xor of the
contributions `mu0` absorbs separately: `tr` (lanes `0…7`, from `TRL`), the
calldata lanes `cd[5195 + 8x …]` (`trabs` from offset 5259), the two
signature bytes `cd[5259], cd[5260]` that `trabs` absorbed into lane 8 (xored
out again), the `0x1F` padding byte and the final `0x80`.
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

/-! ## Byte arrays (as in the reference's `Math/Shake/Bytes.lean`) -/

theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  unfold byteAt
  by_cases h : i < a.size
  · rw [if_pos h, dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h,
      ByteArray.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : i - a.size < b.size
    · rw [dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h2,
        ByteArray.getElem_append_right (by omega)]
    · rw [dif_neg (by rw [ByteArray.size_append]; omega), dif_neg h2]

theorem byteAt_eq_getElem! (b : ByteArray) (i : Nat) : byteAt b i = b[i]!.toNat := by
  rw [byteAt_eq_getD, getElem!_def]
  cases b[i]? <;> rfl

theorem byteAt_set! (b : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (hi : i < b.size) :
    byteAt (b.set! i v) j = if i = j then v.toNat else byteAt b j := by
  rw [byteAt_eq_getElem!, byteAt_eq_getElem!, ByteArray.getElem!_set! _ _ _ _ hi]
  split <;> rfl

theorem byteAt_replicate (n i : Nat) : byteAt (ByteArray.mk (Array.replicate n 0)) i = 0 := by
  unfold byteAt
  split
  · change (Array.replicate n (0 : UInt8))[i].toNat = 0
    rw [Array.getElem_replicate]; rfl
  · rfl

theorem byteAt_extract (b : ByteArray) (lo hi i : Nat) (hi' : hi ≤ b.size) :
    byteAt (b.extract lo hi) i = if i < hi - lo then byteAt b (lo + i) else 0 := by
  unfold byteAt
  have hs : (b.extract lo hi).size = hi - lo := by simp [ByteArray.size_extract]; omega
  by_cases h : i < hi - lo
  · rw [dif_pos (by omega), if_pos h, dif_pos (by omega), ByteArray.getElem_extract]
  · rw [dif_neg (by omega), if_neg h]

theorem byteAt_of_size_le {b : ByteArray} {i : Nat} (h : b.size ≤ i) : byteAt b i = 0 := by
  unfold byteAt; rw [dif_neg (by omega)]

/-- Bytes of a single padded block (`msg.size < rate`). -/
theorem byteAt_pad1 (rate : Nat) (msg : ByteArray) (hm : msg.size < rate) (i : Nat) (hi : i < rate) :
    byteAt (Fips202.pad rate 0x1F msg) i =
      if i < msg.size then byteAt msg i
      else (if i = msg.size then 31 else 0) ||| (if i = rate - 1 then 128 else 0) := by
  unfold Fips202.pad
  simp only
  rw [byteAt_append]
  by_cases h : i < msg.size
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hmod : msg.size % rate = msg.size := Nat.mod_eq_of_lt hm
    rw [hmod]
    have hsz0 : ((ByteArray.mk (Array.replicate (rate - msg.size) 0))).size = rate - msg.size := by
      change (Array.replicate _ (0 : UInt8)).size = _; rw [Array.size_replicate]
    have hsz1 : ((ByteArray.mk (Array.replicate (rate - msg.size) 0)).set! 0 0x1F).size =
        rate - msg.size := by rw [ByteArray.size_set!, hsz0]
    rw [byteAt_set! _ _ _ _ (by rw [hsz1]; omega), byteAt_set! _ _ _ _ (by rw [hsz0]; omega),
      byteAt_replicate]
    rw [ByteArray.getElem!_set! _ _ _ _ (by rw [hsz0]; omega)]
    have hz : ((ByteArray.mk (Array.replicate (rate - msg.size) 0))[rate - msg.size - 1]!) = 0 := by
      have := byteAt_replicate (rate - msg.size) (rate - msg.size - 1)
      rw [byteAt_eq_getElem!] at this
      exact UInt8.toNat_inj.mp this
    rw [hz]
    split_ifs <;> first | rfl | omega

/-! ## Bytes of `muBlock` -/

theorem msgOf_size (cd : ByteArray) : (msgOf cd).size = cd.size - 5261 := by
  simp [msgOf, HDR, ByteArray.size_extract]  -- port: `HDR` is a definition in 65

theorem byteAt_mu {tr cd : ByteArray} (htr : tr.size = 64) (hml : cd.size - 5261 ≤ 69)
    {i : Nat} (hi : i < 136) :
    byteAt (muBlock tr cd) i =
      if i < 64 then byteAt tr i else
        ((if 66 ≤ i then byteAt cd (5195 + i) else 0) |||
          (if i = 66 + (cd.size - 5261) then 31 else 0)) ||| (if i = 135 then 128 else 0) := by
  have h2 : (ByteArray.mk #[(0 : UInt8), 0]).size = 2 := rfl
  have hsz : (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size = 66 + (cd.size - 5261) := by
    simp only [ByteArray.size_append, htr, h2, msgOf_size]; omega
  unfold muBlock
  rw [byteAt_pad1 _ _ (by omega) i hi, hsz]
  by_cases h1 : i < 66 + (cd.size - 5261)
  · rw [if_pos h1, byteAt_append, htr]
    by_cases h64 : i < 64
    · rw [if_pos h64, if_pos h64]
    · rw [if_neg h64, if_neg h64, byteAt_append, h2]
      by_cases h66 : i - 64 < 2
      · rw [if_pos h66, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have : i - 64 = 0 ∨ i - 64 = 1 := by omega
        rcases this with h | h <;> rw [h] <;> rfl
      · rw [if_neg h66, msgOf, HDR, byteAt_extract _ _ _ _ (le_refl _), if_pos (by omega),  -- port: unfold `HDR`
          if_pos (by omega), if_neg (by omega), if_neg (by omega),
          show 5261 + (i - 64 - 2) = 5195 + i by omega]
        simp
  · have h64 : ¬ i < 64 := by omega
    have h66 : 66 ≤ i := by omega
    rw [if_neg h1, if_neg h64, if_pos h66, byteAt_of_size_le (show cd.size ≤ 5195 + i by omega),
      Nat.zero_or]

/-! ## Lanes -/

/-- The calldata-derived lane bytes of `mu0`, as the code absorbs them. -/
def muByte (tr cd : ByteArray) (x q : Nat) : Nat :=
  (if x < 8 then byteAt tr (8 * x + q) else 0) ^^^
  (if 8 ≤ x then byteAt cd (5195 + 8 * x + q) else 0) ^^^
  (if x = 8 ∧ q = 0 then byteAt cd 5259 else if x = 8 ∧ q = 1 then byteAt cd 5260 else 0) ^^^
  (if 8 * x + q = 66 + (cd.size - 5261) then 31 else 0) ^^^
  (if x = 16 ∧ q = 7 then 128 else 0)

theorem byteAt_mu_eq {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    (hml : cd.size - 5261 ≤ 69) {x q : Nat} (hx : x < 17) (hq : q < 8) :
    byteAt (muBlock tr cd) (8 * x + q) = muByte tr cd x q := by
  rw [byteAt_mu htr hml (by omega)]
  unfold muByte
  by_cases hx8 : x < 8
  · have h1 : 8 * x + q < 64 := by omega
    rw [if_pos h1, if_pos hx8, if_neg (show ¬ 8 ≤ x by omega),
      if_neg (show ¬ (x = 8 ∧ q = 0) by omega), if_neg (show ¬ (x = 8 ∧ q = 1) by omega),
      if_neg (show ¬ (8 * x + q = 66 + (cd.size - 5261)) by omega),
      if_neg (show ¬ (x = 16 ∧ q = 7) by omega)]
    simp
  · have h1 : ¬ 8 * x + q < 64 := by omega
    rw [if_neg h1, if_neg hx8, if_pos (show 8 ≤ x by omega), Nat.zero_xor]
    by_cases h66 : 66 ≤ 8 * x + q
    · rw [if_pos h66, if_neg (show ¬ (x = 8 ∧ q = 0) by omega),
        if_neg (show ¬ (x = 8 ∧ q = 1) by omega), Nat.xor_zero,
        show 5195 + (8 * x + q) = 5195 + 8 * x + q by omega]
      by_cases hp : 8 * x + q = 66 + (cd.size - 5261)
      · rw [if_pos hp, byteAt_of_size_le (show cd.size ≤ 5195 + 8 * x + q by omega),
          Nat.zero_or, Nat.zero_xor]
        by_cases ht : 8 * x + q = 135
        · rw [if_pos ht, if_pos (show x = 16 ∧ q = 7 by omega)]; rfl
        · rw [if_neg ht, if_neg (show ¬ (x = 16 ∧ q = 7) by omega)]; rfl
      · rw [if_neg hp, Nat.or_zero, Nat.xor_zero]
        by_cases ht : 8 * x + q = 135
        · rw [if_pos ht, if_pos (show x = 16 ∧ q = 7 by omega),
            byteAt_of_size_le (show cd.size ≤ 5195 + 8 * x + q by omega)]; rfl
        · rw [if_neg ht, if_neg (show ¬ (x = 16 ∧ q = 7) by omega), Nat.or_zero, Nat.xor_zero]
    · have hx8' : x = 8 := by omega
      subst hx8'
      rw [if_neg h66, if_neg (show ¬ (8 * 8 + q = 66 + (cd.size - 5261)) by omega),
        if_neg (show ¬ (8 * 8 + q = 135) by omega), if_neg (show ¬ ((8 : Nat) = 16 ∧ q = 7) by omega),
        Nat.zero_or, Nat.zero_or, Nat.xor_zero, Nat.xor_zero]
      have : q = 0 ∨ q = 1 := by omega
      rcases this with rfl | rfl
      · simp
      · simp

/-- The five contributions to lane `x` of μ's block, in `mu0`'s absorption order. -/
def muTr (tr : ByteArray) (x : Nat) : Nat := if x < 8 then le64 tr (8 * x) else 0
def muCd (cd : ByteArray) (x : Nat) : Nat := if 8 ≤ x then le64 cd (5195 + 8 * x) else 0
def muFix (cd : ByteArray) (x : Nat) : Nat :=
  if x = 8 then byteAt cd 5259 + 256 * byteAt cd 5260 else 0
def muPad (cd : ByteArray) (x : Nat) : Nat :=
  if x = (66 + (cd.size - 5261)) / 8 then 31 * 2 ^ (8 * ((66 + (cd.size - 5261)) % 8)) else 0
def muTop (x : Nat) : Nat := if x = 16 then 2 ^ 63 else 0

theorem testBit_ite (c : Prop) [Decidable c] (v j : Nat) :
    (if c then v else 0).testBit j = (decide c && v.testBit j) := by
  split <;> simp [*]

theorem testBit_muTr (tr : ByteArray) (x : Nat) {j : Nat} (hj : j < 64) :
    (muTr tr x).testBit j = (if x < 8 then byteAt tr (8 * x + j / 8) else 0).testBit (j % 8) := by
  unfold muTr; rw [testBit_ite, testBit_ite, testBit_le64]; simp [hj]

theorem testBit_muCd (cd : ByteArray) (x : Nat) {j : Nat} (hj : j < 64) :
    (muCd cd x).testBit j =
      (if 8 ≤ x then byteAt cd (5195 + 8 * x + j / 8) else 0).testBit (j % 8) := by
  unfold muCd; rw [testBit_ite, testBit_ite, testBit_le64]; simp [hj]

theorem testBit_muFix (cd : ByteArray) (x : Nat) {j : Nat} (hj : j < 64) :
    (muFix cd x).testBit j =
      (if x = 8 ∧ j / 8 = 0 then byteAt cd 5259 else if x = 8 ∧ j / 8 = 1 then byteAt cd 5260
        else 0).testBit (j % 8) := by
  unfold muFix
  have ha := byteAt_lt cd 5259
  have hb := byteAt_lt cd 5260
  by_cases hx : x = 8
  · rw [if_pos hx, show byteAt cd 5259 + 256 * byteAt cd 5260 =
      byteAt cd 5259 + byteAt cd 5260 * 2 ^ 8 by ring, testBit_add_two_pow_mul (by omega)]
    by_cases h0 : j < 8
    · rw [if_pos h0, if_pos (show x = 8 ∧ j / 8 = 0 by omega), show j % 8 = j by omega]
    · rw [if_neg h0, if_neg (show ¬ (x = 8 ∧ j / 8 = 0) by omega)]
      by_cases h1 : j < 16
      · rw [if_pos (show x = 8 ∧ j / 8 = 1 by omega), show j - 8 = j % 8 by omega]
      · have h8 : 2 ^ 8 ≤ 2 ^ (j - 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [if_neg (show ¬ (x = 8 ∧ j / 8 = 1) by omega),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb h8)]
        simp
  · rw [if_neg hx, if_neg (show ¬ (x = 8 ∧ j / 8 = 0) by omega),
      if_neg (show ¬ (x = 8 ∧ j / 8 = 1) by omega)]
    simp

theorem testBit_muPad (cd : ByteArray) (x : Nat) {j : Nat} (hj : j < 64) :
    (muPad cd x).testBit j =
      (if 8 * x + j / 8 = 66 + (cd.size - 5261) then 31 else 0).testBit (j % 8) := by
  unfold muPad
  generalize 66 + (cd.size - 5261) = p
  rw [testBit_ite, testBit_ite, Nat.mul_comm 31, Nat.testBit_two_pow_mul]
  by_cases hx : x = p / 8
  · by_cases hq : j / 8 = p % 8
    · have e1 : 8 * x + j / 8 = p := by omega
      have e2 : 8 * (p % 8) ≤ j := by omega
      have e3 : j - 8 * (p % 8) = j % 8 := by omega
      subst hx
      simp [e1, e2, e3]
    · have e1 : ¬ (8 * x + j / 8 = p) := by omega
      rw [decide_eq_false e1, Bool.false_and]
      by_cases hle : 8 * (p % 8) ≤ j
      · have h5 : (31 : Nat).testBit (j - 8 * (p % 8)) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show (31 : Nat) < 2 ^ 5 by norm_num)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h5]
      · simp [hle]
  · have e1 : ¬ (8 * x + j / 8 = p) := by omega
    simp [hx, e1]

theorem testBit_muTop (x : Nat) {j : Nat} (_hj : j < 64) :
    (muTop x).testBit j = (if x = 16 ∧ j / 8 = 7 then 128 else 0).testBit (j % 8) := by
  unfold muTop
  rw [testBit_ite, testBit_ite, Nat.testBit_two_pow]
  have : (128 : Nat) = 2 ^ 7 := rfl
  rw [this, Nat.testBit_two_pow, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem testBit_xor5 (a b c d e j : Nat) :
    (a ^^^ b ^^^ c ^^^ d ^^^ e).testBit j =
      (a.testBit j ^^ b.testBit j ^^ c.testBit j ^^ d.testBit j ^^ e.testBit j) := by
  simp only [Nat.testBit_xor]

theorem le64_lt64 (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 64 := (le64_partial b a 8).1

theorem muTr_lt (tr : ByteArray) (x : Nat) : muTr tr x < 2 ^ 64 := by
  unfold muTr; split
  · exact le64_lt64 tr _
  · norm_num

theorem muCd_lt (cd : ByteArray) (x : Nat) : muCd cd x < 2 ^ 64 := by
  unfold muCd; split
  · exact le64_lt64 cd _
  · norm_num

theorem muFix_lt (cd : ByteArray) (x : Nat) : muFix cd x < 2 ^ 64 := by
  have := byteAt_lt cd 5259; have := byteAt_lt cd 5260
  unfold muFix; split <;> omega

theorem muPad_lt (cd : ByteArray) (x : Nat) : muPad cd x < 2 ^ 64 := by
  unfold muPad; split
  · have h : (66 + (cd.size - 5261)) % 8 < 8 := Nat.mod_lt _ (by omega)
    generalize (66 + (cd.size - 5261)) % 8 = r at h
    interval_cases r <;> norm_num
  · norm_num

theorem muTop_lt (x : Nat) : muTop x < 2 ^ 64 := by
  unfold muTop; split <;> norm_num

/-- **Lane `x` of μ's padded block.** -/
theorem le64_muBlock {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    (hml : cd.size - 5261 ≤ 69) {x : Nat} (hx : x < 17) :
    le64 (muBlock tr cd) (8 * x) =
      muTr tr x ^^^ muCd cd x ^^^ muFix cd x ^^^ muPad cd x ^^^ muTop x := by
  apply eq_of_testBit_lt (n := 64) (le64_lt64 _ _)
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
      (muTr_lt tr x) (muCd_lt cd x)) (muFix_lt cd x)) (muPad_lt cd x)) (muTop_lt x))
  intro j hj
  rw [testBit_le64, decide_eq_true hj, Bool.true_and,
    byteAt_mu_eq htr hcd hml hx (Nat.div_lt_of_lt_mul (by omega)), muByte, testBit_xor5,
    testBit_xor5, testBit_muTr _ _ hj, testBit_muCd _ _ hj, testBit_muFix _ _ hj,
    testBit_muPad _ _ hj, testBit_muTop _ hj]

end MlDsaOpt65.Proofs.WP4
