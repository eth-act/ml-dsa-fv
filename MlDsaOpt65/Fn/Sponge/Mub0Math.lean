import MlDsaOpt65.Fn.Mu0.MuFinal  -- port: the 65 μ lane lemmas (HDR 5261)
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/Mub0Math.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568; hand adjustments are marked `-- port:`. -/
-- port: `msgOf` unfolds to the 65 `HDR` (a definition): `byteAt_mu0U` unfolds it
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
/-!
# Lanes of μ's unpadded block 0 (`mub0` for `|M| > 69`)

`le64_mu0U`: lane `x < 17` of `tr ‖ 0 ‖ 0 ‖ M` is the xor of the `tr` lane,
the calldata lane `cd[5195 + 8x …]` and the two signature bytes xored out of
lane 8 (`MuMath`'s `muTr`, `muCd`, `muFix`). `mub0_value_long`: the state
words after `mub0`'s path without padding.
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem byteAt_mu0U {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size) (i : Nat) :
    byteAt (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) i =
      if i < 64 then byteAt tr i else if 66 ≤ i then byteAt cd (5195 + i) else 0 := by
  have h2 : (ByteArray.mk #[(0 : UInt8), 0]).size = 2 := rfl
  rw [byteAt_append, htr]
  by_cases h64 : i < 64
  · rw [if_pos h64, if_pos h64]
  · rw [if_neg h64, if_neg h64, byteAt_append, h2]
    by_cases h66 : i - 64 < 2
    · rw [if_pos h66, if_neg (by omega)]
      have : i - 64 = 0 ∨ i - 64 = 1 := by omega
      rcases this with h | h <;> rw [h] <;> rfl
    · rw [if_neg h66, if_pos (by omega), msgOf, HDR, byteAt_extract _ _ _ _ (le_refl _)]  -- port: unfold `HDR`
      by_cases hc : i - 64 - 2 < cd.size - 5261
      · rw [if_pos hc, show 5261 + (i - 64 - 2) = 5195 + i by omega]
      · rw [if_neg hc, byteAt_of_size_le (by omega)]

/-- **Lane `x` of μ's unpadded block 0.** -/
theorem le64_mu0U {tr cd : ByteArray} (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    {x : Nat} (hx : x < 17) :
    le64 (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) (8 * x) =
      muTr tr x ^^^ muCd cd x ^^^ muFix cd x := by
  apply eq_of_testBit_lt (n := 64) (le64_lt64 _ _)
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (muTr_lt tr x) (muCd_lt cd x)) (muFix_lt cd x))
  intro j hj
  rw [testBit_le64, decide_eq_true hj, Bool.true_and, byteAt_mu0U htr hcd, Nat.testBit_xor,
    Nat.testBit_xor, testBit_muTr _ _ hj, testBit_muCd _ _ hj, testBit_muFix _ _ hj]
  have hq : j / 8 < 8 := by omega
  by_cases hx8 : x < 8
  · rw [if_pos (show 8 * x + j / 8 < 64 by omega), if_pos hx8, if_neg (show ¬ 8 ≤ x by omega),
      if_neg (show ¬ (x = 8 ∧ j / 8 = 0) by omega), if_neg (show ¬ (x = 8 ∧ j / 8 = 1) by omega)]
    simp
  · rw [if_neg (show ¬ 8 * x + j / 8 < 64 by omega), if_neg hx8, if_pos (show 8 ≤ x by omega)]
    by_cases h66 : 66 ≤ 8 * x + j / 8
    · rw [if_pos h66, if_neg (show ¬ (x = 8 ∧ j / 8 = 0) by omega),
        if_neg (show ¬ (x = 8 ∧ j / 8 = 1) by omega),
        show 5195 + (8 * x + j / 8) = 5195 + 8 * x + j / 8 by omega]
      simp
    · rw [if_neg h66]
      have hx8' : x = 8 := by omega
      subst hx8'
      have : j / 8 = 0 ∨ j / 8 = 1 := by omega
      rcases this with h | h <;> simp [h]

set_option maxHeartbeats 1000000 in
/-- The state words after `mub0`'s path for `|M| > 69` (no padding). -/
theorem mub0_value_long {m m8 m9 m10 tr cd : ByteArray} {sh : Nat} (hsh : sh < 4)
    (htr : tr.size = 64) (hcd : 5261 ≤ cd.size)
    (hTRL : ∀ x, x < 8 → word m (89344 + 32 * x) = le64 tr (8 * x))
    (h8 : ∀ x, word m8 (32 * x) = if x < 8 then
        (word m (32 * x) ^^^ sprNet (word m (89344 + 32 * x)) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
        else word m (32 * x))
    (h9 : ∀ x, x < 25 → word m9 (32 * x) = if 8 ≤ x ∧ x < 20 then
        word m8 (32 * x) ^^^ spread (trLane cd 5259
          115792089237316195417293883273301227089434195242432897623355228563449095127040 3 (x - 8)) *
            2 ^ sh
        else word m8 (32 * x))
    (h10 : m10 = MachineState.writeBytes m9 (Data.Bytes.natToBytesPadded
      ((word m9 256 ^^^ sprNet (65280 &&& word cd 5259 /
        6901746346790563787434755862277025452451108972170386555162524223799296 |||
      word cd 5259 / 452312848583266388373324160190187140051835877600158453279131187530910662656) *
        2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)
    {x : Nat} (hx : x < 25) :
    word m10 (32 * x) = if x < 17 then
        word m (32 * x) ^^^ spread (le64 (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) (8 * x)) * 2 ^ sh
      else word m (32 * x) := by
  have hFIX : sprNet (65280 &&& word cd 5259 /
        6901746346790563787434755862277025452451108972170386555162524223799296 |||
      word cd 5259 / 452312848583266388373324160190187140051835877600158453279131187530910662656) =
      spread (byteAt cd 5259 + 256 * byteAt cd 5260) := by
    rw [mu0_fix_eq, sprNet_eq (mu0_fix_lt cd)]
  have hw10 : ∀ y, word m10 (32 * y) = if y = 8 then
      (word m9 256 ^^^ spread (byteAt cd 5259 + 256 * byteAt cd 5260) * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      else word m9 (32 * y) := by
    intro y; rw [h10, word_wb32 _ (by omega) (by norm_num) (modL_lt _), hFIX]
    by_cases hy : y = 8
    · rw [if_pos (by omega), if_pos hy]
    · rw [if_neg (by omega), if_neg hy]
  have hS0 : spread 0 * 2 ^ sh = 0 := by rw [spread_zero', Nat.zero_mul]
  have h9' : ∀ y, 8 ≤ y → y ≤ 16 → word m9 (32 * y) = word m (32 * y) ^^^ spread (muCd cd y) * 2 ^ sh := by
    intro y h1 h2
    rw [h9 y (by omega), if_pos ⟨h1, by omega⟩, h8, if_neg (by omega), mu0_trLane cd h1 (by omega),
      if_pos h2]
  rw [hw10]
  by_cases hx17 : x < 17
  · rw [if_pos hx17, le64_mu0U htr hcd hx17, S_xor, S_xor]
    by_cases hx8 : x < 8
    · rw [if_neg (show ¬ x = 8 by omega), h9 x hx, if_neg (show ¬ (8 ≤ x ∧ x < 20) by omega), h8,
        if_pos hx8, hTRL x hx8, sprNet_eq (le64_lt' _ _),
        muTr, if_pos hx8, muCd, if_neg (show ¬ 8 ≤ x by omega), muFix, if_neg (show ¬ x = 8 by omega)]
      mu_fin'
    · rw [muTr, if_neg hx8, muFix]
      by_cases h8' : x = 8
      · subst h8'
        simp only [eq_self_iff_true, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
        rw [show (256 : Nat) = 32 * 8 from rfl, h9' 8 (by omega) (by omega)]
        mu_fin'
      · rw [if_neg h8', if_neg h8', h9' x (by omega) (by omega)]
        mu_fin'
  · rw [if_neg hx17, if_neg (show ¬ x = 8 by omega), h9 x hx]
    by_cases h20 : x < 20
    · rw [if_pos ⟨by omega, h20⟩, h8, if_neg (show ¬ x < 8 by omega), mu0_trLane cd (by omega) h20,
        if_neg (show ¬ x ≤ 16 by omega), hS0, Nat.xor_zero]
    · rw [if_neg (show ¬ (8 ≤ x ∧ x < 20) by omega), h8, if_neg (show ¬ x < 8 by omega)]

end MlDsaOpt65.Proofs.WP4
