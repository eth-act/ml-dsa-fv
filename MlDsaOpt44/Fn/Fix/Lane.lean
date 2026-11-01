import MlDsaOpt44.Layout
set_option warningAsError true
/-!
# `fix`: lane algebra of the masked lane writes
-/

namespace MlDsaOpt44.Proofs.Fix

open MlDsaOptCommon

theorem testBit_lane (x k i : Nat) :
    (lane x k).testBit i = (decide (i < 64) && x.testBit (64 * k + i)) := by
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]

theorem testBit_ge {x n j : Nat} (hx : x < 2 ^ n) (hj : n ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))

theorem lane_lt (x k : Nat) : lane x k < 2 ^ 64 := Nat.mod_lt _ (by positivity)

/-- Words are determined by their four lanes. -/
theorem eq_of_lanes {x y : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256)
    (h : ∀ k, k < 4 → lane x k = lane y k) : x = y := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 256
  · have := congrArg (fun z => z.testBit (j % 64)) (h (j / 64) (by omega))
    simp only [testBit_lane] at this
    rwa [show 64 * (j / 64) + j % 64 = j by omega, show decide (j % 64 < 64) = true by
      simp [Nat.mod_lt], Bool.true_and, Bool.true_and] at this
  · rw [testBit_ge hx (by omega), testBit_ge hy (by omega)]

/-- The complement of lane mask `sl`. -/
def nmask (sl : Nat) : Nat := 2 ^ 256 - 1 - 18446744073709551615 * 2 ^ (64 * sl)

/-- Lane mask `sl`. -/
def lmask (sl : Nat) : Nat := 18446744073709551615 * 2 ^ (64 * sl)

theorem nmask_bit {sl : Nat} (hsl : sl < 4) (j : Nat) :
    (nmask sl).testBit j = decide (j < 256 ∧ (j < 64 * sl ∨ 64 * sl + 64 ≤ j)) := by
  by_cases hj : j < 256
  · have h : ∀ sl, sl < 4 → ∀ j, j < 256 → (nmask sl).testBit j =
        decide (j < 256 ∧ (j < 64 * sl ∨ 64 * sl + 64 ≤ j)) := by
      unfold nmask; decide +kernel
    exact h sl hsl j hj
  · rw [testBit_ge (n := 256) (by unfold nmask; omega) (by omega)]; simp [hj]

theorem lmask_bit (sl j : Nat) :
    (lmask sl).testBit j = decide (64 * sl ≤ j ∧ j < 64 * sl + 64) := by
  unfold lmask
  rw [Nat.testBit_mul_two_pow, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 64 * sl ≤ j
  · simp [h]; omega
  · simp [h]

theorem lmask_lt {sl : Nat} (hsl : sl < 4) : lmask sl < 2 ^ 256 := by
  unfold lmask
  have : 2 ^ (64 * sl) ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by omega)
  calc 18446744073709551615 * 2 ^ (64 * sl) ≤ 18446744073709551615 * 2 ^ 192 :=
        Nat.mul_le_mul_left _ this
    _ < _ := by decide

/-- Flagged-path write: lane `sl` replaced by `y`. -/
theorem lane_fw {x y sl k : Nat} (hy : y < 2 ^ 64) (hsl : sl < 4)
    (hk : k < 4) :
    lane ((nmask sl &&& x ||| y * 2 ^ (64 * sl)) % 2 ^ 256) k = if k = sl then y else lane x k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_lane]
  by_cases hi : i < 64
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_and, nmask_bit hsl,
      Nat.testBit_mul_two_pow]
    by_cases hks : k = sl
    · subst hks
      simp [hi, show 64 * k + i < 256 by omega, show 64 * k ≤ 64 * k + i by omega,
        show 64 * k + i - 64 * k = i by omega]
    · rw [if_neg hks, testBit_lane]
      by_cases hlt : k < sl
      · simp [hi, show 64 * k + i < 256 by omega, show 64 * k + i < 64 * sl by omega,
          show ¬ 64 * sl ≤ 64 * k + i by omega]
      · have h1 : 64 * sl + 64 ≤ 64 * k + i := by omega
        rw [testBit_ge (x := y) (n := 64) hy (by omega)]
        simp [hi, show 64 * k + i < 256 by omega, h1]
  · simp only [hi, decide_false, Bool.false_and]
    split
    · exact (testBit_ge hy (by omega)).symm
    · rw [testBit_lane]; simp [hi]

/-- Clean-path masked copy: lane `sl` of `r`, the other lanes of `x`. -/
theorem lane_cw {x r sl k : Nat} (hsl : sl < 4) (hk : k < 4) :
    lane ((lmask sl &&& r ||| nmask sl &&& x) % 2 ^ 256) k =
      if k = sl then lane r sl else lane x k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_lane]
  by_cases hi : i < 64
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, nmask_bit hsl,
      lmask_bit]
    by_cases hks : k = sl
    · subst hks
      simp [hi, testBit_lane, show 64 * k + i < 256 by omega]
    · rw [if_neg hks, testBit_lane]
      by_cases hlt : k < sl
      · simp [hi, show 64 * k + i < 256 by omega, show 64 * k + i < 64 * sl by omega,
          show ¬ 64 * sl ≤ 64 * k + i by omega]
      · simp [hi, show 64 * k + i < 256 by omega, show 64 * sl + 64 ≤ 64 * k + i by omega,
          show ¬ 64 * k + i < 64 * sl + 64 by omega]
  · simp only [hi, decide_false, Bool.false_and]
    split <;> rw [testBit_lane] <;> simp [hi]

end MlDsaOpt44.Proofs.Fix
