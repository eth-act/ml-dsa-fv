import MlDsaOpt44.Layout
/-!
# `pack` (WP10): bits of `le64 (SimpleBitPack w 43)`

Bit `b < 64` of stream lane `x < 24` is bit `(64x + b) mod 6` of coefficient
`(64x + b) / 6`.
-/

namespace MlDsaOpt44.Proofs.PK

open MlDsaOptCommon
open MlDsa44

/-- Bits of a digit sum `Σ_{i<n} d i · 2^{k i}` with digits below `2^k`. -/
theorem digits_testBit (k : Nat) (hk : 0 < k) (d : Nat → Nat) :
    ∀ n, (∀ i, i < n → d i < 2 ^ k) →
      ((List.range n).map fun i => d i * 2 ^ (k * i)).sum < 2 ^ (k * n) ∧
      ∀ b, ((List.range n).map fun i => d i * 2 ^ (k * i)).sum.testBit b =
        (decide (b < k * n) && (d (b / k)).testBit (b % k))
  | 0, _ => by simp
  | n + 1, h => by
    obtain ⟨ih1, ih2⟩ := digits_testBit k hk d n (fun i hi => h i (by omega))
    have hdn := h n (by omega)
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hpow : 2 ^ (k * (n + 1)) = 2 ^ (k * n) * 2 ^ k := by rw [Nat.mul_succ, Nat.pow_add]
    refine ⟨?_, fun b => ?_⟩
    · rw [hpow]
      have : d n * 2 ^ (k * n) ≤ (2 ^ k - 1) * 2 ^ (k * n) := Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 ^ k - 1) * 2 ^ (k * n) = 2 ^ (k * n) * 2 ^ k - 2 ^ (k * n) := by
        rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
      have : 2 ^ (k * n) ≤ 2 ^ (k * n) * 2 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    · rw [Nat.add_comm, Nat.mul_comm (d n), Nat.testBit_two_pow_mul_add _ ih1]
      by_cases hb : b < k * n
      · rw [if_pos hb, ih2, decide_eq_true hb, decide_eq_true (by rw [Nat.mul_succ]; omega)]
      · rw [if_neg hb]
        by_cases hb2 : b < k * (n + 1)
        · have hq : b / k = n := by
            apply Nat.div_eq_of_lt_le
            · rw [Nat.mul_comm]; omega
            · rw [Nat.mul_comm]; exact hb2
          have hr : b % k = b - k * n := by rw [Nat.mod_def, hq]
          rw [decide_eq_true hb2, hq, hr, Bool.true_and]
        · rw [decide_eq_false hb2, Bool.false_and]
          apply Nat.testBit_lt_two_pow
          exact Nat.lt_of_lt_of_le hdn (Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_succ] at hb2; omega))

theorem bits_testBit (z : Nat → Nat) (n b : Nat) :
    ((List.range n).map fun i => z i % 2 * 2 ^ i).sum.testBit b = (decide (b < n) && decide (z b % 2 = 1)) := by
  have := (digits_testBit 1 (by omega) (fun i => z i % 2) n (fun i _ => by simp only [Nat.pow_one]; exact Nat.mod_lt _ (by omega))).2 b
  simp only [Nat.one_mul, Nat.div_one, Nat.mod_one, Nat.testBit_zero, Nat.mod_mod] at this
  exact this

theorem bits_lt (z : Nat → Nat) (n : Nat) :
    ((List.range n).map fun i => z i % 2 * 2 ^ i).sum < 2 ^ n := by
  have := (digits_testBit 1 (by omega) (fun i => z i % 2) n (fun i _ => by simp only [Nat.pow_one]; exact Nat.mod_lt _ (by omega))).1
  simpa using this

theorem bitlen_43 : Fips204.bitlen 43 = 6 := by
  decide

/-- Byte `n < 192` of `SimpleBitPack w 43`. -/
theorem byteAt_sbp (w : Fips204.Poly) {n : Nat} (hn : n < 192) :
    byteAt (Fips204.simpleBitPack w 43) n =
      ((List.range 8).map fun t => w[(8 * n + t) / 6]!.toNat / 2 ^ ((8 * n + t) % 6) % 2 * 2 ^ t).sum := by
  have hs : (Fips204.simpleBitPack w 43).size = 192 := by
    simp [Fips204.simpleBitPack, bitlen_43, ByteArray.size]
  unfold byteAt
  rw [dif_pos (by omega)]
  have hlt : ((List.range 8).map fun t => w[(8 * n + t) / 6]!.toNat / 2 ^ ((8 * n + t) % 6) % 2 * 2 ^ t).sum
      < 256 := by
    exact bits_lt (fun t => w[(8 * n + t) / 6]!.toNat / 2 ^ ((8 * n + t) % 6)) 8
  simp only [Fips204.simpleBitPack, bitlen_43]
  simp [ByteArray.getElem_eq_data_getElem, Array.getElem_map, Array.getElem_range, 
    Nat.mod_eq_of_lt hlt]

theorem le64_eq (B : ByteArray) (a : Nat) :
    le64 B a = ((List.range 8).map fun i => byteAt B (a + i) * 2 ^ (8 * i)).sum := by
  have e : ∀ i, (256 : Nat) ^ i = 2 ^ (8 * i) := fun i => by rw [Nat.pow_mul]
  simp only [le64, e]

theorem le64_sbp_testBit (w : Fips204.Poly) {x : Nat} (hx : x < 24) (b : Nat) :
    (le64 (Fips204.simpleBitPack w 43) (8 * x)).testBit b =
      (decide (b < 64) && (w[(64 * x + b) / 6]!.toNat).testBit ((64 * x + b) % 6)) := by
  rw [le64_eq, (digits_testBit 8 (by omega) _ 8 (fun i _ => byteAt_lt _ _)).2 b]
  by_cases hb : b < 64
  · simp only [show b < 8 * 8 by omega, decide_true, Bool.true_and]
    rw [byteAt_sbp w (by omega)]
    rw [bits_testBit (fun t => w[(8 * (8 * x + b / 8) + t) / 6]!.toNat / 2 ^ ((8 * (8 * x + b / 8) + t) % 6))]
    have e : 8 * (8 * x + b / 8) + b % 8 = 64 * x + b := by omega
    rw [decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, Nat.testBit_eq_decide_div_mod_eq, e]
  · simp only [show ¬ b < 8 * 8 by omega, decide_false, Bool.false_and]

/-- `le64` of the packed stream is below `2^64`. -/
theorem le64_lt (B : ByteArray) (a : Nat) : le64 B a < 2 ^ 64 := by
  have h := (digits_testBit 8 (by omega) (fun i => byteAt B (a + i)) 8 (fun i _ => byteAt_lt _ _)).1
  rw [le64_eq]; simpa using h

end MlDsaOpt44.Proofs.PK
