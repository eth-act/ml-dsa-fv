import MlDsaOpt44.Layout
/-!
# Lane calculus for row-packed words (WP10 helpers)

`pack4 v` with lanes `v r < 2^64`: bits, lane-wise `AND`, lane-wise
shift-and-mask, and the `Nat`/`UInt256` arithmetic that stays inside lanes.
-/

namespace MlDsaOpt44.Proofs.L10

open EvmSemantics
open MlDsaOptCommon
open MlDsaOpt44.Proofs

/-- Lanes below `2^64`. -/
def Lanes (v : Nat → Nat) : Prop := ∀ r, r < 4 → v r < 2 ^ 64

theorem pk_lt {v : Nat → Nat} (h : Lanes v) : pack4 v < 2 ^ 256 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem pk_lane {v : Nat → Nat} (h : Lanes v) {k : Nat} (hk : k < 4) : lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem testBit_pk {v : Nat → Nat} (h : Lanes v) (i : Nat) :
    (pack4 v).testBit i = (decide (i < 256) && (v (i / 64)).testBit (i % 64)) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have e : pack4 v = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1) + v 0 := by unfold pack4; ring
  rw [e, Nat.testBit_two_pow_mul_add _ h0]
  by_cases i0 : i < 64
  · rw [if_pos i0, show i / 64 = 0 by omega, show i % 64 = i by omega]; simp [show i < 256 by omega]
  rw [if_neg i0, Nat.testBit_two_pow_mul_add _ h1]
  by_cases i1 : i - 64 < 64
  · rw [if_pos i1, show i / 64 = 1 by omega, show i % 64 = i - 64 by omega]
    simp [show i < 256 by omega]
  rw [if_neg i1, Nat.testBit_two_pow_mul_add _ h2]
  by_cases i2 : i - 64 - 64 < 64
  · rw [if_pos i2, show i / 64 = 2 by omega, show i % 64 = i - 64 - 64 by omega]
    simp [show i < 256 by omega]
  rw [if_neg i2]
  by_cases i3 : i < 256
  · rw [show i / 64 = 3 by omega, show i % 64 = i - 64 - 64 - 64 by omega]; simp [i3]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [i3]

theorem lanes_of {v : Nat → Nat} (h : ∀ r, r < 4 → v r < 2 ^ 64) : Lanes v := h

theorem pk_and {a b : Nat → Nat} (ha : Lanes a) (hb : Lanes b) :
    pack4 a &&& pack4 b = pack4 fun r => a r &&& b r := by
  have hab : Lanes fun r => a r &&& b r := fun r hr =>
    Nat.lt_of_le_of_lt Nat.and_le_left (ha r hr)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_pk ha, testBit_pk hb, testBit_pk hab, Nat.testBit_and]
  cases decide (i < 256) <;> simp

/-- Lane-wise shift right by `k` and keep `j` bits (`k + j ≤ 64`). -/
theorem pk_shr_and {v : Nat → Nat} (hv : Lanes v) {k j : Nat} (hkj : k + j ≤ 64) :
    (pack4 v >>> k) &&& pack4 (fun _ => 2 ^ j - 1) = pack4 fun r => v r / 2 ^ k % 2 ^ j := by
  have hm : Lanes fun _ => 2 ^ j - 1 := fun r _ => by
    show 2 ^ j - 1 < 2 ^ 64
    have : 2 ^ j ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hr : Lanes fun r => v r / 2 ^ k % 2 ^ j := fun r _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pk hv, testBit_pk hm, testBit_pk hr,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 256
  · by_cases hb : i % 64 < j
    · rw [show (k + i) / 64 = i / 64 by omega, show (k + i) % 64 = i % 64 + k by omega]
      simp [hi, hb, show k + i < 256 by omega]
    · simp [hb]
  · simp [hi]

theorem pk_add (a b : Nat → Nat) : pack4 a + pack4 b = pack4 fun r => a r + b r := by
  unfold pack4; ring

theorem pk_mul (c : Nat) (a : Nat → Nat) : c * pack4 a = pack4 fun r => c * a r := by
  unfold pack4; ring

theorem pk_sub {a b : Nat → Nat} (h : ∀ r, r < 4 → b r ≤ a r) :
    pack4 a - pack4 b = pack4 fun r => a r - b r := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; beta_reduce; omega

theorem pk_le {a b : Nat → Nat} (h : ∀ r, r < 4 → b r ≤ a r) : pack4 b ≤ pack4 a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem pk_shl (a : Nat → Nat) (k : Nat) : pack4 a <<< k = pack4 fun r => 2 ^ k * a r := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, pk_mul]

/-! ## `UInt256` forms -/

theorem u_shr_and {v : Nat → Nat} (hv : Lanes v) {k j M : Nat} (hk : k < 256) (hkj : k + j ≤ 64)
    (hM : M = pack4 fun _ => 2 ^ j - 1) :
    (UInt256.ofNat M).land ((UInt256.ofNat (pack4 v)).shiftRight (UInt256.ofNat k)) =
      UInt256.ofNat (pack4 fun r => v r / 2 ^ k % 2 ^ j) := by
  rw [ofNat_shr _ hk, Nat.mod_eq_of_lt (pk_lt hv), ofNat_land, Nat.and_comm, hM, pk_shr_and hv hkj]

theorem u_mul (c : Nat) (a : Nat → Nat) :
    UInt256.ofNat c * UInt256.ofNat (pack4 a) = UInt256.ofNat (pack4 fun r => c * a r) := by
  rw [ofNat_mul, pk_mul]

theorem u_sub {a b : Nat → Nat} (ha : Lanes a) (h : ∀ r, r < 4 → b r ≤ a r) :
    UInt256.ofNat (pack4 a) - UInt256.ofNat (pack4 b) = UInt256.ofNat (pack4 fun r => a r - b r) := by
  rw [ofNat_sub (pk_le h) (pk_lt ha), pk_sub h]

theorem u_add (a b : Nat → Nat) :
    UInt256.ofNat (pack4 a) + UInt256.ofNat (pack4 b) = UInt256.ofNat (pack4 fun r => a r + b r) := by
  rw [EvmProof.Word.ofNat_add_mod, pk_add]

theorem u_and {a b : Nat → Nat} (ha : Lanes a) (hb : Lanes b) :
    (UInt256.ofNat (pack4 a)).land (UInt256.ofNat (pack4 b)) =
      UInt256.ofNat (pack4 fun r => a r &&& b r) := by
  rw [ofNat_land, pk_and ha hb]

theorem u_shl (a : Nat → Nat) {k : Nat} (hk : k < 256) :
    (UInt256.ofNat (pack4 a)).shiftLeft (UInt256.ofNat k) =
      UInt256.ofNat (pack4 fun r => 2 ^ k * a r) := by
  rw [ofNat_shl _ hk, pk_shl]

/-- A replicated constant. -/
theorem pk_const (c : Nat) : pack4 (fun _ => c) = c * REP := by
  unfold REP pack4; ring

/-- Every word is the `pack4` of its lanes. -/
theorem pk_lanes {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun r => lane x r) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  omega

theorem lanes_lane (x : Nat) : Lanes fun r => lane x r := fun r _ => Nat.mod_lt _ (by positivity)

end MlDsaOpt44.Proofs.L10
