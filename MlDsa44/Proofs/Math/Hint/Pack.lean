import MlDsa44.Spec.Fips204
set_option warningAsError true
/-!
# `SimpleBitPack(w, 43)` as three-byte groups

With `bitlen 43 = 6`, four 6-bit coefficients fill three bytes. `groupAcc A g e`
is the Yul accumulator `v` of `encodeRow` after `e` inner iterations of group
`g` (`v |= A(4g + e) << 6e`); byte `j` of the packing is byte `j mod 3` of
`groupAcc A (j / 3) 4`.
-/

namespace MlDsa44.Proofs.Hint

theorem lor_mul_two_pow {a k : Nat} (b : Nat) (ha : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq,
    Nat.add_comm]

/-- The `encodeRow` accumulator of group `g` after `e` coefficients. -/
def groupAcc (A : Nat → Nat) (g e : Nat) : Nat :=
  (List.range e).foldl (fun a k => a ||| A (g * 4 + k) * 2 ^ (6 * k)) 0

theorem groupAcc_zero (A : Nat → Nat) (g : Nat) : groupAcc A g 0 = 0 := rfl

theorem groupAcc_succ (A : Nat → Nat) (g e : Nat) :
    groupAcc A g (e + 1) = groupAcc A g e ||| A (g * 4 + e) * 2 ^ (6 * e) := by
  simp only [groupAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem groupAcc_four (A : Nat → Nat) (g : Nat) (hA : ∀ e, e < 4 → A (g * 4 + e) < 64) :
    groupAcc A g 4 =
      A (g * 4) + A (g * 4 + 1) * 64 + A (g * 4 + 2) * 4096 + A (g * 4 + 3) * 262144 := by
  have h0 := hA 0 (by decide)
  have h1 := hA 1 (by decide)
  have h2 := hA 2 (by decide)
  have b1 : A (g * 4 + 0) * 2 ^ (6 * 0) < 2 ^ (6 * 1) := by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]; omega
  have b2 : A (g * 4 + 0) * 2 ^ (6 * 0) + A (g * 4 + 1) * 2 ^ (6 * 1) < 2 ^ (6 * 2) := by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow]; omega
  have b3 : A (g * 4 + 0) * 2 ^ (6 * 0) + A (g * 4 + 1) * 2 ^ (6 * 1) +
      A (g * 4 + 2) * 2 ^ (6 * 2) < 2 ^ (6 * 3) := by
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow]; omega
  rw [groupAcc_succ, groupAcc_succ, groupAcc_succ, groupAcc_succ, groupAcc_zero, Nat.zero_or,
    lor_mul_two_pow _ b1, lor_mul_two_pow _ b2, lor_mul_two_pow _ b3]
  simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow]

theorem bitlen_43 : Fips204.bitlen 43 = 6 := by decide

theorem simpleBitPack43_size (w : Fips204.Poly) : (Fips204.simpleBitPack w 43).size = 192 := by
  simp [Fips204.simpleBitPack, bitlen_43, ByteArray.size]

theorem simpleBitPack43_get (w : Fips204.Poly) (A : Nat → Nat)
    (hw : ∀ n, n < 256 → w[n]!.toNat = A n) (hA : ∀ n, n < 256 → A n < 64)
    (j : Nat) (hj : j < 192) :
    (Fips204.simpleBitPack w 43)[j]!.toNat = groupAcc A (j / 3) 4 / 256 ^ (j % 3) % 256 := by
  rw [getElem!_pos (Fips204.simpleBitPack w 43) j (by rw [simpleBitPack43_size]; exact hj)]
  simp only [Fips204.simpleBitPack, bitlen_43]
  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_map, Array.getElem_range,
    UInt8.toNat_ofNat']
  obtain ⟨g, k, hk, rfl⟩ : ∃ g k, k < 3 ∧ j = 3 * g + k := ⟨j / 3, j % 3, by omega, by omega⟩
  have hg : g < 64 := by omega
  have hterm : ∀ t ∈ List.range 8,
      w[(8 * (3 * g + k) + t) / 6]!.toNat / 2 ^ ((8 * (3 * g + k) + t) % 6) % 2 * 2 ^ t =
        A (g * 4 + (8 * k + t) / 6) / 2 ^ ((8 * k + t) % 6) % 2 * 2 ^ t := by
    intro t ht
    have ht8 : t < 8 := List.mem_range.mp ht
    rw [show (8 * (3 * g + k) + t) / 6 = g * 4 + (8 * k + t) / 6 by omega,
      show (8 * (3 * g + k) + t) % 6 = (8 * k + t) % 6 by omega, hw _ (by omega)]
  rw [List.map_congr_left hterm, show (3 * g + k) / 3 = g by omega,
    show (3 * g + k) % 3 = k by omega, groupAcc_four A g (fun e he => hA _ (by omega))]
  have h0 := hA (g * 4) (by omega)
  have h1 := hA (g * 4 + 1) (by omega)
  have h2 := hA (g * 4 + 2) (by omega)
  have h3 := hA (g * 4 + 3) (by omega)
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceMul, Nat.reduceAdd,
      Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.add_zero]
    omega

end MlDsa44.Proofs.Hint
