import MlDsa44.Spec
set_option warningAsError true
/-!
# `z` as `sigDecode` reads it

Coefficient `j` of `z[i]` is `γ₁ − rawZ cd i j`, where `rawZ` is the 18-bit
field read by `unpack(1344 + 576 i, j, 18)` from the calldata, and the norm
check `‖z‖∞ < γ₁ − β` is `78 < rawZ < 262066` for every coefficient.
-/

namespace MlDsa44.Proofs.Decode

open MlDsa44.Fips204

/-- The 18-bit field `j` of polynomial `i` of `z` in the calldata. -/
def rawZ (cd : ByteArray) (i j : Nat) : Nat :=
  bitsToInteger (cd.extract (1344 + 576 * i) (1344 + 576 * i + 576)) (j * 18) 18

/-- The bytecode's per-coefficient norm check. -/
def okZ (cd : ByteArray) (i j : Nat) : Bool := decide (78 < rawZ cd i j ∧ rawZ cd i j < 262066)

/-- All checks of the first `n` polynomials. -/
def zAll (cd : ByteArray) (n : Nat) : Bool :=
  (List.range n).all fun i => (List.range 256).all (okZ cd i)

theorem bit_lt (v : ByteArray) (p : Nat) : bit v p < 2 := by
  unfold bit; exact Nat.mod_lt _ (by decide)

theorem bitsToInteger_lt (v : ByteArray) (p : Nat) : ∀ c, bitsToInteger v p c < 2 ^ c
  | 0 => by simp [bitsToInteger]
  | c + 1 => by
    have ih := bitsToInteger_lt v p c
    have hb := bit_lt v (p + c)
    have : bitsToInteger v p (c + 1) = bitsToInteger v p c + bit v (p + c) * 2 ^ c := by
      simp [bitsToInteger, List.range_succ, List.map_append, List.sum_append]
    rw [this, Nat.pow_succ]
    have : bit v (p + c) * 2 ^ c ≤ 1 * 2 ^ c := Nat.mul_le_mul_right _ (by omega)
    omega

theorem rawZ_lt (cd : ByteArray) (i j : Nat) : rawZ cd i j < 262144 :=
  bitsToInteger_lt _ _ 18

theorem bitsToInteger_congr {v w : ByteArray} {N : Nat} (h : ∀ k, k < N → v[k]! = w[k]!)
    {p c : Nat} (hp : p + c ≤ 8 * N) : bitsToInteger v p c = bitsToInteger w p c := by
  unfold bitsToInteger
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  unfold bit
  rw [h _ (by omega)]

theorem extract_get {cd : ByteArray} {a b k : Nat} (hb : b ≤ cd.size) (hk : a + k < b) :
    (cd.extract a b)[k]! = cd[a + k]! := by
  have hs : k < (cd.extract a b).size := by rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (cd.extract a b) k hs, ByteArray.getElem_extract,
    getElem!_pos cd (a + k) (by omega)]

theorem bitlen_z : bitlen (gamma1 - 1) = 17 := by decide +kernel

theorem bitlen_zc : bitlen (gamma1 - 1 + gamma1) = 18 := by decide +kernel

theorem sigDecode_z_size (cd : ByteArray) : (sigDecode (cd.extract 1312 3732)).2.1.size = 4 := by
  simp [sigDecode, l]

/-- Polynomial `i` of `z`. -/
theorem sigDecode_z_get (cd : ByteArray) {i : Nat} (hi : i < 4) :
    (sigDecode (cd.extract 1312 3732)).2.1[i]! =
      bitUnpack ((cd.extract 1312 3732).extract (32 + 576 * i) (32 + 576 * (i + 1)))
        (gamma1 - 1) gamma1 := by
  rw [getElem!_pos _ i (by rw [sigDecode_z_size]; exact hi)]
  simp only [sigDecode, Array.getElem_map, Array.getElem_range, bitlen_z,
    show lambda / 4 = 32 from rfl]

theorem bitUnpack_size (v : ByteArray) (a b : Nat) : (bitUnpack v a b).size = 256 := by
  simp [bitUnpack]

set_option maxRecDepth 100000 in
/-- Coefficient `j` of `z[i]`. -/
theorem sigDecode_z_coeff {cd : ByteArray} (hcd : 3732 ≤ cd.size) {i j : Nat} (hi : i < 4)
    (hj : j < 256) :
    (sigDecode (cd.extract 1312 3732)).2.1[i]![j]! = (131072 : Int) - rawZ cd i j := by
  rw [sigDecode_z_get cd hi, getElem!_pos _ j (by rw [bitUnpack_size]; exact hj)]
  simp only [bitUnpack, Array.getElem_map, Array.getElem_range, bitlen_zc]
  have hg : ((gamma1 : Nat) : Int) = 131072 := by decide
  have hr : bitsToInteger ((cd.extract 1312 3732).extract (32 + 576 * i) (32 + 576 * (i + 1)))
      (j * 18) 18 = rawZ cd i j := by
    unfold rawZ
    apply bitsToInteger_congr (N := 576) _ (by omega)
    intro k hk
    have hs : (cd.extract 1312 3732).size = 2420 := by
      simp only [ByteArray.size_extract]; omega
    have hsg : ∀ k, k < 2420 → (cd.extract 1312 3732)[k]! = cd[1312 + k]! :=
      fun k hk => extract_get hcd (by omega)
    have hz : (cd.extract (1344 + 576 * i) (1344 + 576 * i + 576))[k]! = cd[1344 + 576 * i + k]! :=
      extract_get (by omega) (by omega)
    rw [hz, show 1344 + 576 * i + k = 1312 + (32 + 576 * i + k) by omega]
    clear hz hg
    generalize cd.extract 1312 3732 = sig at hs hsg
    have e1 : 32 + 576 * (i + 1) ≤ sig.size := by omega
    have e2 : 32 + 576 * i + k < 32 + 576 * (i + 1) := by omega
    have e3 : 32 + 576 * i + k < 2420 := by omega
    rw [extract_get e1 e2, hsg _ e3]
  rw [hg, hr]

theorem natAbs_iff {r : Nat} (hr : r < 262144) :
    ((131072 : Int) - r).natAbs < 130994 ↔ 78 < r ∧ r < 262066 := by omega

theorem sigDecode_z_coeff' {cd : ByteArray} (hcd : 3732 ≤ cd.size) {i j : Nat}
    (h1 : i < (sigDecode (cd.extract 1312 3732)).2.1.size)
    (h2 : j < (sigDecode (cd.extract 1312 3732)).2.1[i].size) :
    (sigDecode (cd.extract 1312 3732)).2.1[i][j] = (131072 : Int) - rawZ cd i j := by
  have hi : i < 4 := by rwa [sigDecode_z_size] at h1
  have hj : j < 256 := by
    have := sigDecode_z_get cd hi
    rw [getElem!_pos _ i h1] at this
    rw [this, bitUnpack_size] at h2; exact h2
  have := sigDecode_z_coeff hcd hi hj
  rwa [getElem!_pos _ i h1, getElem!_pos _ j h2] at this

theorem normBelow_eq {cd : ByteArray} (hcd : 3732 ≤ cd.size) :
    normBelow (sigDecode (cd.extract 1312 3732)).2.1 (gamma1 - beta) = zAll cd 4 := by
  have hb : gamma1 - beta = 130994 := by decide
  rw [hb, Bool.eq_iff_iff]
  unfold normBelow zAll
  simp only [Array.all_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi j hj
    have h1 : i < (sigDecode (cd.extract 1312 3732)).2.1.size := by rw [sigDecode_z_size]; exact hi
    have h2 : j < (sigDecode (cd.extract 1312 3732)).2.1[i].size := by
      have := sigDecode_z_get cd hi
      rw [getElem!_pos _ i h1] at this
      rw [this, bitUnpack_size]; exact hj
    have h3 := h i h1 j h2
    rw [sigDecode_z_coeff' hcd h1 h2] at h3
    simpa [okZ, natAbs_iff (rawZ_lt cd i j)] using h3
  · intro h i h1 j h2
    have hi : i < 4 := by rwa [sigDecode_z_size] at h1
    have hj : j < 256 := by
      have := sigDecode_z_get cd hi
      rw [getElem!_pos _ i h1] at this
      rw [this, bitUnpack_size] at h2; exact h2
    have h3 := h i hi j hj
    simp only [okZ, decide_eq_true_eq] at h3
    rw [sigDecode_z_coeff' hcd h1 h2]
    simpa using (natAbs_iff (rawZ_lt cd i j)).2 h3

end MlDsa44.Proofs.Decode
