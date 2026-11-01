import MlDsaOpt87.Fn.Decode.ZMath
set_option warningAsError true
/-!
# `z` as `sigDecode` reads it (ML-DSA-87, WP G2)

Parametric twin of `MlDsa44/Proofs/Math/Decode/Z.lean`: coefficient `j` of `z[i]`
(`i < ℓ = 7`) is `γ1 − rawZ cd i j` (20-bit fields at `Z0 + 640 i = CTOFF + 64 + 640 i`),
and `‖z‖∞ < γ1 − β` is `β < rawZ < 2γ1 − β` for every coefficient (`okZ_iff`).
-/

namespace MlDsaOpt87.Proofs.DecodeZ

open MlDsa

theorem bitlen_z : Fips204.bitlen (P.gamma1 - 1) = 19 := by decide +kernel

theorem bitlen_zc : Fips204.bitlen (P.gamma1 - 1 + P.gamma1) = 20 := by decide +kernel

theorem extract_get {cd : ByteArray} {a b k : Nat} (hb : b ≤ cd.size) (hk : a + k < b) :
    (cd.extract a b)[k]! = cd[a + k]! := by
  have hs : k < (cd.extract a b).size := by rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (cd.extract a b) k hs, ByteArray.getElem_extract,
    getElem!_pos cd (a + k) (by omega)]

theorem bitsToInteger_congr {v w : ByteArray} {N : Nat} (h : ∀ k, k < N → v[k]! = w[k]!)
    {p c : Nat} (hp : p + c ≤ 8 * N) : Fips204.bitsToInteger v p c = Fips204.bitsToInteger w p c := by
  unfold Fips204.bitsToInteger
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  unfold Fips204.bit
  rw [h _ (by omega)]

theorem sigDecode_z_size (cd : ByteArray) : (zPolys cd).size = 7 := by
  simp [zPolys, Fips204.sigDecode, P, Params.mldsa87]

theorem sigDecode_z_get (cd : ByteArray) {i : Nat} (hi : i < 7) :
    (zPolys cd)[i]! =
      Fips204.bitUnpack ((sigOf cd).extract (64 + 640 * i) (64 + 640 * (i + 1)))
        (P.gamma1 - 1) P.gamma1 := by
  rw [getElem!_pos _ i (by rw [sigDecode_z_size]; exact hi)]
  simp only [zPolys, Fips204.sigDecode, Array.getElem_map, Array.getElem_range, bitlen_z,
    show P.lambda / 4 = 64 from rfl]

theorem bitUnpack_size (v : ByteArray) (a b : Nat) : (Fips204.bitUnpack v a b).size = 256 := by
  simp [Fips204.bitUnpack]

set_option maxRecDepth 100000 in
/-- Coefficient `j` of `z[i]`. -/
theorem sigDecode_z_coeff {cd : ByteArray} (hcd : HDR ≤ cd.size) {i j : Nat} (hi : i < 7)
    (hj : j < 256) : (zPolys cd)[i]![j]! = (524288 : Int) - rawZ cd i j := by
  rw [sigDecode_z_get cd hi, getElem!_pos _ j (by rw [bitUnpack_size]; exact hj)]
  unfold Fips204.bitUnpack
  dsimp only
  rw [Array.getElem_map, Array.getElem_range, bitlen_zc]
  have hg : ((P.gamma1 : Nat) : Int) = 524288 := by decide
  have hr : Fips204.bitsToInteger ((sigOf cd).extract (64 + 640 * i) (64 + 640 * (i + 1)))
      (j * 20) 20 = rawZ cd i j := by
    unfold rawZ
    rw [Nat.mul_comm j 20]
    apply bitsToInteger_congr (N := 640) _ (by omega)
    intro k hk
    have hs : (sigOf cd).size = 4627 := by
      simp only [sigOf, ByteArray.size_extract, HDR, CTOFF] at hcd ⊢; omega
    have hsg : ∀ k, k < 4627 → (sigOf cd)[k]! = cd[2592 + k]! := by
      intro k hk
      have hb : CTOFF + 4627 ≤ cd.size := by simp only [HDR, CTOFF] at hcd ⊢; omega
      have e := extract_get (cd := cd) (a := CTOFF) (b := CTOFF + 4627) (k := k) hb (by omega)
      unfold sigOf
      rw [show HDR = CTOFF + 4627 from rfl, show 2592 + k = CTOFF + k from rfl]
      exact e
    have hz : (cd.extract (Z0 + 640 * i) (Z0 + 640 * (i + 1)))[k]! = cd[2656 + 640 * i + k]! :=
      extract_get (by simp only [HDR, Z0] at hcd ⊢; omega) (by simp only [Z0]; omega)
    rw [hz, show 2656 + 640 * i + k = 2592 + (64 + 640 * i + k) by omega]
    clear hz hg
    generalize sigOf cd = sig at hs hsg
    have e1 : 64 + 640 * (i + 1) ≤ sig.size := by omega
    have e2 : 64 + 640 * i + k < 64 + 640 * (i + 1) := by omega
    have e3 : 64 + 640 * i + k < 4627 := by omega
    rw [extract_get e1 e2, hsg _ e3]
  rw [hg, hr]

theorem natAbs_iff {r : Nat} (hr : r < 2 ^ 20) :
    ((524288 : Int) - r).natAbs < 524168 ↔ 120 < r ∧ r < 1048456 := by omega

/-- `okZ` is the conjunction of the field checks of the first `ℓ = 7` polynomials. -/
theorem okZ_iff {cd : ByteArray} (hcd : HDR ≤ cd.size) :
    okZ cd = true ↔ ∀ k, k < 7 → ∀ t, t < 256 → 120 < rawZ cd k t ∧ rawZ cd k t < 1048456 := by
  have hb : P.gamma1 - P.beta = 524168 := by decide
  unfold okZ Fips204.normBelow
  rw [hb]
  simp only [Array.all_eq_true]
  constructor
  · intro h i hi j hj
    have h1 : i < (zPolys cd).size := by rw [sigDecode_z_size]; exact hi
    have h2 : j < (zPolys cd)[i].size := by
      have := sigDecode_z_get cd hi
      rw [getElem!_pos _ i h1] at this
      rw [this, bitUnpack_size]; exact hj
    have h3 := h i h1 j h2
    have hc := sigDecode_z_coeff hcd hi hj
    rw [getElem!_pos _ i h1, getElem!_pos _ j h2] at hc
    rw [hc] at h3
    simpa [natAbs_iff (rawZ_lt cd i j)] using h3
  · intro h i h1 j h2
    have hi : i < 7 := by rwa [sigDecode_z_size] at h1
    have hj : j < 256 := by
      have := sigDecode_z_get cd hi
      rw [getElem!_pos _ i h1] at this
      rw [this, bitUnpack_size] at h2; exact h2
    have hc := sigDecode_z_coeff hcd hi hj
    rw [getElem!_pos _ i h1, getElem!_pos _ j h2] at hc
    rw [hc]
    simpa using (natAbs_iff (rawZ_lt cd i j)).2 (h i hi j hj)

theorem okZ_iff_zNormOk (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    okZ cd = true ↔ ∀ k, k < P.l → zNormOk cd k := by
  rw [okZ_iff hcd]
  unfold zNormOk
  rw [show P.l = 7 by decide, show 2 * P.gamma1 - P.beta = 1048456 by decide, show P.beta = 120 by decide]

end MlDsaOpt87.Proofs.DecodeZ
