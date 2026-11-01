import MlDsaOpt44.Math
import MlDsa.Spec.Fips204
set_option warningAsError true
/-!
# `UseHint` and `w1Encode` facts for `γ2 = (q − 1)/32` (WP G5; ML-DSA-65 and ML-DSA-87)

Stated for any parameter set with `γ2 = 261888`; `MlDsaOpt65/Math.lean` and
`MlDsaOpt87/Math.lean` instantiate them (`useHint_emod`, `useHint_range`,
`finBytes_le64_mu`, `finBytes_le64_w1`).
-/

namespace MlDsaOpt65.Proofs.G5

open MlDsa

theorem useHint_emod (Q : Params) (h r : Int) :
    Fips204.useHint Q h (r % (Fips204.q : Int)) = Fips204.useHint Q h r := by
  unfold Fips204.useHint Fips204.decompose
  simp only [Int.emod_emod]

theorem useHint_range (Q : Params) (hQ : Q.gamma2 = 261888) (h r : Int) :
    0 ≤ Fips204.useHint Q h r ∧ Fips204.useHint Q h r < 16 := by
  have hd : 0 ≤ (Fips204.decompose Q r).1 ∧ (Fips204.decompose Q r).1 < 16 := by
    unfold Fips204.decompose Fips204.modPm
    have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
    have hg : ((2 * Q.gamma2 : Nat) : Int) = 523776 := by rw [hQ]; rfl
    have hg2 : (((2 * Q.gamma2) / 2 : Nat) : Int) = 261888 := by rw [hQ]; rfl
    simp only [hq, hg, hg2]
    have h0 : 0 ≤ r % 8380417 := Int.emod_nonneg _ (by decide)
    have h1 : r % 8380417 < 8380417 := Int.emod_lt_of_pos _ (by decide)
    generalize r % 8380417 = x at h0 h1
    have h2 : 0 ≤ x % 523776 := Int.emod_nonneg _ (by decide)
    have h3 : x % 523776 < 523776 := Int.emod_lt_of_pos _ (by decide)
    have h4 : x % 523776 = x - 523776 * (x / 523776) := Int.emod_def _ _
    generalize x % 523776 = y at h2 h3 h4
    generalize x / 523776 = d at h4
    split_ifs
    · simp
    · simp only; omega
    · simp
    · simp only; omega
  unfold Fips204.useHint
  have hm : (((Fips204.q - 1) / (2 * Q.gamma2) : Nat) : Int) = 16 := by rw [hQ]; rfl
  simp only [hm]
  generalize Fips204.decompose Q r = p at hd
  obtain ⟨r1, r0⟩ := p
  simp only at hd ⊢
  split_ifs <;> omega

/-- Bytes of a concatenation of 128-byte blocks. -/
theorem byteAt_foldl (B : Nat → ByteArray) (hB : ∀ i, (B i).size = 128) :
    ∀ n, ((List.range n).foldl (fun out i => out ++ B i) ByteArray.empty).size = 128 * n ∧
      ∀ r o, r < n → o < 128 →
        MlDsaOptCommon.byteAt ((List.range n).foldl (fun out i => out ++ B i) ByteArray.empty) (128 * r + o) =
          MlDsaOptCommon.byteAt (B r) o
  | 0 => ⟨rfl, fun r o hr _ => absurd hr (by omega)⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := byteAt_foldl B hB n
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [ByteArray.size_append, ih1, hB]; ring, fun r o hr ho => ?_⟩
    by_cases hrn : r < n
    · rw [MlDsaOpt44.Proofs.SpecFacts.byteAt_app_lt (by rw [ih1]; omega), ih2 r o hrn ho]
    · rw [MlDsaOpt44.Proofs.SpecFacts.byteAt_app_ge (by rw [ih1]; omega), ih1,
        show r = n by omega, show 128 * n + o - 128 * n = o by omega]

theorem sbp15_size (w : Fips204.Poly) : (Fips204.simpleBitPack w 15).size = 128 := by
  have hb : Fips204.bitlen 15 = 4 := by decide
  simp [Fips204.simpleBitPack, hb, ByteArray.size]

/-- Byte `128 r + o` of `w1Encode` (`k` rows, `γ2 = 261888`) is byte `o` of row `r`'s
`SimpleBitPack(w1_r, 15)`. -/
theorem byteAt_w1Encode (Q : Params) (hQ : Q.gamma2 = 261888) (W : Array Fips204.Poly) {r o : Nat}
    (hr : r < Q.k) (ho : o < 128) :
    MlDsaOptCommon.byteAt (Fips204.w1Encode Q W) (128 * r + o) =
      MlDsaOptCommon.byteAt (Fips204.simpleBitPack W[r]! 15) o := by
  have hb : (Fips204.q - 1) / (2 * Q.gamma2) - 1 = 15 := by rw [hQ]; rfl
  unfold Fips204.w1Encode
  rw [hb]
  exact (byteAt_foldl _ (fun i => sbp15_size _) Q.k).2 r o hr ho

end MlDsaOpt65.Proofs.G5
