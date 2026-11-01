import MlDsaOpt44.Layout
import MlDsaOpt44.Math.Ntt.Conv
import MlDsaOpt44.Math.Facts
import MlDsa44.Proofs.Math.NttMod
/-!
# One row of `w′`: spec data flow vs. the bytecode's data flow

`nttInv_row`: if `X ≡ AZ − NTT(c) ∘ NTT(T)` then
`NTT⁻¹ X ≡ NTT⁻¹ AZ − c · T` (linearity of `NTT⁻¹` and the convolution theorem),
plus the coefficient bookkeeping (`toF` of `addNTT`, `multiplyNTT`, `azRow`, …)
used by `accepts_eq_optAccepts`.
-/

namespace MlDsaOpt44.Proofs.RowMath

open MlDsa44 MlDsaOpt44.Proofs.NttConv

theorem list_sum_cast (n : Nat) (g : Nat → Int) :
    ((((List.range n).map g).sum : Int) : F) = ∑ i ∈ Finset.range n, (g i : F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Int.cast_add, ih, Finset.sum_range_succ]
    simp

theorem negacyclic_cast (c f : Fips204.Poly) (t : Nat) :
    ((negacyclic c f t : Int) : F) = negF (toF c) (toF f) t := by
  unfold negacyclic negF
  rw [list_sum_cast]
  apply Finset.sum_congr rfl
  intro p _
  unfold toF
  split <;> push_cast <;> rfl

theorem negF_congr (c : Nat → F) {t t' : Nat → F} (h : ∀ j, j < 256 → t j = t' j) {k : Nat}
    (hk : k < 256) : negF c t k = negF c t' k := by
  unfold negF
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_range] at hp
  split
  · rw [h _ (by omega)]
  · rw [h _ (by omega)]

theorem negF_smul (c t : Nat → F) (a : F) (k : Nat) :
    negF c (fun j => a * t j) k = a * negF c t k := by
  unfold negF
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split <;> ring

theorem toF_map_range (G : Nat → Int) {j : Nat} (hj : j < 256) :
    toF ((Array.range 256).map G) j = (G j : F) := by
  unfold toF; rw [Proofs.Math.getElem!_map_range 256 j G hj]

theorem toF_map (f : Fips204.Poly) (G : Int → Int) {j : Nat} (hj : j < f.size) :
    toF (f.map G) j = (G f[j]! : F) := by
  unfold toF; rw [Proofs.Math.getElem!_map f G j hj]

theorem toF_addNTT (a b : Fips204.Poly) {j : Nat} (hj : j < 256) :
    toF (Fips204.addNTT a b) j = toF a j + toF b j := by
  unfold Fips204.addNTT; rw [toF_map_range _ hj, cast_emod, Int.cast_add]; rfl

theorem toF_mulNTT (a b : Fips204.Poly) {j : Nat} (hj : j < 256) :
    toF (Fips204.multiplyNTT a b) j = toF a j * toF b j := by
  unfold Fips204.multiplyNTT; rw [toF_map_range _ hj, cast_emod, Int.cast_mul]; rfl

theorem toF_zero (j : Nat) : toF Fips204.zeroPoly j = 0 := by
  unfold toF Fips204.zeroPoly
  by_cases h : j < 256
  · simp [getElem!_pos, h]
  · simp [getElem!_neg, h]

theorem eq_of_toF {a b : Int} (h : (a : F) = (b : F)) : a % (Fips204.q : Int) = b % (Fips204.q : Int) :=
  (ZMod.intCast_eq_intCast_iff' a b 8380417).1 h

/-- `UseHint` only sees its argument modulo `q`. -/
theorem useHint_congr (h : Int) {a b : Int} (hab : (a : F) = (b : F)) :
    Fips204.useHint h a = Fips204.useHint h b := by
  rw [← Facts.useHint_emod h a, ← Facts.useHint_emod h b, eq_of_toF hab]

/-- **Row identity**: `X ≡ AZ − NTT(c) ∘ NTT(T)` gives `NTT⁻¹ X ≡ NTT⁻¹ AZ − c · T`. -/
theorem nttInv_row (X AZ c T : Fips204.Poly) (hX : X.size = 256) (hAZ : AZ.size = 256)
    (hc : c.size = 256) (hT : T.size = 256)
    (h : ∀ j, j < 256 → toF X j = toF AZ j - toF (Fips204.ntt c) j * toF (Fips204.ntt T) j)
    {j : Nat} (hj : j < 256) :
    toF (Fips204.nttInv X) j = toF (Fips204.nttInv AZ) j - negF (toF c) (toF T) j := by
  obtain ⟨-, eX⟩ := nttInv_spec X hX
  obtain ⟨-, eA⟩ := nttInv_spec AZ hAZ
  have hV : (Fips204.multiplyNTT (Fips204.ntt c) (Fips204.ntt T)).size = 256 := by
    simp [Fips204.multiplyNTT]
  obtain ⟨-, eV⟩ := nttInv_spec _ hV
  have hconv := conv c T _ hc hT hV (fun j hj => toF_mulNTT _ _ hj) hj
  rw [eV j hj] at hconv
  rw [eX j hj, eA j hj, ← hconv,
    If_congr (u := toF X) (v := fun j => toF AZ j - toF (Fips204.multiplyNTT (Fips204.ntt c)
      (Fips204.ntt T)) j) (fun j hj => by rw [h j hj, toF_mulNTT _ _ hj]) 8 (Nat.le_refl _) j hj,
    If_sub]
  ring

/-- `Â ∘ ẑ` row as `MatrixVectorNTT` folds it. -/
theorem toF_azFold (A zs : Array Fips204.Poly) {j : Nat} (hj : j < 256) :
    toF ((List.range Fips204.l).foldl
      (fun acc s => Fips204.addNTT acc (Fips204.multiplyNTT A[s]! zs[s]!)) Fips204.zeroPoly) j =
      toF A[0]! j * toF zs[0]! j + toF A[1]! j * toF zs[1]! j + toF A[2]! j * toF zs[2]! j +
        toF A[3]! j * toF zs[3]! j := by
  rw [show List.range Fips204.l = [0, 1, 2, 3] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, toF_addNTT _ _ hj, toF_mulNTT _ _ hj, toF_zero,
    zero_add]

theorem toF_azRow (cd : ByteArray) (r : Nat) {j : Nat} (hj : j < 256) :
    toF (azRow cd r) j =
      toF (aD cd r 0) j * toF (zHat cd 0) j + toF (aD cd r 1) j * toF (zHat cd 1) j +
        toF (aD cd r 2) j * toF (zHat cd 2) j + toF (aD cd r 3) j * toF (zHat cd 3) j := by
  unfold azRow
  rw [toF_map_range _ hj, cast_emod, list_sum_cast]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Int.cast_mul]
  rfl

end MlDsaOpt44.Proofs.RowMath
