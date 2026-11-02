import MlDsaOpt44.Fn.Ct.Csum4Spec
import MlDsaOpt65.Fn.Csum.Defs
set_option warningAsError true
/-!
# `csum` (v4): counting facts about `c` (ML-DSA-65)

As `MlDsaOpt44/Fn/Ct/Csum4Spec.lean` with `τ = 49` and the table rows at calldata
offset `off`: `sPrime` is the sum over the `BASES` list, the running count
`N c t'` (the 44 definition `CS4.N`) starts at `τ − negCount c` and steps by the
`CW` code of `c[t']`, and `nNeg c t = N c (t + 1)`.
-/

namespace MlDsaOpt65.Proofs.G4

open EvmSemantics
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs.CS4 (N N_step_gen N_zero_gen sum_ite_filter)

/-- Facts about `c` that `CRep` and SampleInBall provide. -/
structure CFacts (c : Fips204.Poly) (ps : List Nat) : Prop where
  coeff : ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1
  len : ps.length = 49
  nodup : ps.Nodup
  mem : ∀ p, p ∈ ps ↔ p < 256 ∧ c[p]! ≠ 0

theorem support_perm {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) :
    ((List.range 256).filter fun p => !decide (c[p]! = 0)).Perm ps := by
  rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) h.nodup]
  intro p
  rw [h.mem, List.mem_filter, List.mem_range]
  simp

theorem sum_over_ps {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) (F : Nat → Nat) :
    ((List.range 256).map fun p => if c[p]! = 0 then 0 else F p).sum =
      ((List.range 49).map fun i => F ps[i]!).sum := by
  rw [sum_ite_filter, (support_perm h).map F |>.sum_eq]
  congr 1
  apply List.ext_getElem
  · simp [h.len]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have := h.len
    rw [List.length_map] at h1
    rw [getElem!_pos ps i (by omega)]

/-- `sPrime` as a sum over the `BASES` list. -/
theorem sPrime_ps {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) (cd : ByteArray)
    (off r t : Nat) :
    sPrime c cd off r t = ((List.range 49).map fun i =>
      tEntry cd off r (t + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0)).sum := by
  unfold sPrime
  exact sum_over_ps h (fun p => tEntry cd off r (t + 256 - p + if c[p]! = -1 then 256 else 0))

theorem nNeg_eq (c : Fips204.Poly) (t : Nat) : nNeg c t = N c (t + 1) := by
  unfold nNeg N
  congr 1
  apply List.filter_congr
  intro p _
  simp only [decide_eq_decide]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
    first | (left; exact ⟨by omega, h2⟩) | (right; exact ⟨by omega, h2⟩)

theorem N_step {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {t' : Nat} (ht : t' < 256) :
    N c (t' + 1) + (if c[t']! = 1 then 1 else 0) = N c t' + (if c[t']! = -1 then 1 else 0) :=
  N_step_gen c 256 h.coeff ht

theorem N_zero {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) : N c 0 + negCount c = 49 := by
  have hsupp : ((List.range 256).filter fun p => !decide (c[p]! = 0)).length = 49 := by
    rw [(support_perm h).length_eq, h.len]
  rw [← hsupp]
  exact N_zero_gen c 256 h.coeff

theorem negCount_le {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) : negCount c ≤ 49 := by
  have := N_zero h; omega

end MlDsaOpt65.Proofs.G4
