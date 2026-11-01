import MlDsaOpt44.Fn.Ct.Defs
/-!
# `csum` (WP10): counting facts about `c`

* `sPrime` is the sum over the `BASES` list (a permutation of the support);
* `N c t'` (negative contributions with the split at `t'`) steps by the
  `CW` code of `c[t']`, starts at the number of `+1` coefficients
  `τ − negCount c`, and `nNeg c t = N c (t + 1)`.
-/

namespace MlDsaOpt44.Proofs.CS

open EvmSemantics
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs

theorem sum_ite_filter (l : List Nat) (q : Nat → Prop) [DecidablePred q] (F : Nat → Nat) :
    (l.map fun p => if q p then 0 else F p).sum = ((l.filter fun p => !decide (q p)).map F).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : q a
    · simp [h, ih]
    · simp [h, ih]

theorem len_filter_sum (l : List Nat) (P : Nat → Bool) :
    (l.filter P).length = (l.map fun p => if P p then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : P a <;> simp [h, ih]; omega

theorem single_sum (n a : Nat) (Q : Prop) [Decidable Q] :
    ((List.range n).map fun p => if p = a ∧ Q then 1 else 0).sum = if a < n ∧ Q then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hq : Q <;> by_cases han : a < n <;> by_cases ha : n = a <;>
      (simp [hq, han, ha, show a < n + 1 ↔ a < n ∨ a = n by omega]; try omega)

/-- Facts about `c` that `CRep` and SampleInBall provide. -/
structure CFacts (c : Fips204.Poly) (ps : List Nat) : Prop where
  coeff : ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1
  len : ps.length = 39
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
      ((List.range 39).map fun i => F ps[i]!).sum := by
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
theorem sPrime_ps {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) (cd : ByteArray) (r t : Nat) :
    sPrime c cd r t = ((List.range 39).map fun i =>
      tEntry cd r (t + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0)).sum := by
  unfold sPrime
  exact sum_over_ps h (fun p => tEntry cd r (t + 256 - p + if c[p]! = -1 then 256 else 0))

/-- Negative contributions with the split before `t'`. -/
def N (c : Fips204.Poly) (t' : Nat) : Nat :=
  ((List.range 256).filter fun p => (p < t' ∧ c[p]! = -1) ∨ (t' ≤ p ∧ c[p]! = 1)).length

theorem nNeg_eq (c : Fips204.Poly) (t : Nat) : nNeg c t = N c (t + 1) := by
  unfold nNeg N
  congr 1
  apply List.filter_congr
  intro p _
  simp only [decide_eq_decide]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> first | (left; exact ⟨by omega, h2⟩) | (right; exact ⟨by omega, h2⟩)

theorem N_step_gen (c : Fips204.Poly) (n : Nat) (coeff : ∀ t, t < n → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1)
    {t' : Nat} (ht : t' < n) :
    ((List.range n).filter fun p => (p < t' + 1 ∧ c[p]! = -1) ∨ (t' + 1 ≤ p ∧ c[p]! = 1)).length +
        (if c[t']! = 1 then 1 else 0) =
      ((List.range n).filter fun p => (p < t' ∧ c[p]! = -1) ∨ (t' ≤ p ∧ c[p]! = 1)).length +
        (if c[t']! = -1 then 1 else 0) := by
  rw [len_filter_sum, len_filter_sum]
  have e1 := single_sum n t' (c[t']! = 1)
  have e2 := single_sum n t' (c[t']! = -1)
  simp only [ht, true_and] at e1 e2
  rw [← e1, ← e2, ← List.sum_map_add, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [List.mem_range] at hp
  have hc := coeff p hp
  by_cases hpt : p = t'
  · subst hpt; rcases hc with hc | hc | hc <;> simp [hc]
  · by_cases hlt : p < t'
    · simp [hpt, hlt, show p < t' + 1 by omega, show ¬ t' + 1 ≤ p by omega, show ¬ t' ≤ p by omega]
    · simp [hpt, hlt, show ¬ p < t' + 1 by omega, show t' + 1 ≤ p by omega, show t' ≤ p by omega]

theorem N_step {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {t' : Nat} (ht : t' < 256) :
    N c (t' + 1) + (if c[t']! = 1 then 1 else 0) = N c t' + (if c[t']! = -1 then 1 else 0) :=
  N_step_gen c 256 h.coeff ht

theorem N_zero_gen (c : Fips204.Poly) (n : Nat) (coeff : ∀ t, t < n → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) :
    ((List.range n).filter fun p => (p < 0 ∧ c[p]! = -1) ∨ (0 ≤ p ∧ c[p]! = 1)).length +
      ((List.range n).filter fun p => c[p]! = -1).length =
      ((List.range n).filter fun p => !decide (c[p]! = 0)).length := by
  rw [len_filter_sum, len_filter_sum, len_filter_sum, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [List.mem_range] at hp
  rcases coeff p hp with hc | hc | hc <;> simp [hc]

theorem N_zero {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) : N c 0 + negCount c = 39 := by
  have hsupp : ((List.range 256).filter fun p => !decide (c[p]! = 0)).length = 39 := by
    rw [(support_perm h).length_eq, h.len]
  rw [← hsupp]
  exact N_zero_gen c 256 h.coeff

theorem negCount_le {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) : negCount c ≤ 39 := by
  have := N_zero h; omega

/-- The running `n_neg` word: base. -/
theorem g_zero {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) :
    UInt256.ofNat 39 - UInt256.ofNat (negCount c) = UInt256.ofNat (N c 0) := by
  rw [ofNat_sub (negCount_le h) (by norm_num)]
  congr 1; have := N_zero h; omega

/-- The running `n_neg` word: one `CW` code. -/
theorem g_step {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {t' : Nat} (ht : t' < 256) :
    UInt256.ofNat (N c t') + UInt256.ofNat (codeOf c[t']!) = UInt256.ofNat (N c (t' + 1)) := by
  rw [EvmProof.Word.ofNat_add_mod, ofNat_eq_ofNat_iff]
  have hs := N_step h ht
  unfold codeOf
  rcases h.coeff t' ht with hc | hc | hc <;> simp [hc] at hs ⊢ <;> omega

end MlDsaOpt44.Proofs.CS
