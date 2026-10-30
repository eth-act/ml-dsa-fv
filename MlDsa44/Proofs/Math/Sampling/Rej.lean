import MlDsa44.Spec
set_option warningAsError true
/-!
# `rejNTTPolyOf` as a left fold

`rejNTTPolyOf_eq`: the spec loop is `(List.range 336).foldl (rejStep s)`, and
each step accepts the candidate `rejZv s t` (the bytecode's OR/AND form) iff
it is below `q`.
-/

namespace MlDsa44.Proofs.Sampling

open MlDsa44

theorem forIn_id_eq_foldl {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  have : f = fun a b => pure (.yield (g b a)) := funext fun a => funext fun b => h a b
  subst this
  exact List.forIn_pure_yield_eq_foldl _ _

theorem getElem!_set! (a : Array Int) (i j : Nat) (z : Int) :
    (a.set! j z)[i]! = if i = j ∧ j < a.size then z else a[i]! := by
  simp only [getElem!_def, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size <;> simp [h2]
  · simp [Ne.symm h1, h1]

theorem size_set! (a : Array Int) (j : Nat) (z : Int) : (a.set! j z).size = a.size := by
  simp

/-- The candidate coefficient of triple `t`, in the bytecode's OR/AND form. -/
def rejZv (s : ByteArray) (t : Nat) : Nat :=
  s[3 * t]!.toNat ||| s[3 * t + 1]!.toNat * 256 ||| (s[3 * t + 2]!.toNat &&& 127) * 65536

theorem or3_eq (b0 b1 b2 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    b0 ||| b1 * 256 ||| (b2 &&& 127) * 65536 = 65536 * (b2 % 128) + 256 * b1 + b0 := by
  have hm : b2 &&& 127 = b2 % 128 := Nat.and_two_pow_sub_one_eq_mod b2 7
  have e1 : b0 ||| b1 * 256 = b1 * 256 + b0 := by
    rw [Nat.or_comm, show b1 * 256 = b1 <<< 8 by simp [Nat.shiftLeft_eq],
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  have e2 : b1 * 256 + b0 ||| (b2 % 128) * 65536 = (b2 % 128) * 65536 + (b1 * 256 + b0) := by
    rw [Nat.or_comm, show (b2 % 128) * 65536 = (b2 % 128) <<< 16 by simp [Nat.shiftLeft_eq],
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  rw [e1, hm, e2]; omega

theorem rejZv_lt (s : ByteArray) (t : Nat) : rejZv s t < 2 ^ 24 := by
  unfold rejZv
  rw [or3_eq _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _)]
  have := UInt8.toNat_lt s[3 * t + 1]!
  have := UInt8.toNat_lt s[3 * t]!
  omega

theorem coeff_eq (s : ByteArray) (t : Nat) :
    Fips204.coeffFromThreeBytes s[3 * t]!.toNat s[3 * t + 1]!.toNat s[3 * t + 2]!.toNat =
      if rejZv s t < Fips204.q then some (rejZv s t : Int) else none := by
  unfold Fips204.coeffFromThreeBytes rejZv
  rw [or3_eq _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _)]
  have h2 := UInt8.toNat_lt s[3 * t + 2]!
  have : (if s[3 * t + 2]!.toNat > 127 then s[3 * t + 2]!.toNat - 128 else s[3 * t + 2]!.toNat) =
      s[3 * t + 2]!.toNat % 128 := by split <;> omega
  simp only [this]

/-- One step of the RejNTTPoly scan on the state `(a, j)`. -/
def rejStep (s : ByteArray) (st : Fips204.Poly × Nat) (t : Nat) : Fips204.Poly × Nat :=
  if st.2 < 256 ∧ rejZv s t < Fips204.q then (st.1.set! st.2 (rejZv s t : Int), st.2 + 1) else st

/-- The scan state after `t` triples. -/
def rejFold (s : ByteArray) (t : Nat) : Fips204.Poly × Nat :=
  (List.range t).foldl (rejStep s) (Fips204.zeroPoly, 0)

theorem rejFold_zero (s : ByteArray) : rejFold s 0 = (Fips204.zeroPoly, 0) := rfl

theorem rejFold_succ (s : ByteArray) (t : Nat) :
    rejFold s (t + 1) = rejStep s (rejFold s t) t := by
  simp [rejFold, List.range_succ, List.foldl_append]

theorem rejNTTPolyOf_eq (s : ByteArray) : Fips204.rejNTTPolyOf s =
    if (rejFold s 336).2 < 256 then none else some (rejFold s 336).1 := by
  unfold Fips204.rejNTTPolyOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_id_eq_foldl _ _ _ (rejStep s)]
  · have hr : List.range' 0 [:Fips204.rejNTTPolyLimit / 3].size = List.range 336 := by
      rw [List.range_eq_range']; rfl
    rw [hr]; rfl
  · intro t st
    unfold rejStep
    rw [coeff_eq]
    by_cases h1 : st.2 < 256
    · by_cases h2 : rejZv s t < Fips204.q <;> simp [h1, h2]
    · simp [h1]

/-- Invariants of the scan: size, count bound, reduced coefficients. -/
theorem rejFold_inv (s : ByteArray) : ∀ t,
    (rejFold s t).1.size = 256 ∧ (rejFold s t).2 ≤ 256 ∧
      ∀ i, i < 256 → (0 : Int) ≤ (rejFold s t).1[i]! ∧ (rejFold s t).1[i]! < (Fips204.q : Int)
  | 0 => by
    refine ⟨by simp [rejFold_zero, Fips204.zeroPoly], by simp [rejFold_zero], fun i hi => ?_⟩
    simp [rejFold_zero, Fips204.zeroPoly, hi, Fips204.q]
  | t + 1 => by
    obtain ⟨h1, h2, h3⟩ := rejFold_inv s t
    rw [rejFold_succ]
    unfold rejStep
    split
    · rename_i h
      refine ⟨by simp only; rw [size_set!, h1], by simp only; omega, fun i hi => ?_⟩
      simp only
      rw [getElem!_set!]
      split
      · exact ⟨by omega, by exact_mod_cast h.2⟩
      · exact h3 i hi
    · exact ⟨h1, h2, h3⟩

end MlDsa44.Proofs.Sampling
