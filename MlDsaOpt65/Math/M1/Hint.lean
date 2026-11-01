import MlDsa.Spec.Fips204
import MlDsa44.Proofs.Math.Decode.Hint
/-!
# HintBitUnpack for any parameter set (work package M1)

`MlDsa44.Proofs.Decode` (`Decode/Hint.lean`) with `k` and `ω` parameters:
`hintBitUnpack_eq` models Algorithm 21 as a fold whose early returns clear a
`good` flag, and `hintBitUnpack_range` says a decoded hint has `k` rows of 256
coefficients in `{0, 1}`. Shared by the ML-DSA-65 and ML-DSA-87 proofs.
-/

namespace MlDsaOptM1

open MlDsa MlDsa.Fips204
open MlDsa44.Proofs.Decode (forIn_inner range_size)

/-- `h[i][v] := 1`, as Algorithm 21 writes it. -/
def setH (H : Array Poly) (i v : Nat) : Array Poly := H.set! i (H[i]!.set! v 1)

/-- Set `h[i][y idx] := 1` for every `idx ∈ l`. -/
def fillH (y : Nat → Nat) (i : Nat) (H : Array Poly) (l : List Nat) : Array Poly :=
  l.foldl (fun H idx => setH H i (y idx)) H

/-- Model state of the outer loop: `index`, `good`, hint polynomials. -/
structure HS where
  index : Nat
  good : Bool
  H : Array Poly

/-- One iteration `i` of the outer loop. -/
def outerStep (P : Params) (y : Nat → Nat) (st : HS) (i : Nat) : HS :=
  let B := y (P.omega + i)
  if B < st.index ∨ P.omega < B then ⟨st.index, false, st.H⟩
  else
    let l := List.range' st.index (B - st.index)
    ⟨B, st.good && l.all (MlDsa44.Proofs.Decode.okIdx y st.index), fillH y i st.H l⟩

def hs0 (P : Params) : HS := ⟨0, true, Array.replicate P.k zeroPoly⟩

/-- State after the outer loop. -/
def outerAll (P : Params) (y : Nat → Nat) : HS := (List.range P.k).foldl (outerStep P y) (hs0 P)

/-- The final `good` flag. -/
def hintGood (P : Params) (y : Nat → Nat) : Bool :=
  (outerAll P y).good &&
    (List.range' (outerAll P y).index (P.omega - (outerAll P y).index)).all (fun idx => y idx == 0)

theorem outerStep_good_false (P : Params) (y : Nat → Nat) (st : HS) (i : Nat)
    (h : st.good = false) : (outerStep P y st i).good = false := by
  unfold outerStep; dsimp only; split <;> simp [h]

theorem foldl_good_false (P : Params) (y : Nat → Nat) : ∀ (l : List Nat) (st : HS),
    st.good = false → (l.foldl (outerStep P y) st).good = false
  | [], _, h => h
  | i :: l, st, h => foldl_good_false P y l _ (outerStep_good_false P y st i h)

theorem forIn_outer (P : Params) {y : Nat → Nat}
    {F : Nat → Option (Option (Array Poly)) × Array Poly × Nat →
      Id (ForInStep (Option (Option (Array Poly)) × Array Poly × Nat))}
    (hF : ∀ i (st : HS), st.good = true → ∃ X, F i (none, st.H, st.index) =
      pure (if (outerStep P y st i).good then
        .yield (none, (outerStep P y st i).H, (outerStep P y st i).index)
        else .done (some none, X))) :
    ∀ (l : List Nat) (st : HS), st.good = true → (forIn l (none, st.H, st.index) F : Id _) =
      pure (if (l.foldl (outerStep P y) st).good then
        (none, (l.foldl (outerStep P y) st).H, (l.foldl (outerStep P y) st).index)
      else (some none, (forIn l (none, st.H, st.index) F : Id _).run.2))
  | [], st, hg => by simp [hg]
  | i :: l, st, hg => by
    obtain ⟨X, hX⟩ := hF i st hg
    rw [List.forIn_cons, hX]
    by_cases hok : (outerStep P y st i).good = true
    · simp only [hok, if_true, pure_bind, List.foldl_cons]
      exact forIn_outer P hF l (outerStep P y st i) hok
    · have hf : (outerStep P y st i).good = false := by simpa using hok
      simp [hok, foldl_good_false P y l _ hf]

theorem hintBitUnpack_eq (P : Params) (Y : ByteArray) :
    hintBitUnpack P Y = if hintGood P (fun j => Y[j]!.toNat) then
      some (outerAll P (fun j => Y[j]!.toNat)).H else none := by
  unfold hintBitUnpack
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show List.range' 0 [:P.k].size = List.range P.k by simp [List.range_eq_range'],
    show ((none, Array.replicate P.k zeroPoly, 0) :
        Option (Option (Array Poly)) × Array Poly × Nat) =
      (none, (hs0 P).H, (hs0 P).index) from rfl,
    forIn_outer P (y := fun j => Y[j]!.toNat) ?_ _ (hs0 P) rfl]
  · simp only [hintGood, outerAll]
    by_cases hg : (List.foldl (outerStep P fun j => Y[j]!.toNat) (hs0 P) (List.range P.k)).good = true
    · simp only [hg, if_true, Bool.true_and, pure_bind]
      rw [forIn_inner (ok := fun idx => Y[idx]!.toNat == 0) (next := fun _ b => b) ?_]
      · simp only [pure_bind, range_size]
        split_ifs <;> rfl
      · intro idx b
        by_cases h : Y[idx]!.toNat = 0 <;> simp [h]
    · have hg' : (List.foldl (outerStep P fun j => Y[j]!.toNat) (hs0 P) (List.range P.k)).good =
          false := by simpa using hg
      simp only [hg', pure_bind]
      rfl
  · intro i st hg
    dsimp only
    rw [forIn_inner (ok := MlDsa44.Proofs.Decode.okIdx (fun j => Y[j]!.toNat) st.index)
      (next := fun idx H => setH H i Y[idx]!.toNat) ?_]
    · unfold outerStep
      simp only [range_size]
      split
      · rename_i hc
        have hbad : Y[P.omega + i]!.toNat < st.index ∨ P.omega < Y[P.omega + i]!.toNat := by
          simp only [Bool.or_eq_true] at hc
          rcases hc with h | h
          · exact Or.inl (of_decide_eq_true h)
          · exact Or.inr (of_decide_eq_true h)
        refine ⟨(st.H, st.index), ?_⟩
        simp only [hbad, ↓reduceIte]
        rfl
      · rename_i hc
        have hbad : ¬(Y[P.omega + i]!.toNat < st.index ∨ P.omega < Y[P.omega + i]!.toNat) := by
          rintro (h | h)
          · exact hc (by simp only [Bool.or_eq_true]; exact Or.inl (decide_eq_true h))
          · exact hc (by simp only [Bool.or_eq_true]; exact Or.inr (decide_eq_true h))
        simp only [hbad, ↓reduceIte]
        by_cases hs : (List.range' st.index (Y[P.omega + i]!.toNat - st.index)).all
            (MlDsa44.Proofs.Decode.okIdx (fun j => Y[j]!.toNat) st.index) = true
        · refine ⟨(st.H, st.index), ?_⟩
          simp only [hs, if_true, pure_bind, hg, Bool.true_and, fillH]
        · have hs' : (List.range' st.index (Y[P.omega + i]!.toNat - st.index)).all
              (MlDsa44.Proofs.Decode.okIdx (fun j => Y[j]!.toNat) st.index) = false := by
            simpa only [Bool.not_eq_true] using hs
          simp only [hs', if_false, pure_bind, hg, Bool.true_and, Bool.false_eq_true]
          exact ⟨_, rfl⟩
    · intro idx b
      unfold MlDsa44.Proofs.Decode.okIdx setH
      by_cases h1 : idx > st.index <;> by_cases h2 : Y[idx - 1]!.toNat < Y[idx]!.toNat <;>
        simp [h1, h2]

/-! ## Shape of the hint polynomials -/

/-- `n` polynomials of 256 coefficients, each `0` or `1`. -/
def WF (n : Nat) (H : Array Poly) : Prop :=
  H.size = n ∧ ∀ i, i < n → H[i]!.size = 256 ∧ ∀ j, j < 256 → H[i]![j]! = 0 ∨ H[i]![j]! = 1

theorem WF_hs0 (P : Params) : WF P.k (hs0 P).H := by
  refine ⟨by simp [hs0], fun i hi => ?_⟩
  have h1 : (hs0 P).H[i]! = zeroPoly := by
    rw [getElem!_pos (hs0 P).H i (by simp [hs0]; omega)]; simp [hs0]
  rw [h1]
  refine ⟨by simp [zeroPoly], fun j hj => Or.inl ?_⟩
  rw [getElem!_pos zeroPoly j (by simp [zeroPoly]; omega)]; simp [zeroPoly]

theorem setH_get {n : Nat} {H : Array Poly} (hH : WF n H) {i v i' j : Nat} (hi : i < n)
    (hi' : i' < n) (hj : j < 256) :
    (setH H i v)[i']![j]! = if i' = i ∧ j = v then 1 else H[i']![j]! := by
  have hs : H.size = n := hH.1
  have hrow : H[i]!.size = 256 := (hH.2 i hi).1
  unfold setH
  simp only [Array.set!_eq_setIfInBounds]
  rw [getElem!_pos (H.setIfInBounds i _) i' (by simp [hs, hi'])]
  rw [Array.getElem_setIfInBounds (by simp [hs, hi'])]
  by_cases hii : i = i'
  · subst hii
    rw [if_pos rfl]
    rw [getElem!_pos (H[i]!.setIfInBounds v 1) j (by simp [hrow, hj]),
      Array.getElem_setIfInBounds (by simp [hrow, hj])]
    by_cases hjv : v = j
    · subst hjv; simp
    · rw [if_neg hjv, if_neg (by omega), getElem!_pos H[i]! j (by simp [hrow, hj])]
  · rw [if_neg hii, if_neg (by omega), getElem!_pos H i' (by omega)]

theorem WF_setH {n : Nat} {H : Array Poly} (hH : WF n H) {i v : Nat} (hi : i < n) :
    WF n (setH H i v) := by
  have hs : H.size = n := hH.1
  refine ⟨by simp [setH, hs], fun i' hi' => ⟨?_, fun j hj => ?_⟩⟩
  · unfold setH
    simp only [Array.set!_eq_setIfInBounds]
    rw [getElem!_pos (H.setIfInBounds i _) i' (by simp [hs, hi']),
      Array.getElem_setIfInBounds (by simp [hs, hi'])]
    split
    · simp [(hH.2 i hi).1]
    · rw [← getElem!_pos H i' (by omega)]; exact (hH.2 i' hi').1
  · rw [setH_get hH hi hi' hj]
    split
    · exact Or.inr rfl
    · exact (hH.2 i' hi').2 j hj

theorem WF_fillH (n : Nat) (y : Nat → Nat) {i : Nat} (hi : i < n) :
    ∀ (l : List Nat) (H : Array Poly), WF n H → WF n (fillH y i H l)
  | [], _, hH => hH
  | _ :: l, _, hH => WF_fillH n y hi l _ (WF_setH hH hi)

theorem WF_foldl (P : Params) (y : Nat → Nat) :
    ∀ (l : List Nat) (st : HS), (∀ i ∈ l, i < P.k) → WF P.k st.H →
      WF P.k (l.foldl (outerStep P y) st).H
  | [], _, _, hH => hH
  | i :: l, st, hl, hH => by
    rw [List.foldl_cons]
    apply WF_foldl P y l _ (fun j hj => hl j (by simp [hj]))
    unfold outerStep
    dsimp only
    split
    · exact hH
    · exact WF_fillH P.k y (hl i (by simp)) _ _ hH

/-- HintBitUnpack outputs `k` rows of 0/1 coefficients. -/
theorem hintBitUnpack_range (P : Params) (y : ByteArray) (h : Array Poly)
    (hh : hintBitUnpack P y = some h) {r t : Nat} (hr : r < P.k) (ht : t < 256) :
    (0 : Int) ≤ h[r]![t]! ∧ h[r]![t]! ≤ 1 := by
  rw [hintBitUnpack_eq] at hh
  by_cases hg : hintGood P (fun j => y[j]!.toNat) = true
  · rw [if_pos hg] at hh
    have e := Option.some.inj hh
    subst e
    have hw := WF_foldl P (fun j => y[j]!.toNat) (List.range P.k) (hs0 P)
      (by simp) (WF_hs0 P)
    unfold outerAll
    rcases (hw.2 r hr).2 t ht with h1 | h1 <;> rw [h1] <;> decide
  · rw [if_neg hg] at hh; exact absurd hh (by simp)

/-- A decoded hint is `k` rows of 256 coefficients. -/
theorem hintBitUnpack_size (P : Params) (y : ByteArray) (h : Array Poly)
    (hh : hintBitUnpack P y = some h) : h.size = P.k := by
  rw [hintBitUnpack_eq] at hh
  by_cases hg : hintGood P (fun j => y[j]!.toNat) = true
  · rw [if_pos hg] at hh
    have e := Option.some.inj hh
    subst e
    exact (WF_foldl P (fun j => y[j]!.toNat) (List.range P.k) (hs0 P) (by simp) (WF_hs0 P)).1
  · rw [if_neg hg] at hh; exact absurd hh (by simp)

end MlDsaOptM1
