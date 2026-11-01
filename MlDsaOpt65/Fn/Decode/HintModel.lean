import MlDsaOpt65.Layout
import Mathlib.Tactic.SplitIfs
set_option warningAsError true
/-!
# `HintBitUnpack` (FIPS 204 Algorithm 21) as a run of the bytecode's loop (WP G2)

Parametric twin of `MlDsa44/Proofs/Math/Decode/Hint.lean` (any `k`, `ω`): the bytecode
runs Algorithm 21 with every `return ⊥` replaced by `good := 0` (clamping
`bound := index` when the count is out of range). `outerStep ω` models one iteration
of its outer loop over the hint bytes `y`; `hintBitUnpack_eq` says the spec returns
`some H` exactly when the model's `good` flag survives, with the same `H`.
-/

namespace MlDsaOpt65.Proofs.DecodeH

open MlDsa
open MlDsa.Fips204

/-- `h[i][v] := 1`, as Algorithm 21 writes it. -/
def setH (H : Array Poly) (i v : Nat) : Array Poly := H.set! i (H[i]!.set! v 1)

/-- Set `h[i][y idx] := 1` for every `idx ∈ l`. -/
def fillH (y : Nat → Nat) (i : Nat) (H : Array Poly) (l : List Nat) : Array Poly :=
  l.foldl (fun H idx => setH H i (y idx)) H

/-- The order check of index `idx` in the run starting at `first`. -/
def okIdx (y : Nat → Nat) (first idx : Nat) : Bool :=
  !(decide (idx > first)) || decide (y (idx - 1) < y idx)

/-- Model state of the outer loop: `index`, `good`, hint polynomials. -/
structure HS where
  index : Nat
  good : Bool
  H : Array Poly

/-- One iteration `i` of the outer loop of the bytecode. -/
def outerStep (ω : Nat) (y : Nat → Nat) (st : HS) (i : Nat) : HS :=
  let B := y (ω + i)
  if B < st.index ∨ ω < B then ⟨st.index, false, st.H⟩
  else
    let l := List.range' st.index (B - st.index)
    ⟨B, st.good && l.all (okIdx y st.index), fillH y i st.H l⟩

def hs0 (k : Nat) : HS := ⟨0, true, Array.replicate k zeroPoly⟩

/-- State after the outer loop. -/
def outerAll (k ω : Nat) (y : Nat → Nat) : HS := (List.range' 0 k).foldl (outerStep ω y) (hs0 k)

/-- The bytecode's final `good` flag. -/
def hintGood (k ω : Nat) (y : Nat → Nat) : Bool :=
  (outerAll k ω y).good &&
    (List.range' (outerAll k ω y).index (ω - (outerAll k ω y).index)).all (fun idx => y idx == 0)

theorem outerStep_good_false (ω : Nat) (y : Nat → Nat) (st : HS) (i : Nat) (h : st.good = false) :
    (outerStep ω y st i).good = false := by
  unfold outerStep; dsimp only; split <;> simp [h]

theorem foldl_good_false (ω : Nat) (y : Nat → Nat) : ∀ (l : List Nat) (st : HS), st.good = false →
    (l.foldl (outerStep ω y) st).good = false
  | [], _, h => h
  | i :: l, st, h => foldl_good_false ω y l _ (outerStep_good_false ω y st i h)

/-! ## Generic loop lemmas (`Id`, early exit through `some none`) -/

theorem forIn_inner {β : Type} {ok : Nat → Bool} {next : Nat → β → β}
    {G : Nat → Option (Option (Array Poly)) × β → Id (ForInStep (Option (Option (Array Poly)) × β))}
    (hG : ∀ idx b, G idx (none, b) =
      pure (if ok idx then .yield (none, next idx b) else .done (some none, b))) :
    ∀ (l : List Nat) (b : β), (forIn l (none, b) G : Id _) =
      pure (if l.all ok then (none, l.foldl (fun b idx => next idx b) b)
      else (some none, (forIn l (none, b) G : Id _).run.2))
  | [], b => by simp
  | idx :: l, b => by
    rw [List.forIn_cons, hG]
    by_cases hok : ok idx = true
    · simp only [hok, if_true, pure_bind, List.all_cons, Bool.true_and, List.foldl_cons]
      exact forIn_inner hG l (next idx b)
    · simp [hok]

theorem forIn_outer {ω : Nat} {y : Nat → Nat}
    {F : Nat → Option (Option (Array Poly)) × Array Poly × Nat →
      Id (ForInStep (Option (Option (Array Poly)) × Array Poly × Nat))}
    (hF : ∀ i (st : HS), st.good = true → ∃ X, F i (none, st.H, st.index) =
      pure (if (outerStep ω y st i).good then
        .yield (none, (outerStep ω y st i).H, (outerStep ω y st i).index) else .done (some none, X))) :
    ∀ (l : List Nat) (st : HS), st.good = true → (forIn l (none, st.H, st.index) F : Id _) =
      pure (if (l.foldl (outerStep ω y) st).good then
        (none, (l.foldl (outerStep ω y) st).H, (l.foldl (outerStep ω y) st).index)
      else (some none, (forIn l (none, st.H, st.index) F : Id _).run.2))
  | [], st, hg => by simp [hg]
  | i :: l, st, hg => by
    obtain ⟨X, hX⟩ := hF i st hg
    rw [List.forIn_cons, hX]
    by_cases hok : (outerStep ω y st i).good = true
    · simp only [hok, if_true, pure_bind, List.foldl_cons]
      exact forIn_outer hF l (outerStep ω y st i) hok
    · have hf : (outerStep ω y st i).good = false := by simpa using hok
      simp [hok, foldl_good_false ω y l _ hf]

/-! ## The spec -/

theorem range_size (a b : Nat) : [a:b].size = b - a := by simp

theorem hintBitUnpack_eq (Pa : Params) (Y : ByteArray) :
    hintBitUnpack Pa Y = if hintGood Pa.k Pa.omega (fun j => Y[j]!.toNat) then
      some (outerAll Pa.k Pa.omega (fun j => Y[j]!.toNat)).H else none := by
  unfold hintBitUnpack
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show [:Pa.k].size = Pa.k by simp,
    show ((none, Array.replicate Pa.k zeroPoly, 0) : Option (Option (Array Poly)) × Array Poly × Nat) =
      (none, (hs0 Pa.k).H, (hs0 Pa.k).index) from rfl,
    forIn_outer (ω := Pa.omega) (y := fun j => Y[j]!.toNat) ?_ _ (hs0 Pa.k) rfl]
  · simp only [hintGood, outerAll]
    by_cases hg : (List.foldl (outerStep Pa.omega fun j => Y[j]!.toNat) (hs0 Pa.k) (List.range' 0 Pa.k)).good = true
    · simp only [hg, if_true, Bool.true_and, pure_bind]
      rw [forIn_inner (ok := fun idx => Y[idx]!.toNat == 0) (next := fun _ b => b) ?_]
      · simp only [pure_bind, range_size]
        split_ifs <;> rfl
      · intro idx b
        by_cases h : Y[idx]!.toNat = 0 <;> simp [h]
    · have hg' : (List.foldl (outerStep Pa.omega fun j => Y[j]!.toNat) (hs0 Pa.k) (List.range' 0 Pa.k)).good = false := by
        simpa using hg
      simp only [hg', pure_bind]
      rfl
  · intro i st hg
    dsimp only
    rw [forIn_inner (ok := okIdx (fun j => Y[j]!.toNat) st.index)
      (next := fun idx H => setH H i Y[idx]!.toNat) ?_]
    · unfold outerStep
      simp only [range_size]
      split
      · rename_i hc
        have hbad : Y[Pa.omega + i]!.toNat < st.index ∨ Pa.omega < Y[Pa.omega + i]!.toNat := by
          simp only [Bool.or_eq_true] at hc
          rcases hc with h | h
          · exact Or.inl (of_decide_eq_true h)
          · exact Or.inr (of_decide_eq_true h)
        refine ⟨(st.H, st.index), ?_⟩
        simp only [hbad, ↓reduceIte]
        rfl
      · rename_i hc
        have hbad : ¬(Y[Pa.omega + i]!.toNat < st.index ∨ Pa.omega < Y[Pa.omega + i]!.toNat) := by
          rintro (h | h)
          · exact hc (by simp only [Bool.or_eq_true]; exact Or.inl (decide_eq_true h))
          · exact hc (by simp only [Bool.or_eq_true]; exact Or.inr (decide_eq_true h))
        simp only [hbad, ↓reduceIte]
        by_cases hs : (List.range' st.index (Y[Pa.omega + i]!.toNat - st.index)).all
            (okIdx (fun j => Y[j]!.toNat) st.index) = true
        · refine ⟨(st.H, st.index), ?_⟩
          simp only [hs, if_true, pure_bind, hg, Bool.true_and, fillH]
        · have hs' : (List.range' st.index (Y[Pa.omega + i]!.toNat - st.index)).all
              (okIdx (fun j => Y[j]!.toNat) st.index) = false := by simpa only [Bool.not_eq_true] using hs
          simp only [hs', if_false, pure_bind, hg, Bool.true_and, Bool.false_eq_true]
          exact ⟨_, rfl⟩
    · intro idx b
      unfold okIdx setH
      by_cases h1 : idx > st.index <;> by_cases h2 : Y[idx - 1]!.toNat < Y[idx]!.toNat <;> simp [h1, h2]

/-! ## Shape of the hint polynomials -/

/-- `k` polynomials of 256 coefficients, each `0` or `1`. -/
def WF (k : Nat) (H : Array Poly) : Prop :=
  H.size = k ∧ ∀ i, i < k → H[i]!.size = 256 ∧ ∀ j, j < 256 → H[i]![j]! = 0 ∨ H[i]![j]! = 1

theorem WF_hs0 (k : Nat) : WF k (hs0 k).H := by
  refine ⟨by simp [hs0], fun i hi => ?_⟩
  have h1 : (hs0 k).H[i]! = zeroPoly := by
    rw [getElem!_pos (hs0 k).H i (by simp [hs0]; omega)]; simp [hs0]
  rw [h1]
  refine ⟨by simp [zeroPoly], fun j hj => Or.inl ?_⟩
  rw [getElem!_pos zeroPoly j (by simp [zeroPoly]; omega)]; simp [zeroPoly]

/-- Rows past `k` (absent) read `0`. -/
theorem WF_get_out {k : Nat} {H : Array Poly} (hH : WF k H) {i j : Nat} (hi : k ≤ i) :
    H[i]![j]! = 0 := by
  rw [getElem!_neg H i (by rw [hH.1]; omega)]
  rfl

theorem setH_get {k : Nat} {H : Array Poly} (hH : WF k H) {i v i' j : Nat} (hi : i < k)
    (hj : j < 256) :
    (setH H i v)[i']![j]! = if i' = i ∧ j = v then 1 else H[i']![j]! := by
  have hs : H.size = k := hH.1
  have hrow : H[i]!.size = 256 := (hH.2 i hi).1
  unfold setH
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hi' : i' < k
  · have hrow' : H[i']!.size = 256 := (hH.2 i' hi').1
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
  · rw [getElem!_neg (H.setIfInBounds i _) i' (by simp [hs]; omega), if_neg (by omega),
      getElem!_neg H i' (by omega)]

theorem WF_setH {k : Nat} {H : Array Poly} (hH : WF k H) {i v : Nat} (hi : i < k) :
    WF k (setH H i v) := by
  have hs : H.size = k := hH.1
  refine ⟨by simp [setH, hs], fun i' hi' => ⟨?_, fun j hj => ?_⟩⟩
  · unfold setH
    simp only [Array.set!_eq_setIfInBounds]
    rw [getElem!_pos (H.setIfInBounds i _) i' (by simp [hs, hi']),
      Array.getElem_setIfInBounds (by simp [hs, hi'])]
    split
    · simp [(hH.2 i hi).1]
    · rw [← getElem!_pos H i' (by omega)]; exact (hH.2 i' hi').1
  · rw [setH_get hH hi hj]
    split
    · exact Or.inr rfl
    · exact (hH.2 i' hi').2 j hj

end MlDsaOpt65.Proofs.DecodeH
