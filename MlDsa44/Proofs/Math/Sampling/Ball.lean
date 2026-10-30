import MlDsa44.Proofs.Math.Sampling.Rej
set_option warningAsError true
/-!
# `sampleInBallOf` as a scan over byte positions

The spec iterates over `i ∈ [217, 256)` and searches the next accepted
position with `sampleIndex`; the bytecode iterates over positions
`p ∈ [8, 272)` and advances `i` on acceptance. `sampleInBallOf_eq` shows both
compute the same thing: `ballFold s 264` is the bytecode's scan.
-/

namespace MlDsa44.Proofs.Sampling

open MlDsa44

/-- The sign written for index `i` (Algorithm 29, line 8). -/
def ballSign (s : ByteArray) (i : Nat) : Int :=
  if Fips204.bit s (i + Fips204.tau - 256) = 1 then -1 else 1

/-- The swap-and-set update of Algorithm 29 at index `i` with `j`. -/
def ballSet (s : ByteArray) (c : Fips204.Poly) (i j : Nat) : Fips204.Poly :=
  (c.set! i c[j]!).set! j (ballSign s i)

/-- One position of the bytecode's scan on the state `(c, i)`. -/
def ballStep (s : ByteArray) (st : Fips204.Poly × Nat) (p : Nat) : Fips204.Poly × Nat :=
  if st.2 < 256 ∧ s[p]!.toNat ≤ st.2 then (ballSet s st.1 st.2 s[p]!.toNat, st.2 + 1) else st

/-- The scan state after positions `8, …, 8 + k - 1`. -/
def ballFold (s : ByteArray) (k : Nat) : Fips204.Poly × Nat :=
  (List.range' 8 k).foldl (ballStep s) (Fips204.zeroPoly, 217)

theorem ballFold_zero (s : ByteArray) : ballFold s 0 = (Fips204.zeroPoly, 217) := rfl

theorem ballFold_succ (s : ByteArray) (k : Nat) :
    ballFold s (k + 1) = ballStep s (ballFold s k) (8 + k) := by
  simp [ballFold, List.range'_concat, List.foldl_append]

/-- The spec loop with its early return, as a recursion over the indices. -/
def specRun (s : ByteArray) : List Nat → Fips204.Poly → Nat → Option Fips204.Poly
  | [], c, _ => some c
  | i :: l, c, pos =>
    match Fips204.sampleIndex s i pos with
    | none => none
    | some p => specRun s l (ballSet s c i s[p]!.toNat) (p + 1)

theorem sampleInBallOf_specRun (s : ByteArray) :
    Fips204.sampleInBallOf s = specRun s (List.range' 217 39) Fips204.zeroPoly 8 := by
  unfold Fips204.sampleInBallOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' (256 - Fips204.tau) [256 - Fips204.tau:256].size = List.range' 217 39 := rfl
  rw [hr]
  generalize List.range' 217 39 = l
  generalize Fips204.zeroPoly = c
  generalize (8 : Nat) = pos
  induction l generalizing c pos with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons]
    simp only [specRun]
    cases Fips204.sampleIndex s i pos with
    | none => rfl
    | some p => exact ih _ _

theorem sampleIndex_none (s : ByteArray) (i : Nat) : ∀ pos,
    Fips204.sampleIndex s i pos = none → ∀ p, pos ≤ p → p < 272 → i < s[p]!.toNat := by
  intro pos
  induction h : 272 - pos generalizing pos with
  | zero => intro _ p h1 h2; omega
  | succ n ih =>
    intro hn p h1 h2
    rw [Fips204.sampleIndex] at hn
    have hpos : pos < Fips204.sampleInBallLimit := by
      simp only [Fips204.sampleInBallLimit]; omega
    rw [if_pos hpos] at hn
    split at hn
    · exact absurd hn (by simp)
    · rename_i hle
      by_cases hp : p = pos
      · subst hp; omega
      · exact ih (pos + 1) (by omega) hn p (by omega) h2

theorem sampleIndex_some (s : ByteArray) (i : Nat) : ∀ pos p,
    Fips204.sampleIndex s i pos = some p →
      pos ≤ p ∧ p < 272 ∧ s[p]!.toNat ≤ i ∧ ∀ p', pos ≤ p' → p' < p → i < s[p']!.toNat := by
  intro pos
  induction h : 272 - pos generalizing pos with
  | zero =>
    intro p hp
    rw [Fips204.sampleIndex, if_neg (by simp only [Fips204.sampleInBallLimit]; omega)] at hp
    exact absurd hp (by simp)
  | succ n ih =>
    intro p hp
    rw [Fips204.sampleIndex] at hp
    have hpos : pos < Fips204.sampleInBallLimit := by
      simp only [Fips204.sampleInBallLimit]; omega
    rw [if_pos hpos] at hp
    split at hp
    · rename_i hle
      simp only [Option.some.injEq] at hp
      subst hp
      refine ⟨(Nat.le_refl _), by simpa [Fips204.sampleInBallLimit] using hpos, hle, fun p' h1 h2 => ?_⟩
      omega
    · rename_i hle
      obtain ⟨h1, h2, h3, h4⟩ := ih (pos + 1) (by omega) p hp
      refine ⟨by omega, h2, h3, fun p' h5 h6 => ?_⟩
      by_cases hp' : p' = pos
      · subst hp'; omega
      · exact h4 p' (by omega) h6

theorem foldl_ballStep_done (s : ByteArray) (c : Fips204.Poly) (i : Nat) (hi : 256 ≤ i) :
    ∀ l : List Nat, l.foldl (ballStep s) (c, i) = (c, i)
  | [] => rfl
  | p :: l => by
    rw [List.foldl_cons]
    have : ballStep s (c, i) p = (c, i) := by
      unfold ballStep; rw [if_neg (by simp only; omega)]
    rw [this]; exact foldl_ballStep_done s c i hi l

theorem foldl_ballStep_skip (s : ByteArray) (c : Fips204.Poly) (i : Nat) :
    ∀ l : List Nat, (∀ p ∈ l, i < s[p]!.toNat) → l.foldl (ballStep s) (c, i) = (c, i)
  | [] => fun _ => rfl
  | p :: l => fun h => by
    rw [List.foldl_cons]
    have : ballStep s (c, i) p = (c, i) := by
      unfold ballStep; rw [if_neg (by simp only; have := h p (by simp); omega)]
    rw [this]; exact foldl_ballStep_skip s c i l (fun p' hp' => h p' (by simp [hp']))

theorem specRun_scan (s : ByteArray) : ∀ n i (c : Fips204.Poly) pos, n = 256 - i → i ≤ 256 →
    specRun s (List.range' i n) c pos =
      (let r := (List.range' pos (272 - pos)).foldl (ballStep s) (c, i)
       if r.2 < 256 then none else some r.1)
  | 0, i, c, pos, hn, hi => by
    have : i = 256 := by omega
    subst this
    simp only [List.range'_zero, specRun, foldl_ballStep_done s c 256 (Nat.le_refl _)]
    simp
  | n + 1, i, c, pos, hn, hi => by
    rw [List.range'_succ]
    simp only [specRun]
    cases hsi : Fips204.sampleIndex s i pos with
    | none =>
      have hall := sampleIndex_none s i pos hsi
      simp only
      rw [foldl_ballStep_skip s c i _ (fun p hp => by
        rw [List.mem_range'_1] at hp; exact hall p (by omega) (by omega))]
      simp only [show i < 256 by omega, ↓reduceIte]
    | some p =>
      obtain ⟨h1, h2, h3, h4⟩ := sampleIndex_some s i pos p hsi
      simp only
      rw [specRun_scan s n (i + 1) _ (p + 1) (by omega) (by omega)]
      have hsplit : List.range' pos (272 - pos) =
          List.range' pos (p - pos) ++ p :: List.range' (p + 1) (272 - (p + 1)) := by
        have := @List.range'_append pos (p - pos) (272 - p) 1
        rw [show pos + 1 * (p - pos) = p by omega,
          show p - pos + (272 - p) = 272 - pos by omega] at this
        rw [← this, show 272 - p = (272 - (p + 1)) + 1 by omega, List.range'_succ]
      rw [hsplit, List.foldl_append, foldl_ballStep_skip s c i _ (fun p' hp' => by
        rw [List.mem_range'_1] at hp'; exact h4 p' (by omega) (by omega)), List.foldl_cons]
      have : ballStep s (c, i) p = (ballSet s c i s[p]!.toNat, i + 1) := by
        unfold ballStep; rw [if_pos ⟨by simp only; omega, h3⟩]
      rw [this]

theorem sampleInBallOf_eq (s : ByteArray) : Fips204.sampleInBallOf s =
    if (ballFold s 264).2 < 256 then none else some (ballFold s 264).1 := by
  rw [sampleInBallOf_specRun, specRun_scan s 39 217 _ 8 rfl (by omega)]
  rfl

/-- Invariants of the scan: size, index range, coefficients in `{-1, 0, 1}`. -/
theorem ballFold_inv (s : ByteArray) : ∀ k,
    (ballFold s k).1.size = 256 ∧ 217 ≤ (ballFold s k).2 ∧ (ballFold s k).2 ≤ 256 ∧
      ∀ x, x < 256 → (ballFold s k).1[x]! = 0 ∨ (ballFold s k).1[x]! = 1 ∨
        (ballFold s k).1[x]! = -1
  | 0 => by
    refine ⟨by simp [ballFold_zero, Fips204.zeroPoly], by simp [ballFold_zero],
      by simp [ballFold_zero], fun x hx => ?_⟩
    simp [ballFold_zero, Fips204.zeroPoly, hx]
  | k + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := ballFold_inv s k
    rw [ballFold_succ]
    unfold ballStep
    split
    · rename_i h
      refine ⟨by simp only [ballSet]; rw [size_set!, size_set!, h1], by simp only; omega,
        by simp only; omega, fun x hx => ?_⟩
      simp only [ballSet]
      rw [getElem!_set!, getElem!_set!]
      split
      · unfold ballSign; split <;> simp
      · split
        · exact h4 _ (by omega)
        · exact h4 x hx
    · exact ⟨h1, h2, h3, h4⟩

end MlDsa44.Proofs.Sampling
