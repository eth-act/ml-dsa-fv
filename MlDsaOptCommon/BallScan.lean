import MlDsa.Spec.Fips204
import MlDsa44.Proofs.Math.Sampling.Rej
set_option warningAsError true
/-!
# `sampleInBallOf P` as a scan over byte positions (any parameter set)

`MlDsa44/Proofs/Math/Sampling/Ball.lean` for the parametric `MlDsa.Fips204.sampleInBallOf P`:
the spec iterates over `i ∈ [256 − τ, 256)` and searches the next accepted
position with `sampleIndex`; the bytecode iterates over positions
`p ∈ [8, 272)` and advances `i` on acceptance. `sampleInBallOf_eq` shows both
compute the same thing: `ballFold P s 264` is the bytecode's scan.
-/

namespace MlDsaOptCommon.BallScan

open MlDsa

/-- The sign written for index `i` (Algorithm 29, line 8). -/
def ballSign (P : Params) (s : ByteArray) (i : Nat) : Int :=
  if Fips204.bit s (i + P.tau - 256) = 1 then -1 else 1

/-- The swap-and-set update of Algorithm 29 at index `i` with `j`. -/
def ballSet (P : Params) (s : ByteArray) (c : Fips204.Poly) (i j : Nat) : Fips204.Poly :=
  (c.set! i c[j]!).set! j (ballSign P s i)

/-- One position of the bytecode's scan on the state `(c, i)`. -/
def ballStep (P : Params) (s : ByteArray) (st : Fips204.Poly × Nat) (p : Nat) :
    Fips204.Poly × Nat :=
  if st.2 < 256 ∧ s[p]!.toNat ≤ st.2 then (ballSet P s st.1 st.2 s[p]!.toNat, st.2 + 1) else st

/-- The scan state after positions `8, …, 8 + k - 1`. -/
def ballFold (P : Params) (s : ByteArray) (k : Nat) : Fips204.Poly × Nat :=
  (List.range' 8 k).foldl (ballStep P s) (Fips204.zeroPoly, 256 - P.tau)

theorem ballFold_zero (P : Params) (s : ByteArray) :
    ballFold P s 0 = (Fips204.zeroPoly, 256 - P.tau) := rfl

theorem ballFold_succ (P : Params) (s : ByteArray) (k : Nat) :
    ballFold P s (k + 1) = ballStep P s (ballFold P s k) (8 + k) := by
  simp [ballFold, List.range'_concat, List.foldl_append]

/-- The spec loop with its early return, as a recursion over the indices. -/
def specRun (P : Params) (s : ByteArray) :
    List Nat → Fips204.Poly → Nat → Option Fips204.Poly
  | [], c, _ => some c
  | i :: l, c, pos =>
    match Fips204.sampleIndex s i pos with
    | none => none
    | some p => specRun P s l (ballSet P s c i s[p]!.toNat) (p + 1)

theorem sampleInBallOf_specRun (P : Params) (s : ByteArray) :
    Fips204.sampleInBallOf P s =
      specRun P s (List.range' (256 - P.tau) (256 - (256 - P.tau))) Fips204.zeroPoly 8 := by
  unfold Fips204.sampleInBallOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' (256 - P.tau) [256 - P.tau:256].size =
      List.range' (256 - P.tau) (256 - (256 - P.tau)) := by
    congr 1
    simp [Std.Legacy.Range.size]
  rw [hr]
  generalize List.range' (256 - P.tau) (256 - (256 - P.tau)) = l
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
      refine ⟨(Nat.le_refl _), by simpa [Fips204.sampleInBallLimit] using hpos, hle,
        fun p' h1 h2 => ?_⟩
      omega
    · rename_i hle
      obtain ⟨h1, h2, h3, h4⟩ := ih (pos + 1) (by omega) p hp
      refine ⟨by omega, h2, h3, fun p' h5 h6 => ?_⟩
      by_cases hp' : p' = pos
      · subst hp'; omega
      · exact h4 p' (by omega) h6

theorem foldl_ballStep_done (P : Params) (s : ByteArray) (c : Fips204.Poly) (i : Nat)
    (hi : 256 ≤ i) : ∀ l : List Nat, l.foldl (ballStep P s) (c, i) = (c, i)
  | [] => rfl
  | p :: l => by
    rw [List.foldl_cons]
    have : ballStep P s (c, i) p = (c, i) := by
      unfold ballStep; rw [if_neg (by simp only; omega)]
    rw [this]; exact foldl_ballStep_done P s c i hi l

theorem foldl_ballStep_skip (P : Params) (s : ByteArray) (c : Fips204.Poly) (i : Nat) :
    ∀ l : List Nat, (∀ p ∈ l, i < s[p]!.toNat) → l.foldl (ballStep P s) (c, i) = (c, i)
  | [] => fun _ => rfl
  | p :: l => fun h => by
    rw [List.foldl_cons]
    have : ballStep P s (c, i) p = (c, i) := by
      unfold ballStep; rw [if_neg (by simp only; have := h p (by simp); omega)]
    rw [this]; exact foldl_ballStep_skip P s c i l (fun p' hp' => h p' (by simp [hp']))

theorem specRun_scan (P : Params) (s : ByteArray) : ∀ n i (c : Fips204.Poly) pos,
    n = 256 - i → i ≤ 256 →
    specRun P s (List.range' i n) c pos =
      (let r := (List.range' pos (272 - pos)).foldl (ballStep P s) (c, i)
       if r.2 < 256 then none else some r.1)
  | 0, i, c, pos, hn, hi => by
    have : i = 256 := by omega
    subst this
    simp only [List.range'_zero, specRun, foldl_ballStep_done P s c 256 (Nat.le_refl _)]
    simp
  | n + 1, i, c, pos, hn, hi => by
    rw [List.range'_succ]
    simp only [specRun]
    cases hsi : Fips204.sampleIndex s i pos with
    | none =>
      have hall := sampleIndex_none s i pos hsi
      simp only
      rw [foldl_ballStep_skip P s c i _ (fun p hp => by
        rw [List.mem_range'_1] at hp; exact hall p (by omega) (by omega))]
      simp only [show i < 256 by omega, ↓reduceIte]
    | some p =>
      obtain ⟨h1, h2, h3, h4⟩ := sampleIndex_some s i pos p hsi
      simp only
      rw [specRun_scan P s n (i + 1) _ (p + 1) (by omega) (by omega)]
      have hsplit : List.range' pos (272 - pos) =
          List.range' pos (p - pos) ++ p :: List.range' (p + 1) (272 - (p + 1)) := by
        have := @List.range'_append pos (p - pos) (272 - p) 1
        rw [show pos + 1 * (p - pos) = p by omega,
          show p - pos + (272 - p) = 272 - pos by omega] at this
        rw [← this, show 272 - p = (272 - (p + 1)) + 1 by omega, List.range'_succ]
      rw [hsplit, List.foldl_append, foldl_ballStep_skip P s c i _ (fun p' hp' => by
        rw [List.mem_range'_1] at hp'; exact h4 p' (by omega) (by omega)), List.foldl_cons]
      have : ballStep P s (c, i) p = (ballSet P s c i s[p]!.toNat, i + 1) := by
        unfold ballStep; rw [if_pos ⟨by simp only; omega, h3⟩]
      rw [this]

theorem sampleInBallOf_eq (P : Params) (s : ByteArray) : Fips204.sampleInBallOf P s =
    if (ballFold P s 264).2 < 256 then none else some (ballFold P s 264).1 := by
  rw [sampleInBallOf_specRun, specRun_scan P s _ (256 - P.tau) _ 8 rfl (by omega)]
  rfl

/-- Invariants of the scan: size, index range, coefficients in `{-1, 0, 1}`. -/
theorem ballFold_inv (P : Params) (s : ByteArray) : ∀ k,
    (ballFold P s k).1.size = 256 ∧ 256 - P.tau ≤ (ballFold P s k).2 ∧
      (ballFold P s k).2 ≤ 256 ∧
      ∀ x, x < 256 → (ballFold P s k).1[x]! = 0 ∨ (ballFold P s k).1[x]! = 1 ∨
        (ballFold P s k).1[x]! = -1
  | 0 => by
    refine ⟨by simp [ballFold_zero, Fips204.zeroPoly], by simp [ballFold_zero],
      by simp [ballFold_zero], fun x hx => ?_⟩
    simp [ballFold_zero, Fips204.zeroPoly, hx]
  | k + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := ballFold_inv P s k
    rw [ballFold_succ]
    unfold ballStep
    split
    · rename_i h
      refine ⟨by
          simp only [ballSet]
          rw [MlDsa44.Proofs.Sampling.size_set!, MlDsa44.Proofs.Sampling.size_set!, h1],
        by simp only; omega, by simp only; omega, fun x hx => ?_⟩
      simp only [ballSet]
      rw [MlDsa44.Proofs.Sampling.getElem!_set!, MlDsa44.Proofs.Sampling.getElem!_set!]
      split
      · unfold ballSign; split <;> simp
      · split
        · exact h4 _ (by omega)
        · exact h4 x hx
    · exact ⟨h1, h2, h3, h4⟩

/-- SampleInBall outputs 256 coefficients in `{−1, 0, 1}`. -/
theorem sampleInBallOf_coeffs (P : Params) (bs : ByteArray) (c : Fips204.Poly)
    (h : Fips204.sampleInBallOf P bs = some c) :
    c.size = 256 ∧ ∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1 := by
  rw [sampleInBallOf_eq] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, -, -, h4⟩ := ballFold_inv P bs 264
    exact ⟨h1, h4⟩

end MlDsaOptCommon.BallScan
