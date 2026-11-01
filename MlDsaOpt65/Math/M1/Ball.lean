import MlDsa.Bridge44
import MlDsaOpt44.Math.Facts
/-!
# SampleInBall for any parameter set (work package M1)

`MlDsa44.Proofs.Sampling` (`Ball.lean`) and `MlDsaOpt44.Proofs.Facts` with
`τ` a parameter: the spec loop over `i ∈ [256 − τ, 256)` is the scan
`ballFold` over the byte positions `8 … 271`, whose invariants give the shape
of the output (256 coefficients in `{−1, 0, 1}`, at most `τ` nonzero).
Shared by the ML-DSA-65 and ML-DSA-87 proofs.
-/

namespace MlDsaOptM1

open MlDsa

/-- The sign written for index `i` (Algorithm 29, line 8). -/
def ballSign (P : Params) (s : ByteArray) (i : Nat) : Int :=
  if Fips204.bit s (i + P.tau - 256) = 1 then -1 else 1

/-- The swap-and-set update of Algorithm 29 at index `i` with `j`. -/
def ballSet (P : Params) (s : ByteArray) (c : Fips204.Poly) (i j : Nat) : Fips204.Poly :=
  (c.set! i c[j]!).set! j (ballSign P s i)

/-- One position of the scan on the state `(c, i)`. -/
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
def specRun (P : Params) (s : ByteArray) : List Nat → Fips204.Poly → Nat → Option Fips204.Poly
  | [], c, _ => some c
  | i :: l, c, pos =>
    match Fips204.sampleIndex s i pos with
    | none => none
    | some p => specRun P s l (ballSet P s c i s[p]!.toNat) (p + 1)

theorem sampleInBallOf_specRun (P : Params) (s : ByteArray) (hτ : P.tau ≤ 256) :
    Fips204.sampleInBallOf P s =
      specRun P s (List.range' (256 - P.tau) P.tau) Fips204.zeroPoly 8 := by
  unfold Fips204.sampleInBallOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' (256 - P.tau) [256 - P.tau:256].size = List.range' (256 - P.tau) P.tau := by
    congr 1; simp; omega
  rw [hr]
  generalize List.range' (256 - P.tau) P.tau = l
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

theorem sampleIndex_none (s : ByteArray) (i pos : Nat) (h : Fips204.sampleIndex s i pos = none) :
    ∀ p, pos ≤ p → p < 272 → i < s[p]!.toNat := by
  rw [Bridge44.sampleIndex_eq] at h
  exact MlDsa44.Proofs.Sampling.sampleIndex_none s i pos h

theorem sampleIndex_some (s : ByteArray) (i pos p : Nat) (h : Fips204.sampleIndex s i pos = some p) :
    pos ≤ p ∧ p < 272 ∧ s[p]!.toNat ≤ i ∧ ∀ p', pos ≤ p' → p' < p → i < s[p']!.toNat := by
  rw [Bridge44.sampleIndex_eq] at h
  exact MlDsa44.Proofs.Sampling.sampleIndex_some s i pos p h

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

theorem sampleInBallOf_eq (P : Params) (s : ByteArray) (hτ : P.tau ≤ 256) :
    Fips204.sampleInBallOf P s =
      if (ballFold P s 264).2 < 256 then none else some (ballFold P s 264).1 := by
  rw [sampleInBallOf_specRun P s hτ, specRun_scan P s P.tau (256 - P.tau) _ 8 (by omega) (by omega)]
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
      refine ⟨by simp only [ballSet]; rw [Array.size_set!, Array.size_set!, h1],
        by simp only; omega, by simp only; omega, fun x hx => ?_⟩
      simp only [ballSet]
      rw [MlDsa44.Proofs.Sampling.getElem!_set!, MlDsa44.Proofs.Sampling.getElem!_set!]
      split
      · unfold ballSign; split <;> simp
      · split
        · exact h4 _ (by omega)
        · exact h4 x hx
    · exact ⟨h1, h2, h3, h4⟩

open MlDsaOpt44.Proofs.Facts in
theorem ballFold_cnt (P : Params) (s : ByteArray) : ∀ k,
    (∀ p, (ballFold P s k).2 ≤ p → p < 256 → (ballFold P s k).1[p]! = 0) ∧
      cnt (ballFold P s k).1 256 + (256 - P.tau) ≤ (ballFold P s k).2
  | 0 => by
    rw [ballFold_zero]
    refine ⟨fun p _ hp => ?_, ?_⟩
    · simp [Fips204.zeroPoly, hp]
    · have : ∀ n, n ≤ 256 → cnt (Array.replicate 256 (0 : Int)) n = 0 := by
        intro n hn
        induction n with
        | zero => rfl
        | succ n ih => simp [cnt, ih (by omega), show n < 256 by omega]
      show cnt (Array.replicate 256 (0 : Int)) 256 + (256 - P.tau) ≤ 256 - P.tau
      rw [this 256 (Nat.le_refl _)]; omega
  | k + 1 => by
    obtain ⟨hz, hc⟩ := ballFold_cnt P s k
    obtain ⟨hsz, -, -, -⟩ := ballFold_inv P s k
    rw [ballFold_succ]
    generalize ballFold P s k = st at hz hc hsz
    obtain ⟨c, i⟩ := st
    simp only at hz hc hsz
    unfold ballStep
    split
    · rename_i h
      simp only at h ⊢
      obtain ⟨hi, hj⟩ := h
      generalize (8 + k : Nat) = p at hj
      generalize hjv : s[p]!.toNat = j at hj
      have hci : c[i]! = 0 := hz i (Nat.le_refl _) hi
      unfold ballSet
      have e1 := cnt_set c i c[j]! (by omega) 256
      have e2 := cnt_set (c.set! i c[j]!) j (ballSign P s i) (by simp [hsz]; omega) 256
      have hc1j : (c.set! i c[j]!)[j]! = c[j]! := by
        rw [MlDsa44.Proofs.Sampling.getElem!_set!]; split
        · rename_i h; rw [h.1]
        · rfl
      rw [hc1j] at e2
      simp only [show i < 256 from hi, show j < 256 by omega, hci, ↓reduceIte,
        Nat.add_zero] at e1 e2
      refine ⟨fun p' hp1 hp2 => ?_, ?_⟩
      · rw [MlDsa44.Proofs.Sampling.getElem!_set!, if_neg (by omega),
          MlDsa44.Proofs.Sampling.getElem!_set!, if_neg (by omega)]
        exact hz p' (by omega) hp2
      · have b1 : (if ballSign P s i = 0 then 0 else 1) ≤ 1 := by split <;> omega
        omega
    · exact ⟨hz, hc⟩

/-- SampleInBall's output: 256 coefficients in `{−1, 0, 1}`, at most `τ` nonzero. -/
theorem sampleInBallOf_inv (P : Params) (hτ : P.tau ≤ 256) {s : ByteArray} {c : Fips204.Poly}
    (h : Fips204.sampleInBallOf P s = some c) :
    c.size = 256 ∧ (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) ∧
      MlDsaOpt44.Proofs.Facts.cnt c 256 ≤ P.tau := by
  rw [sampleInBallOf_eq P s hτ] at h
  have hinv := ballFold_inv P s 264
  have hcnt := (ballFold_cnt P s 264).2
  generalize ballFold P s 264 = st at h hinv hcnt
  obtain ⟨c', i⟩ := st
  simp only at h hinv hcnt
  by_cases hb : i < 256
  · rw [if_pos hb] at h; exact absurd h (by simp)
  · rw [if_neg hb] at h
    have e := Option.some.inj h
    subst e
    obtain ⟨h1, -, h3, h4⟩ := hinv
    exact ⟨h1, h4, by omega⟩

end MlDsaOptM1
