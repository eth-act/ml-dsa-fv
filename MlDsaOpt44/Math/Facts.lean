import MlDsa44.Proofs.Math.Sampling.Ball
import MlDsa44.Proofs.Math.Decode.Hint
import MlDsa44.Proofs.Math.Decode.Z
import MlDsa44.Proofs.Math.Sponge
import MlDsa44.Proofs.Math.Verify
/-!
# Spec-level facts about FIPS 202/204 building blocks

SHAKE output sizes, the shape of SampleInBall's output (coefficients in
`{−1, 0, 1}`, at most `τ = 39` nonzero), RejNTTPoly's range, decoded hints
are bits, and `UseHint`'s dependence on `r mod q` and range.
-/

namespace MlDsaOpt44.Proofs.Facts

open MlDsa44

theorem shake_size (rate : Nat) (msg : ByteArray) (n : Nat) (hrate : rate = 136 ∨ rate = 168) :
    (Fips202.shake rate msg n).size = n := by
  unfold Fips202.shake
  rw [ByteArray.size_extract, Proofs.Math.squeeze_size_of_rate _ _ _ hrate]
  rcases hrate with rfl | rfl <;> omega

theorem H_size (s : ByteArray) (n : Nat) : (Fips204.H s n).size = n :=
  shake_size 136 s n (Or.inl rfl)

/-! ## SampleInBall -/

/-- Number of nonzero coefficients below `n`. -/
def cnt (c : Fips204.Poly) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt c n + if c[n]! = 0 then 0 else 1

theorem cnt_set (c : Fips204.Poly) (k : Nat) (v : Int) (hk : k < c.size) : ∀ n,
    cnt (c.set! k v) n + (if k < n then (if c[k]! = 0 then 0 else 1) else 0) =
      cnt c n + (if k < n then (if v = 0 then 0 else 1) else 0)
  | 0 => by simp [cnt]
  | n + 1 => by
    have ih := cnt_set c k v hk n
    simp only [cnt, Proofs.Sampling.getElem!_set!]
    by_cases h1 : k < n
    · have h2 : ¬ (n = k ∧ k < c.size) := fun h => by omega
      simp only [h1, h2, if_true, if_false, show k < n + 1 by omega] at ih ⊢
      omega
    · by_cases h3 : n = k
      · subst h3
        simp only [h1, if_false, Nat.lt_succ_self, and_self, hk, if_true] at ih ⊢
        omega
      · have h2 : ¬ (n = k ∧ k < c.size) := fun h => h3 h.1
        simp only [h1, h2, if_false, show ¬ k < n + 1 by omega] at ih ⊢
        omega

theorem ballFold_cnt (s : ByteArray) : ∀ k,
    (∀ p, (Proofs.Sampling.ballFold s k).2 ≤ p → p < 256 → (Proofs.Sampling.ballFold s k).1[p]! = 0) ∧
      cnt (Proofs.Sampling.ballFold s k).1 256 + 217 ≤ (Proofs.Sampling.ballFold s k).2
  | 0 => by
    rw [Proofs.Sampling.ballFold_zero]
    refine ⟨fun p _ hp => ?_, ?_⟩
    · simp [Fips204.zeroPoly, hp]
    · have : ∀ n, n ≤ 256 → cnt (Array.replicate 256 (0 : Int)) n = 0 := by
        intro n hn
        induction n with
        | zero => rfl
        | succ n ih => simp [cnt, ih (by omega), show n < 256 by omega]
      show cnt (Array.replicate 256 (0 : Int)) 256 + 217 ≤ 217
      rw [this 256 (Nat.le_refl _)]; omega
  | k + 1 => by
    obtain ⟨hz, hc⟩ := ballFold_cnt s k
    obtain ⟨hsz, -, -, -⟩ := Proofs.Sampling.ballFold_inv s k
    rw [Proofs.Sampling.ballFold_succ]
    generalize Proofs.Sampling.ballFold s k = st at hz hc hsz
    obtain ⟨c, i⟩ := st
    simp only at hz hc hsz
    unfold Proofs.Sampling.ballStep
    split
    · rename_i h
      simp only at h ⊢
      obtain ⟨hi, hj⟩ := h
      generalize (8 + k : Nat) = p at hj
      generalize hjv : s[p]!.toNat = j at hj
      have hci : c[i]! = 0 := hz i (Nat.le_refl _) hi
      unfold Proofs.Sampling.ballSet
      have e1 := cnt_set c i c[j]! (by omega) 256
      have hs1 : (c.set! i c[j]!).size = 256 := by simp [hsz]
      have e2 := cnt_set (c.set! i c[j]!) j (Proofs.Sampling.ballSign s i) (by omega) 256
      have hc1j : (c.set! i c[j]!)[j]! = c[j]! := by
        rw [Proofs.Sampling.getElem!_set!]; split
        · rename_i h; rw [h.1]
        · rfl
      rw [hc1j] at e2
      simp only [show i < 256 from hi, show j < 256 by omega, hci, ↓reduceIte, Nat.add_zero] at e1 e2
      refine ⟨fun p' hp1 hp2 => ?_, ?_⟩
      · rw [Proofs.Sampling.getElem!_set!, if_neg (by omega), Proofs.Sampling.getElem!_set!,
          if_neg (by omega)]
        exact hz p' (by omega) hp2
      · have b1 : (if Proofs.Sampling.ballSign s i = 0 then 0 else 1) ≤ 1 := by split <;> omega
        omega
    · exact ⟨hz, hc⟩

/-- SampleInBall's output: 256 coefficients in `{−1, 0, 1}`, at most `τ = 39` nonzero. -/
theorem sampleInBallOf_inv {s : ByteArray} {c : Fips204.Poly} (h : Fips204.sampleInBallOf s = some c) :
    c.size = 256 ∧ (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) ∧ cnt c 256 ≤ 39 := by
  rw [Proofs.Sampling.sampleInBallOf_eq] at h
  have hinv := Proofs.Sampling.ballFold_inv s 264
  have hcnt := (ballFold_cnt s 264).2
  generalize Proofs.Sampling.ballFold s 264 = st at h hinv hcnt
  obtain ⟨c', i⟩ := st
  simp only at h hinv hcnt
  by_cases hb : i < 256
  · rw [if_pos hb] at h; exact absurd h (by simp)
  · rw [if_neg hb] at h
    have e := Option.some.inj h
    subst e
    obtain ⟨h1, -, h3, h4⟩ := hinv
    exact ⟨h1, h4, by omega⟩

/-! ## RejNTTPoly -/

theorem rejNTTPoly_range (seed : ByteArray) (a : Fips204.Poly)
    (h : Fips204.rejNTTPoly seed = some a) :
    a.size = 256 ∧ ∀ t, t < 256 → (0 : Int) ≤ a[t]! ∧ a[t]! < (Fips204.q : Int) := by
  unfold Fips204.rejNTTPoly at h
  rw [Proofs.Sampling.rejNTTPolyOf_eq] at h
  have hinv := Proofs.Sampling.rejFold_inv (Fips204.G seed Fips204.rejNTTPolyLimit) 336
  generalize Proofs.Sampling.rejFold (Fips204.G seed Fips204.rejNTTPolyLimit) 336 = st at h hinv
  by_cases hb : st.2 < 256
  · rw [if_pos hb] at h; exact absurd h (by simp)
  · rw [if_neg hb] at h
    obtain ⟨h1, -, h3⟩ := hinv
    rw [← Option.some.inj h]
    exact ⟨h1, h3⟩

/-! ## HintBitUnpack -/

theorem WF_fillH (y : Nat → Nat) {i : Nat} (hi : i < 4) :
    ∀ (l : List Nat) (H : Array Fips204.Poly), Proofs.Decode.WF H →
      Proofs.Decode.WF (Proofs.Decode.fillH y i H l)
  | [], _, hH => hH
  | _ :: l, _, hH => WF_fillH y hi l _ (Proofs.Decode.WF_setH hH hi)

theorem WF_foldl (y : Nat → Nat) :
    ∀ (l : List Nat) (st : Proofs.Decode.HS), (∀ i ∈ l, i < 4) → Proofs.Decode.WF st.H →
      Proofs.Decode.WF (l.foldl (Proofs.Decode.outerStep y) st).H
  | [], _, _, hH => hH
  | i :: l, st, hl, hH => by
    rw [List.foldl_cons]
    apply WF_foldl y l _ (fun j hj => hl j (by simp [hj]))
    unfold Proofs.Decode.outerStep
    dsimp only
    split
    · exact hH
    · exact WF_fillH y (hl i (by simp)) _ _ hH

theorem hintBitUnpack_range (y : ByteArray) (h : Array Fips204.Poly)
    (hh : Fips204.hintBitUnpack y = some h) {r t : Nat} (hr : r < 4) (ht : t < 256) :
    (0 : Int) ≤ h[r]![t]! ∧ h[r]![t]! ≤ 1 := by
  rw [Proofs.Decode.hintBitUnpack_eq] at hh
  by_cases hg : Proofs.Decode.hintGood (fun j => y[j]!.toNat) = true
  · rw [if_pos hg] at hh
    have e := Option.some.inj hh
    subst e
    have hw := WF_foldl (fun j => y[j]!.toNat) [0, 1, 2, 3] Proofs.Decode.hs0
      (by simp) Proofs.Decode.WF_hs0
    unfold Proofs.Decode.outerAll
    rcases (hw.2 r hr).2 t ht with h1 | h1 <;> rw [h1] <;> decide
  · rw [if_neg hg] at hh; exact absurd hh (by simp)

/-! ## UseHint -/

theorem useHint_emod (h r : Int) :
    Fips204.useHint h (r % (Fips204.q : Int)) = Fips204.useHint h r := by
  unfold Fips204.useHint Fips204.decompose
  simp only [Int.emod_emod]

theorem decompose_fst (r : Int) : 0 ≤ (Fips204.decompose r).1 ∧ (Fips204.decompose r).1 < 44 := by
  unfold Fips204.decompose Fips204.modPm
  have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
  have hg : ((2 * Fips204.gamma2 : Nat) : Int) = 190464 := rfl
  have hg2 : (((2 * Fips204.gamma2) / 2 : Nat) : Int) = 95232 := rfl
  simp only [hq, hg, hg2]
  have h0 : 0 ≤ r % 8380417 := Int.emod_nonneg _ (by decide)
  have h1 : r % 8380417 < 8380417 := Int.emod_lt_of_pos _ (by decide)
  generalize r % 8380417 = x at h0 h1
  have h2 : 0 ≤ x % 190464 := Int.emod_nonneg _ (by decide)
  have h3 : x % 190464 < 190464 := Int.emod_lt_of_pos _ (by decide)
  have h4 : x % 190464 = x - 190464 * (x / 190464) := Int.emod_def _ _
  generalize x % 190464 = y at h2 h3 h4
  generalize x / 190464 = d at h4
  split_ifs
  · simp
  · simp only; omega
  · simp
  · simp only; omega

theorem useHint_range (h r : Int) : 0 ≤ Fips204.useHint h r ∧ Fips204.useHint h r < 44 := by
  have := decompose_fst r
  unfold Fips204.useHint
  have hm : (((Fips204.q - 1) / (2 * Fips204.gamma2) : Nat) : Int) = 44 := rfl
  simp only [hm]
  generalize Fips204.decompose r = p at this
  obtain ⟨r1, r0⟩ := p
  simp only at this ⊢
  split_ifs <;> omega

end MlDsaOpt44.Proofs.Facts
