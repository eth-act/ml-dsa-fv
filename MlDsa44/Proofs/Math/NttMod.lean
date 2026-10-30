import MlDsa44.Spec.Fips204
/-!
# Reducing the NTT input mod `q`

Algorithm 41 reduces every written value `% q`, and its first layer
(`len = 128`) reads each index exactly once before overwriting it, so the
output depends only on the residues of the input.
-/

namespace MlDsa44.Proofs.Math
open Fips204

theorem getElem!_set! (a : Array Int) (i j : Nat) (v : Int) (h : j < a.size) :
    (a.set! j v)[i]! = if i = j then v else a[i]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; simp [h]
  · simp [hij, Ne.symm hij]

/-- One Cooley–Tukey butterfly of Algorithm 41 on indices `a`, `a + len`. -/
def bf (len : Nat) (z : Int) (b : Poly) (a : Nat) : Poly :=
  (b.set! (a + len) ((b[a]! - z * b[a + len]! % q) % q)).set! a
    (((b.set! (a + len) ((b[a]! - z * b[a + len]! % q) % q))[a]! + z * b[a + len]! % q) % q)

theorem bf_size (len : Nat) (z : Int) (b : Poly) (a : Nat) : (bf len z b a).size = b.size := by
  simp [bf]

theorem bf_get (z : Int) (b : Poly) (a i : Nat) (ha : a < 128) (hb : b.size = 256) :
    (bf 128 z b a)[i]! =
      if i = a then (b[a]! + z * b[a + 128]! % q) % q
      else if i = a + 128 then (b[a]! - z * b[a + 128]! % q) % q else b[i]! := by
  unfold bf
  rw [getElem!_set! _ _ _ _ (by simp; omega), getElem!_set! _ _ _ _ (by omega),
    getElem!_set! _ _ _ _ (by omega)]
  by_cases h1 : i = a
  · subst h1; simp
  · simp [h1]

theorem emod_sub_congr {x x' y y' z : Int} (hx : x % q = x' % q) (hy : y % q = y' % q) :
    (x - z * y % q) % q = (x' - z * y' % q) % q := by
  have : z * y % q = z * y' % q := by rw [Int.mul_emod, hy, ← Int.mul_emod]
  rw [this, Int.sub_emod, hx, ← Int.sub_emod]

theorem emod_add_congr {x x' y y' z : Int} (hx : x % q = x' % q) (hy : y % q = y' % q) :
    (x + z * y % q) % q = (x' + z * y' % q) % q := by
  have : z * y % q = z * y' % q := by rw [Int.mul_emod, hy, ← Int.mul_emod]
  rw [this, Int.add_emod, hx, ← Int.add_emod]

def Inv (n : Nat) (a b : Poly) : Prop :=
  a.size = 256 ∧ b.size = 256 ∧ (∀ i : Nat, a[i]! % q = b[i]! % q) ∧
    (∀ i : Nat, i < n ∨ (128 ≤ i ∧ i < 128 + n) → a[i]! = b[i]!)

theorem inv_step (z : Int) (n : Nat) (hn : n < 128) (a b : Poly) (h : Inv n a b) :
    Inv (n + 1) (bf 128 z a n) (bf 128 z b n) := by
  obtain ⟨ha, hb, hc, he⟩ := h
  refine ⟨by rw [bf_size, ha], by rw [bf_size, hb], ?_, ?_⟩
  · intro i
    rw [bf_get z a n i hn ha, bf_get z b n i hn hb]
    by_cases h1 : i = n
    · simp only [h1, if_true, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
      exact emod_add_congr (hc n) (hc (n + 128))
    · by_cases h2 : i = n + 128
      · have h3 : ¬ (n + 128 = n) := by omega
        simp only [h2, h3, if_false, if_true, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
        exact emod_sub_congr (hc n) (hc (n + 128))
      · simp only [h1, h2, if_false]; exact hc i
  · intro i hi
    rw [bf_get z a n i hn ha, bf_get z b n i hn hb]
    by_cases h1 : i = n
    · simp only [h1, if_true]
      exact emod_add_congr (hc n) (hc (n + 128))
    · by_cases h2 : i = n + 128
      · have h3 : ¬ (n + 128 = n) := by omega
        simp only [h2, h3, if_false, if_true]
        exact emod_sub_congr (hc n) (hc (n + 128))
      · simp only [h1, h2, if_false]; exact he i (by omega)

theorem inv_fold (z : Int) (n : Nat) (hn : n ≤ 128) (a b : Poly) (h : Inv 0 a b) :
    Inv n ((List.range' 0 n).foldl (bf 128 z) a) ((List.range' 0 n).foldl (bf 128 z) b) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_append]
    simpa using inv_step z n (by omega) _ _ (ih (by omega))

theorem layer1 (z : Int) (f : Poly) (hf : f.size = 256) :
    (List.range' 0 128).foldl (bf 128 z) (f.map (· % (q : Int))) =
      (List.range' 0 128).foldl (bf 128 z) f := by
  have h0 : Inv 0 (f.map (· % (q : Int))) f := by
    refine ⟨by simp [hf], hf, fun i => ?_, fun i hi => by omega⟩
    by_cases hi : i < f.size
    · simp [getElem!_pos, hi]
    · simp [getElem!_neg, hi]
  obtain ⟨ha, hb, -, he⟩ := inv_fold z 128 (Nat.le_refl _) _ _ h0
  apply Array.ext (by rw [ha, hb])
  intro i hi1 hi2
  have := he i (by omega)
  simpa [getElem!_pos, hi1, hi2] using this

set_option maxRecDepth 100000 in
theorem ntt_map_emod (f : Poly) (hf : f.size = 256) :
    ntt (f.map (· % (q : Int))) = ntt f := by
  unfold ntt
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, Std.Legacy.Range.size, map_pure, Nat.reduceSub, Nat.reduceAdd,
    Nat.div_one, Nat.sub_zero, Nat.add_sub_cancel]
  rw [show List.range' 0 8 = 0 :: List.range' 1 7 from rfl, List.foldl_cons, List.foldl_cons]
  dsimp only
  simp only [Nat.reduceDiv, List.range'_one, List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel_left, Nat.zero_add]
  have key := layer1 (zetas 1) f hf
  unfold bf at key
  rw [key]

end MlDsa44.Proofs.Math
