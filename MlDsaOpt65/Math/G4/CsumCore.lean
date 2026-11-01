import MlDsaOpt44.Math.Csum
import MlDsa.Spec.Fips204
/-!
# The sparse product identity behind `csum`, for any `t1` row (WP G4)

`MlDsaOpt44/Math/Csum.lean` with the `t1` row abstracted: for `c ∈ {−1, 0, 1}^256` with
at most 64 nonzero coefficients and a row `t1` whose coefficients are the 10-bit values
`tv i`, the window sum `S'(t)` (window table entries `tE tv e`) and `n_neg(t)` satisfy
`2^13 S'(t) + n_neg(t) − 2^13 (c · t1)(t) = q · n_neg(t)` (`2^13 · 1023 + 1 = q`), and
`2^13 S'(t) + n_neg(t) ≤ q · 64 < 2^29`. Shared by the ML-DSA-65 and ML-DSA-87 proofs.
-/

namespace MlDsaOptG4

open MlDsa
open MlDsaOpt44.Proofs.CsumMath (sum_succ_nat sum_succ_int)

theorem bitsToInteger_lt (v : ByteArray) (s : Nat) : ∀ c, Fips204.bitsToInteger v s c < 2 ^ c
  | 0 => by simp [Fips204.bitsToInteger]
  | c + 1 => by
    have ih := bitsToInteger_lt v s c
    unfold Fips204.bitsToInteger at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    have hb : Fips204.bit v (s + c) ≤ 1 := by
      unfold Fips204.bit
      have := Nat.mod_lt (v[(s + c) / 8]!.toNat / 2 ^ ((s + c) % 8)) (by decide : 0 < 2)
      omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ]
    have : Fips204.bit v (s + c) * 2 ^ c ≤ 2 ^ c := by
      calc _ ≤ 1 * 2 ^ c := Nat.mul_le_mul_right _ hb
        _ = 2 ^ c := Nat.one_mul _
    omega

/-- The window table entry of a row with values `tv`. -/
def tE (tv : Nat → Nat) (e : Nat) : Nat :=
  if 256 ≤ e ∧ e < 512 then tv (e - 256) else 1023 - tv (e % 256)

section
variable (c : Fips204.Poly) (tv : Nat → Nat) (t1 : Fips204.Poly) (t : Nat)

/-- Contribution of position `p` to `S'(t)`. -/
def sp (p : Nat) : Nat :=
  if c[p]! = 0 then 0 else tE tv (t + 256 - p + if c[p]! = -1 then 256 else 0)

/-- Contribution of position `p` to `n_neg(t)`. -/
def np (p : Nat) : Nat := if (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1) then 1 else 0

/-- Contribution of position `p` to `(c · t1)(t)`. -/
def ng (p : Nat) : Int :=
  if p ≤ t then c[p]! * t1[t - p]! else -(c[p]! * t1[t + 256 - p]!)

end

theorem tE_pos (tv : Nat → Nat) {e : Nat} (h1 : 256 ≤ e) (h2 : e < 512) : tE tv e = tv (e - 256) := by
  unfold tE; rw [if_pos ⟨h1, h2⟩]

theorem tE_neg (tv : Nat → Nat) {e : Nat} (h : ¬ (256 ≤ e ∧ e < 512)) : tE tv e = 1023 - tv (e % 256) := by
  unfold tE; rw [if_neg h]

theorem term {c : Fips204.Poly} {tv : Nat → Nat} {t1 : Fips204.Poly}
    (htv : ∀ i, tv i < 1024) (ht1 : ∀ i, i < 256 → t1[i]! = (tv i : Int))
    {t p : Nat} (ht : t < 256) (hp : p < 256) (hcp : c[p]! = 0 ∨ c[p]! = 1 ∨ c[p]! = -1) :
    ((2 ^ 13 * sp c tv t p + np c t p : Nat) : Int) - 2 ^ 13 * ng c t1 t p =
      (Fips204.q : Int) * (np c t p : Nat) := by
  have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
  rw [hq]
  rcases hcp with h | h | h
  · have hs : sp c tv t p = 0 := by unfold sp; rw [if_pos h]
    have hn : np c t p = 0 := by
      unfold np; rw [if_neg]; rw [h]; omega
    have hg : ng c t1 t p = 0 := by unfold ng; rw [h]; split <;> simp
    rw [hs, hn, hg]; simp
  · by_cases hpt : p ≤ t
    · have hs : sp c tv t p = tv (t - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_neg (by decide), Nat.add_zero, tE_pos tv (by omega) (by omega)]
        rw [show t + 256 - p - 256 = t - p by omega]
      have hn : np c t p = 0 := by unfold np; rw [h, if_neg]; omega
      have hg : ng c t1 t p = tv (t - p) := by
        unfold ng; rw [if_pos hpt, h, ht1 _ (by omega), one_mul]
      rw [hs, hn, hg]; push_cast; ring
    · have hx := htv (t + 256 - p)
      have hs : sp c tv t p = 1023 - tv (t + 256 - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_neg (by decide), Nat.add_zero, tE_neg tv (by omega)]
        congr 2; omega
      have hn : np c t p = 1 := by unfold np; rw [h, if_pos]; omega
      have hg : ng c t1 t p = -(tv (t + 256 - p) : Int) := by
        unfold ng; rw [if_neg hpt, h, ht1 _ (by omega), one_mul]
      rw [hs, hn, hg]; push_cast [Nat.cast_sub (show tv (t + 256 - p) ≤ 1023 by omega)]; ring
  · by_cases hpt : p ≤ t
    · have hx := htv (t - p)
      have hs : sp c tv t p = 1023 - tv (t - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_pos rfl, tE_neg tv (by omega)]
        congr 2; omega
      have hn : np c t p = 1 := by unfold np; rw [h, if_pos]; omega
      have hg : ng c t1 t p = -(tv (t - p) : Int) := by
        unfold ng; rw [if_pos hpt, h, ht1 _ (by omega), neg_one_mul]
      rw [hs, hn, hg]; push_cast [Nat.cast_sub (show tv (t - p) ≤ 1023 by omega)]; ring
    · have hs : sp c tv t p = tv (t + 256 - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_pos rfl, tE_pos tv (by omega) (by omega)]
        rw [show t + 256 - p + 256 - 256 = t + 256 - p by omega]
      have hn : np c t p = 0 := by unfold np; rw [h, if_neg]; omega
      have hg : ng c t1 t p = tv (t + 256 - p) := by
        unfold ng; rw [if_neg hpt, h, ht1 _ (by omega), neg_one_mul, neg_neg]
      rw [hs, hn, hg]; push_cast; ring

theorem sums {c : Fips204.Poly} {tv : Nat → Nat} {t1 : Fips204.Poly}
    (htv : ∀ i, tv i < 1024) (ht1 : ∀ i, i < 256 → t1[i]! = (tv i : Int))
    {t : Nat} (ht : t < 256) (hc : ∀ p, p < 256 → c[p]! = 0 ∨ c[p]! = 1 ∨ c[p]! = -1) :
    ∀ n, n ≤ 256 →
    ((2 ^ 13 * ((List.range n).map (sp c tv t)).sum + ((List.range n).map (np c t)).sum : Nat) : Int) -
      2 ^ 13 * ((List.range n).map (ng c t1 t)).sum =
      (Fips204.q : Int) * (((List.range n).map (np c t)).sum : Nat)
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := sums htv ht1 ht hc n (by omega)
    have hterm := term htv ht1 ht (show n < 256 by omega) (hc n (by omega))
    rw [sum_succ_nat, sum_succ_nat, sum_succ_int]
    push_cast at ih hterm ⊢
    linear_combination ih + hterm

theorem tE_le {tv : Nat → Nat} (htv : ∀ i, tv i < 1024) (e : Nat) : tE tv e ≤ 1023 := by
  unfold tE
  split
  · have := htv (e - 256); omega
  · omega

theorem sp_le (c : Fips204.Poly) {tv : Nat → Nat} (htv : ∀ i, tv i < 1024) (t : Nat) : ∀ n,
    ((List.range n).map (sp c tv t)).sum ≤ 1023 * MlDsaOpt44.Proofs.Facts.cnt c n
  | 0 => by simp
  | n + 1 => by
    rw [sum_succ_nat]
    have ih := sp_le c htv t n
    have : sp c tv t n ≤ 1023 * (if c[n]! = 0 then 0 else 1) := by
      unfold sp
      split
      · simp
      · exact tE_le htv _
    simp only [MlDsaOpt44.Proofs.Facts.cnt]
    omega

theorem np_le (c : Fips204.Poly) (t : Nat) : ∀ n,
    ((List.range n).map (np c t)).sum ≤ MlDsaOpt44.Proofs.Facts.cnt c n
  | 0 => by simp
  | n + 1 => by
    rw [sum_succ_nat]
    have ih := np_le c t n
    have : np c t n ≤ (if c[n]! = 0 then 0 else 1) := by
      unfold np
      split
      · rename_i h
        have : c[n]! ≠ 0 := by rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> decide
        simp [this]
      · omega
    simp only [MlDsaOpt44.Proofs.Facts.cnt]
    omega

/-- The identity for one coefficient `t`, as explicit sums. -/
theorem csum_core {c : Fips204.Poly} {tv : Nat → Nat} {t1 : Fips204.Poly}
    (hc : ∀ p, p < 256 → c[p]! = 0 ∨ c[p]! = 1 ∨ c[p]! = -1)
    (hcnt : MlDsaOpt44.Proofs.Facts.cnt c 256 ≤ 64)
    (htv : ∀ i, tv i < 1024) (ht1 : ∀ i, i < 256 → t1[i]! = (tv i : Int))
    {t : Nat} (ht : t < 256) :
    2 ^ 13 * ((List.range 256).map (sp c tv t)).sum + ((List.range 256).map (np c t)).sum < 2 ^ 29 ∧
      (((2 ^ 13 * ((List.range 256).map (sp c tv t)).sum +
          ((List.range 256).map (np c t)).sum : Nat) : Int) -
        2 ^ 13 * ((List.range 256).map (ng c t1 t)).sum) % (Fips204.q : Int) = 0 := by
  refine ⟨?_, ?_⟩
  · have h1 := sp_le c htv t 256
    have h2 := np_le c t 256
    omega
  · rw [sums htv ht1 ht hc 256 (Nat.le_refl _)]
    exact Int.mul_emod_right _ _

end MlDsaOptG4
