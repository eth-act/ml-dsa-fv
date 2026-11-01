import MlDsaOpt44.Layout
import MlDsaOpt44.Math.Facts
import Mathlib.Tactic.LinearCombination
/-!
# The sparse product identity behind `csum`

For `c ∈ {−1, 0, 1}^256` and `t1_r` with 10-bit coefficients, the window sum
`S'_r(t)` and the count `n_neg(t)` satisfy
`2^13 S'_r(t) + n_neg(t) − 2^13 (c · t1_r)(t) = q · n_neg(t)`
because `2^13 · 1023 + 1 = q`; every nonzero coefficient contributes at most
`1023` to `S'`, and SampleInBall has at most `39` of them.
-/

namespace MlDsaOpt44.Proofs.CsumMath

open MlDsa44

theorem t1v_lt (cd : ByteArray) (r i : Nat) : t1v cd r i < 1024 :=
  Proofs.Decode.bitsToInteger_lt _ _ 10

theorem t1Of_get (cd : ByteArray) {r i : Nat} (hr : r < 4) (hi : i < 256) :
    (t1Of cd r)[i]! = (t1v cd r i : Int) := by
  have hw : Fips204.bitlen (Fips204.q - 1) - Fips204.d = 10 := by decide
  have hc : Fips204.bitlen (2 ^ 10 - 1) = 10 := by decide
  unfold t1Of pkOf Fips204.pkDecode
  simp only [hw]
  rw [show Fips204.k = 4 from rfl, Proofs.Math.getElem!_map_range 4 r _ hr]
  unfold Fips204.simpleBitUnpack
  simp only [hc]
  rw [Proofs.Math.getElem!_map_range 256 i _ hi, ByteArray.extract_extract, Nat.mul_comm i 10]
  unfold t1v
  congr 3 <;> omega

theorem sum_succ_int (g : Nat → Int) (n : Nat) :
    ((List.range (n + 1)).map g).sum = ((List.range n).map g).sum + g n := by
  simp [List.range_succ]

theorem sum_succ_nat (g : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map g).sum = ((List.range n).map g).sum + g n := by
  simp [List.range_succ]

theorem filter_length (P : Nat → Bool) : ∀ n,
    ((List.range n).filter P).length = ((List.range n).map fun p => if P p then 1 else 0).sum
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_length P n,
      List.map_append, List.sum_append]
    by_cases h : P n <;> simp [h]

/-- The window table entry (same body as `tEntry` in `Fn/Ct.lean`). -/
def tE (cd : ByteArray) (r e : Nat) : Nat :=
  if 256 ≤ e ∧ e < 512 then t1v cd r (e - 256) else 1023 - t1v cd r (e % 256)

section
variable (c : Fips204.Poly) (cd : ByteArray) (r t : Nat)

/-- Contribution of position `p` to `S'_r(t)`. -/
def sp (p : Nat) : Nat :=
  if c[p]! = 0 then 0 else tE cd r (t + 256 - p + if c[p]! = -1 then 256 else 0)

/-- Contribution of position `p` to `n_neg(t)`. -/
def np (p : Nat) : Nat := if (p ≤ t ∧ c[p]! = -1) ∨ (t < p ∧ c[p]! = 1) then 1 else 0

/-- Contribution of position `p` to `(c · t1_r)(t)`. -/
def ng (p : Nat) : Int :=
  if p ≤ t then c[p]! * (t1Of cd r)[t - p]! else -(c[p]! * (t1Of cd r)[t + 256 - p]!)

end

theorem tEntry_pos (cd : ByteArray) (r : Nat) {e : Nat} (h1 : 256 ≤ e) (h2 : e < 512) :
    tE cd r e = t1v cd r (e - 256) := by
  unfold tE; rw [if_pos ⟨h1, h2⟩]

theorem tEntry_neg (cd : ByteArray) (r : Nat) {e : Nat} (h : ¬ (256 ≤ e ∧ e < 512)) :
    tE cd r e = 1023 - t1v cd r (e % 256) := by
  unfold tE; rw [if_neg h]

theorem term {c : Fips204.Poly} (cd : ByteArray) {r t p : Nat} (hr : r < 4) (ht : t < 256)
    (hp : p < 256) (hcp : c[p]! = 0 ∨ c[p]! = 1 ∨ c[p]! = -1) :
    ((2 ^ 13 * sp c cd r t p + np c t p : Nat) : Int) - 2 ^ 13 * ng c cd r t p =
      (Fips204.q : Int) * (np c t p : Nat) := by
  have hq : ((Fips204.q : Nat) : Int) = 8380417 := rfl
  rw [hq]
  rcases hcp with h | h | h
  · have hs : sp c cd r t p = 0 := by unfold sp; rw [if_pos h]
    have hn : np c t p = 0 := by
      unfold np; rw [if_neg]; rw [h]; omega
    have hg : ng c cd r t p = 0 := by unfold ng; rw [h]; split <;> simp
    rw [hs, hn, hg]; simp
  · by_cases hpt : p ≤ t
    · have hs : sp c cd r t p = t1v cd r (t - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_neg (by decide), Nat.add_zero,
          tEntry_pos cd r (by omega) (by omega)]
        rw [show t + 256 - p - 256 = t - p by omega]
      have hn : np c t p = 0 := by unfold np; rw [h, if_neg]; omega
      have hg : ng c cd r t p = t1v cd r (t - p) := by
        unfold ng; rw [if_pos hpt, h, t1Of_get cd hr (by omega), one_mul]
      rw [hs, hn, hg]; push_cast; ring
    · have hx := t1v_lt cd r (t + 256 - p)
      have hs : sp c cd r t p = 1023 - t1v cd r (t + 256 - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_neg (by decide), Nat.add_zero, tEntry_neg cd r (by omega)]
        congr 2; omega
      have hn : np c t p = 1 := by unfold np; rw [h, if_pos]; omega
      have hg : ng c cd r t p = -(t1v cd r (t + 256 - p) : Int) := by
        unfold ng; rw [if_neg hpt, h, t1Of_get cd hr (by omega), one_mul]
      rw [hs, hn, hg]; push_cast [Nat.cast_sub (show t1v cd r (t + 256 - p) ≤ 1023 by omega)]; ring
  · by_cases hpt : p ≤ t
    · have hx := t1v_lt cd r (t - p)
      have hs : sp c cd r t p = 1023 - t1v cd r (t - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_pos rfl, tEntry_neg cd r (by omega)]
        congr 2; omega
      have hn : np c t p = 1 := by unfold np; rw [h, if_pos]; omega
      have hg : ng c cd r t p = -(t1v cd r (t - p) : Int) := by
        unfold ng; rw [if_pos hpt, h, t1Of_get cd hr (by omega), neg_one_mul]
      rw [hs, hn, hg]; push_cast [Nat.cast_sub (show t1v cd r (t - p) ≤ 1023 by omega)]; ring
    · have hs : sp c cd r t p = t1v cd r (t + 256 - p) := by
        unfold sp
        rw [h, if_neg (by decide), if_pos rfl, tEntry_pos cd r (by omega) (by omega)]
        rw [show t + 256 - p + 256 - 256 = t + 256 - p by omega]
      have hn : np c t p = 0 := by unfold np; rw [h, if_neg]; omega
      have hg : ng c cd r t p = t1v cd r (t + 256 - p) := by
        unfold ng; rw [if_neg hpt, h, t1Of_get cd hr (by omega), neg_one_mul, neg_neg]
      rw [hs, hn, hg]; push_cast; ring

theorem sums {c : Fips204.Poly} (cd : ByteArray) {r t : Nat} (hr : r < 4) (ht : t < 256)
    (hc : ∀ p, p < 256 → c[p]! = 0 ∨ c[p]! = 1 ∨ c[p]! = -1) : ∀ n, n ≤ 256 →
    ((2 ^ 13 * ((List.range n).map (sp c cd r t)).sum + ((List.range n).map (np c t)).sum : Nat) : Int) -
      2 ^ 13 * ((List.range n).map (ng c cd r t)).sum =
      (Fips204.q : Int) * (((List.range n).map (np c t)).sum : Nat)
  | 0, _ => by simp
  | n + 1, hn => by
    have ih := sums cd hr ht hc n (by omega)
    have hterm := term cd hr ht (show n < 256 by omega) (hc n (by omega))
    rw [sum_succ_nat, sum_succ_nat, sum_succ_int]
    push_cast at ih hterm ⊢
    linear_combination ih + hterm

theorem tEntry_le (cd : ByteArray) (r e : Nat) : tE cd r e ≤ 1023 := by
  unfold tE
  split
  · have := t1v_lt cd r (e - 256); omega
  · omega

theorem sp_le {c : Fips204.Poly} (cd : ByteArray) (r t : Nat) : ∀ n,
    ((List.range n).map (sp c cd r t)).sum ≤ 1023 * Facts.cnt c n
  | 0 => by simp
  | n + 1 => by
    rw [sum_succ_nat]
    have ih := sp_le (c := c) cd r t n
    have : sp c cd r t n ≤ 1023 * (if c[n]! = 0 then 0 else 1) := by
      unfold sp
      split
      · simp
      · exact tEntry_le cd r _
    simp only [Facts.cnt]
    omega

theorem np_le (c : Fips204.Poly) (t : Nat) : ∀ n,
    ((List.range n).map (np c t)).sum ≤ Facts.cnt c n
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
    simp only [Facts.cnt]
    omega

end MlDsaOpt44.Proofs.CsumMath
