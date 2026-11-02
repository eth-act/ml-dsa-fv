import MlDsaOpt44.Fn.Decode.ZMath
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Meaning of one v4 `dz` store (WP F, R4-3 / R4-6)

v4 stores `zv4 R = K − R` with `K = γ1 + 9q` in every lane (the forward NTT's
bias `8q` is added here) and forms the flag word with one multiply:
`zf4 R = C + (2^32 − 1) R`, lane `(r + 78) 2^32 + (2^27 + 78 − r)` (no
borrow, no carry across lanes). Bit `27` of a lane is set iff `r ≤ 78`, bit
`50` iff `r ≥ 262066`.
-/

namespace MlDsaOpt44.Proofs.DecodeZ4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.DecodeZ

/-- Stored word `K − R`, `K = γ1 + 9q` in every lane. -/
def zv4 (R : Nat) : Nat := 474265323124336972468189373290603469171128550588537205346189500425 - R

/-- Flag word (one multiply). -/
def zf4 (R : Nat) : Nat :=
  2103718338860712296951814420252711173974543160988018484972446399070286 + 4294967295 * R

theorem zf4_eq (R : Nat) :
    2103718338860712296951814420252711173974543160988018484972446399070286 + 4294967295 * R = zf4 R := rfl

theorem zsub4 (x : Nat) :
    UInt256.ofNat 474265323124336972468189373290603469171128550588537205346189500425 -
      UInt256.ofNat (zR x) = UInt256.ofNat (zv4 (zR x)) := by
  have h : zR x ≤ 1645498280219470655563407987279682868948834857825835856559341567 := Nat.and_le_left
  exact ofNat_sub (by omega) (by norm_num)

theorem zv4_mod (R : Nat) :
    zv4 R % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = zv4 R :=
  Nat.mod_eq_of_lt (by unfold zv4; omega)

/-- The flag bits checked after `dz` (`zBits` of the contract). -/
def zBits4 : Nat := pack4 fun _ => 2 ^ 50 + 2 ^ 27

theorem zv4_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zv4 (pack4 r) = pack4 (fun k => 75554825 - r k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [zv4, pack4]; omega

theorem and_bits4_eq_zero (y : Nat) :
    y &&& (2 ^ 50 + 2 ^ 27) = 0 ↔ y.testBit 50 = false ∧ y.testBit 27 = false := by
  constructor
  · intro h
    have e50 := congrArg (Nat.testBit · 50) h
    have e27 := congrArg (Nat.testBit · 27) h
    simp only [Nat.testBit_and, Nat.zero_testBit, Nat.reducePow, Nat.reduceAdd, testBit_lit, Bool.and_true] at e50 e27
    exact ⟨e50, e27⟩
  · rintro ⟨h50, h27⟩
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j = 50
    · subst hj; rw [h50, Bool.false_and]
    by_cases hj' : j = 27
    · subst hj'; rw [h27, Bool.false_and]
    have : (2 ^ 50 + 2 ^ 27 : Nat).testBit j = false := by
      rw [show (2 ^ 50 + 2 ^ 27 : Nat) = 2 ^ 50 ||| 2 ^ 27 by decide, Nat.testBit_or,
        Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [this, Bool.and_false]

/-- One lane of the flag word. -/
theorem lane_flag4 {r : Nat} (hr : r < 2 ^ 18) :
    (335141666894 + 4294967295 * r) &&& (2 ^ 50 + 2 ^ 27) = 0 ↔ 78 < r ∧ r < 262066 := by
  rw [and_bits4_eq_zero, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not, Nat.reducePow]
  have e : 335141666894 + 4294967295 * r = (r + 78) * 4294967296 + (134217806 - r) := by omega
  have e27 : (335141666894 + 4294967295 * r) / 134217728 = (r + 78) * 32 + (134217806 - r) / 134217728 := by
    rw [e]; omega
  have e50 : (335141666894 + 4294967295 * r) / 1125899906842624 = (r + 78) / 262144 := by
    rw [e]; omega
  rw [e27, e50]
  have : (134217806 - r) / 134217728 = if r ≤ 78 then 1 else 0 := by split <;> omega
  rw [this]
  have : (r + 78) / 262144 = if 262066 ≤ r then 1 else 0 := by split <;> omega
  rw [this]
  split <;> split <;> omega

theorem zf4_pack {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zf4 (pack4 r) = pack4 (fun k => 335141666894 + 4294967295 * r k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [zf4, pack4]; omega

theorem zf4_and {r : Nat → Nat} (h : ∀ k, k < 4 → r k < 2 ^ 18) :
    zf4 (pack4 r) &&& zBits4 = 0 ↔ ∀ k, k < 4 → 78 < r k ∧ r k < 262066 := by
  have hl : ∀ k, k < 4 → 335141666894 + 4294967295 * r k < 2 ^ 64 :=
    fun k hk => by have := h k hk; omega
  rw [zf4_pack h, zBits4, pack4_and hl (fun _ _ => by norm_num), pack4_eq_zero]
  exact forall_congr' fun k => imp_congr_right fun hk => lane_flag4 (h k hk)

theorem zf4_zR_lt (x : Nat) : zf4 (zR x) < 2 ^ 256 := by
  have h : zR x ≤ 1645498280219470655563407987279682868948834857825835856559341567 := Nat.and_le_left
  unfold zf4; omega

end MlDsaOpt44.Proofs.DecodeZ4
