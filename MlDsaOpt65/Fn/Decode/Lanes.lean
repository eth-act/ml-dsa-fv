import MlDsaOpt44.Fn.Decode.Lanes
import MlDsaOpt65.Layout
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Lane arithmetic of the `dz` gather step (ML-DSA-65, WP G2)

The 20-bit twin of `MlDsaOpt44/Fn/Decode/Lanes.lean`: one gather step builds
`W = gW gs V0 V1 V2 V3` (60 bits of each little-endian window `V_k` from bit `gs` in
lane `k`), extracts three raw words `zR (W >> 20 kk)`, stores `zv R = K − R`
(`K = γ1 + 9q`, v4) and ORs the flag word `zf R` into the accumulator.
-/

namespace MlDsaOpt65.Proofs.DecodeZ

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- The gathered word: 60 bits of `V_k` from bit `gs` in lane `k`. -/
def gW (gs V0 V1 V2 V3 : Nat) : Nat :=
  (1152921504606846975 &&& V3 / 2 ^ gs) * 6277101735386680763835789423207666416102355444464034512896 |||
    ((1152921504606846975 &&& V2 / 2 ^ gs) * 340282366920938463463374607431768211456 |||
      ((1152921504606846975 &&& V1 / 2 ^ gs) * 18446744073709551616 ||| 1152921504606846975 &&& V0 / 2 ^ gs))

theorem gW_eq (gs V0 V1 V2 V3 : Nat) :
    (1152921504606846975 &&& V3 / 2 ^ gs) * 6277101735386680763835789423207666416102355444464034512896 |||
      ((1152921504606846975 &&& V2 / 2 ^ gs) * 340282366920938463463374607431768211456 |||
        ((1152921504606846975 &&& V1 / 2 ^ gs) * 18446744073709551616 ||| 1152921504606846975 &&& V0 / 2 ^ gs)) =
    gW gs V0 V1 V2 V3 := rfl

/-- Raw word: the low 20 bits of every lane. -/
def zR (x : Nat) : Nat := 6582011952183088782295924477334101861609978183833731334774194175 &&& x

theorem zR_eq (x : Nat) :
    6582011952183088782295924477334101861609978183833731334774194175 &&& x = zR x := rfl

/-- Stored word `K − R`, `K = γ1 + 9q` in every lane (v4: the forward NTT's bias `8q` is
added here). -/
def zv (R : Nat) : Nat := 476733579960318781531555631535630678667459122251541153085296926729 - R

/-- Flag word (v4, one multiply): `C + (2^32 − 1) R`, lane `(r + β) 2^32 + (2^27 + β − r)`
(no borrow, no carry across lanes). Bit `27` of a lane is set iff `raw ≤ β = 196`, bit `52`
iff `raw ≥ 2γ1 − β`. -/
def zf (R : Nat) : Nat :=
  5284992046325185797670607723898850609056285312075943487823019889393860 + 4294967295 * R

theorem zf_eq (R : Nat) :
    5284992046325185797670607723898850609056285312075943487823019889393860 + 4294967295 * R = zf R := rfl

theorem zsub (x : Nat) :
    UInt256.ofNat 476733579960318781531555631535630678667459122251541153085296926729 -
      UInt256.ofNat (zR x) = UInt256.ofNat (zv (zR x)) := by
  have h : zR x ≤ 6582011952183088782295924477334101861609978183833731334774194175 := Nat.and_le_left
  exact ofNat_sub (by omega) (by norm_num)

theorem zv_mod (R : Nat) :
    zv R % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = zv R :=
  Nat.mod_eq_of_lt (by unfold zv; omega)

theorem gW_mod (gs V0 V1 V2 V3 : Nat) :
    gW gs V0 V1 V2 V3 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      gW gs V0 V1 V2 V3 := by
  have hb : ∀ y c, c ≤ 192 → (1152921504606846975 &&& y) * 2 ^ c < 2 ^ 256 := fun y c hc =>
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ Nat.and_le_left)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hc)) (by norm_num))
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow (hb _ 192 le_rfl) (Nat.or_lt_two_pow (hb _ 128 (by omega))
    (Nat.or_lt_two_pow (hb _ 64 (by omega)) (by simpa using hb (V0 / 2 ^ gs) 0 (by omega))))

end MlDsaOpt65.Proofs.DecodeZ
