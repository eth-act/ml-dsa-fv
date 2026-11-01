import MlDsaOpt44.Fn.Decode.Bswap
import MlDsa44.Proofs.Math.Decode.Z
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Lane arithmetic of the `dz` gather step (WP8)

One gather step of `dz` builds `W = gW gs V0 V1 V2 V3` (54 bits of each
little-endian window `V_k` from bit `gs` in lane `k`), extracts three raw
words `zR (W >> 18 kk)`, stores `zv R = K − R` and ORs the flag word `zf R`
into the accumulator. The names below are the shapes `opt44_block` leaves;
the lemmas give their lane-wise meaning.
-/

namespace MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## Shapes -/

/-- The gathered word: 54 bits of `V_k` from bit `gs` in lane `k`. -/
def gW (gs V0 V1 V2 V3 : Nat) : Nat :=
  (18014398509481983 &&& V3 / 2 ^ gs) * 6277101735386680763835789423207666416102355444464034512896 |||
    ((18014398509481983 &&& V2 / 2 ^ gs) * 340282366920938463463374607431768211456 |||
      ((18014398509481983 &&& V1 / 2 ^ gs) * 18446744073709551616 ||| 18014398509481983 &&& V0 / 2 ^ gs))

theorem gW_eq (gs V0 V1 V2 V3 : Nat) :
    (18014398509481983 &&& V3 / 2 ^ gs) * 6277101735386680763835789423207666416102355444464034512896 |||
      ((18014398509481983 &&& V2 / 2 ^ gs) * 340282366920938463463374607431768211456 |||
        ((18014398509481983 &&& V1 / 2 ^ gs) * 18446744073709551616 ||| 18014398509481983 &&& V0 / 2 ^ gs)) =
    gW gs V0 V1 V2 V3 := rfl

/-- Raw word: the low 18 bits of every lane. -/
def zR (x : Nat) : Nat := 1645498280219470655563407987279682868948834857825835856559341567 &&& x

theorem zR_eq (x : Nat) :
    1645498280219470655563407987279682868948834857825835856559341567 &&& x = zR x := rfl

/-- Stored word `K − R`, `K = γ1 + q` in every lane. -/
def zv (R : Nat) : Nat := 53427482372624644070796229104889929017927045372949748072275107841 - R

/-- Flag word: bit `25` of a lane is set iff `raw ≤ 78`, bit `50` iff `raw ≥ 262066`. -/
def zf (R : Nat) : Nat :=
  157197590578425089497557413537698244700129010769177211286849462349 + zv R |||
    (489613935360161099605733599630031180607565790085621957525582 + R) * 4294967296

theorem zf_eq (R : Nat) :
    157197590578425089497557413537698244700129010769177211286849462349 + zv R |||
      (489613935360161099605733599630031180607565790085621957525582 + R) * 4294967296 = zf R := rfl

theorem zsub (x : Nat) :
    UInt256.ofNat 53427482372624644070796229104889929017927045372949748072275107841 -
      UInt256.ofNat (zR x) = UInt256.ofNat (zv (zR x)) := by
  have h : zR x ≤ 1645498280219470655563407987279682868948834857825835856559341567 := Nat.and_le_left
  exact ofNat_sub (by omega) (by norm_num)

theorem zv_mod (R : Nat) :
    zv R % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = zv R :=
  Nat.mod_eq_of_lt (by unfold zv; omega)

theorem gW_mod (gs V0 V1 V2 V3 : Nat) :
    gW gs V0 V1 V2 V3 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      gW gs V0 V1 V2 V3 := by
  have hb : ∀ y c, c ≤ 192 → (18014398509481983 &&& y) * 2 ^ c < 2 ^ 256 := fun y c hc =>
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ Nat.and_le_left)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hc)) (by norm_num))
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow (hb _ 192 le_rfl) (Nat.or_lt_two_pow (hb _ 128 (by omega))
    (Nat.or_lt_two_pow (hb _ 64 (by omega)) (by simpa using hb (V0 / 2 ^ gs) 0 (by omega))))

end MlDsaOpt44.Proofs.DecodeZ
