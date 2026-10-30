import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# `byte(0, calldataload(a))` and `MSTORE8` in `evm_block` form

`evm_block` leaves `CALLDATALOAD` as `UInt256.ofNat (word cd a)`;
`byte0_word` turns `BYTE 0` of it into the single byte `byteAt cd a`.
-/

namespace MlDsa44.Proofs.Decode

open EvmSemantics
open EvmSemantics.EVM

theorem beNat_succ (m : ByteArray) : ∀ (a w : Nat),
    Infra.beNat m a (w + 1) = byteAt m a * 256 ^ w + Infra.beNat m (a + 1) w
  | a, 0 => by simp [Infra.beNat]
  | a, w + 1 => by
    rw [Infra.beNat, beNat_succ m a w, Infra.beNat, show a + (w + 1) = a + 1 + w by omega,
      pow_succ]
    ring

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, Infra.beNat m a w < 256 ^ w
  | 0 => by simp [Infra.beNat]
  | w + 1 => by
    have h1 := beNat_lt m a w
    have h2 := Infra.byteAt_lt m (a + w)
    rw [Infra.beNat, pow_succ]
    have h3 : (Infra.beNat m a w + 1) * 256 ≤ 256 ^ w * 256 := Nat.mul_le_mul_right _ h1
    omega

theorem byte0_word (m : ByteArray) (a : Nat) :
    UInt256.byteAt (UInt256.ofNat 0) (UInt256.ofNat (word m a)) = UInt256.ofNat (byteAt m a) := by
  unfold UInt256.byteAt
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  rw [h0, if_neg (by omega), EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (Infra.word_lt m a),
    Infra.word_eq_beNat, beNat_succ, Nat.shiftRight_eq_div_pow]
  have hb := Infra.byteAt_lt m a
  have hr := beNat_lt m (a + 1) 31
  have : (byteAt m a * 256 ^ 31 + Infra.beNat m (a + 1) 31) / 2 ^ (8 * (31 - 0)) = byteAt m a := by
    rw [show (2 : Nat) ^ (8 * (31 - 0)) = 256 ^ 31 by norm_num, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [this, show (0xff : Nat) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)]

theorem byteAt_lt_two_pow (m : ByteArray) (a : Nat) : byteAt m a < 2 ^ 256 :=
  lt_trans (Infra.byteAt_lt m a) (by norm_num)

end MlDsa44.Proofs.Decode
