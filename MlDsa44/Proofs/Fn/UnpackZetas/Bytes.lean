import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# `BYTE` of a calldata/memory word

`ofNat_byteAt_word`: the `BYTE k` opcode applied to the 32-byte big-endian
`word m a` gives `byteAt m (a + k)` (an `evm_block` simp lemma).
-/

namespace MlDsa44.Proofs.UnpackZetas

open EvmSemantics
open Infra

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, beNat m a w < 256 ^ w
  | 0 => by simp [beNat]
  | w + 1 => by
    have h1 := beNat_lt m a w
    have := byteAt_lt m (a + w)
    have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt h1)
    simp only [beNat, Nat.pow_succ, Nat.succ_mul] at this ⊢
    omega

theorem beNat_split (m : ByteArray) (a j : Nat) :
    ∀ k, beNat m a (j + k) = beNat m a j * 256 ^ k + beNat m (a + j) k
  | 0 => by simp [beNat]
  | k + 1 => by
    rw [← Nat.add_assoc, beNat, beNat_split m a j k, beNat, Nat.add_assoc a j k, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem word_div_mod (m : ByteArray) (a k : Nat) (hk : k < 32) :
    word m a / 2 ^ (8 * (31 - k)) % 256 = byteAt m (a + k) := by
  rw [word_eq_beNat, show 32 = (k + 1) + (31 - k) by omega, beNat_split,
    show 2 ^ (8 * (31 - k)) = 256 ^ (31 - k) by rw [Nat.pow_mul],
    Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (beNat_lt _ _ _), Nat.zero_add, beNat, Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt (byteAt_lt m _)

theorem ofNat_byteAt_word (m : ByteArray) (a k : Nat) (hk : k < 32) :
    UInt256.byteAt (UInt256.ofNat k) (UInt256.ofNat (word m a)) =
      UInt256.ofNat (byteAt m (a + k)) := by
  unfold UInt256.byteAt
  have hk' : (UInt256.ofNat k).toNat = k := toNat_ofNat_of_lt (by omega)
  rw [hk', if_neg (by omega), EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (word_lt m a),
    Nat.shiftRight_eq_div_pow, ← word_div_mod m a k hk]
  congr 1
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

end MlDsa44.Proofs.UnpackZetas
