import MlDsa44.Proofs.Fn.Keccak.Model
/-!
# Lanes as words: `UInt64` operations versus the Yul word operations

`L a` is the 64-bit lane `a` held in a 256-bit word.  The lemmas push `L`
through the spec's lane operations (`^^^`, `rotl64`, the chi term), giving
the word operations of the Yul model, and evaluate `mloadY` after `mstoreY`.
-/

namespace MlDsa44.Proofs.KeccakModel

open EvmSemantics
open EvmSemantics.EVM

/-- A lane in a word. -/
def L (a : UInt64) : UInt256 := UInt256.ofNat a.toNat

theorem L_toNat (a : UInt64) : (L a).toNat = a.toNat := by
  unfold L
  rw [EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by have := a.toNat_lt; omega)]

theorem L_xor (a b : UInt64) : L (a ^^^ b) = UInt256.xor (L a) (L b) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_xor, L_toNat, L_toNat, L_toNat, UInt64.toNat_xor]

theorem L_andnot (b c : UInt64) :
    L ((b ^^^ 0xffffffffffffffff) &&& c) = UInt256.land (UInt256.lnot (L b)) (L c) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_land, L_toNat, L_toNat, UInt64.toNat_and, UInt64.toNat_xor]
  unfold UInt256.lnot
  rw [EvmProof.Word.word_toNat_ofNat, L_toNat]
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hm : (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 := rfl
  rw [hm, Nat.mod_eq_of_lt (by simp only [UInt256.size]; omega),
    show UInt256.size - 1 - b.toNat = 2 ^ 256 - (b.toNat + 1) by simp only [UInt256.size]; omega]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_succ (by omega)]
  by_cases hi : i < 64
  · have : i < 256 := by omega
    simp [hi, this]
  · have : c.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem L_rotl (a : UInt64) {n : Nat} (h0 : 0 < n) (h64 : n < 64) :
    L (Crypto.Keccak.rotl64 a n) = rotY (L a) n := by
  apply EvmProof.Word.word_ext
  unfold rotY Crypto.Keccak.rotl64
  rw [if_neg (by omega), EvmProof.Word.word_toNat_lor, EvmProof.Word.word_toNat_land,
    EvmProof.Word.shiftLeft_toNat _ (by omega), EvmProof.Word.shiftRight_toNat _ (by omega),
    L_toNat, L_toNat, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    EvmProof.Word.word_toNat_ofNat]
  have hn : (UInt64.ofNat n).toNat % 64 = n := by
    rw [UInt64.toNat_ofNat']; omega
  have hn' : (UInt64.ofNat (64 - n)).toNat % 64 = 64 - n := by
    rw [UInt64.toNat_ofNat']; omega
  rw [hn, hn', Nat.shiftLeft_eq,
    show (0xffffffffffffffff : Nat) % 2 ^ 256 = 2 ^ 64 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num))]

theorem rotl64_zero (a : UInt64) : Crypto.Keccak.rotl64 a 0 = a := by
  simp [Crypto.Keccak.rotl64]

/-! ## Memory -/

theorem mloadY_eq_ofNat (M : ByteArray) (a : Nat) : mloadY M a = UInt256.ofNat (word M a) :=
  Infra.readWord_eq_word M a

theorem word_eq_toNat_mloadY (M : ByteArray) (a : Nat) : word M a = (mloadY M a).toNat := rfl

theorem mloadY_of_word {M : ByteArray} {a : Nat} {x : UInt64} (h : word M a = x.toNat) :
    mloadY M a = L x := by
  rw [mloadY_eq_ofNat, h]; rfl

theorem word_of_mloadY {M : ByteArray} {a : Nat} {x : UInt64} (h : mloadY M a = L x) :
    word M a = x.toNat := by
  rw [word_eq_toNat_mloadY, h, L_toNat]

theorem mloadY_mstoreY_same (M : ByteArray) (a : Nat) (v : UInt256) :
    mloadY (mstoreY M a v) a = v := by
  rw [mloadY_eq_ofNat, mstoreY, Infra.word_mstore _ _ _ (show v.toNat < 2 ^ 256 from v.val.isLt), Infra.ofNat_toNat]

theorem mloadY_mstoreY_ne (M : ByteArray) {a b : Nat} (v : UInt256)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) : mloadY (mstoreY M b v) a = mloadY M a := by
  rw [mloadY_eq_ofNat, mloadY_eq_ofNat, mstoreY, Infra.word_mstore_disjoint _ _ h]

theorem FrameExcept.mstoreY (M : ByteArray) {a lo hi : Nat} (v : UInt256) (hlo : lo ≤ a)
    (hhi : a + 32 ≤ hi) : FrameExcept M (KeccakModel.mstoreY M a v) [(lo, hi)] :=
  Infra.FrameExcept.mono (Infra.FrameExcept.mstore M a v.toNat) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨(lo, hi), by simp, hlo, hhi⟩)

theorem FrameExcept.trans' {m₁ m₂ m₃ : ByteArray} {rs : List (Nat × Nat)}
    (h₁ : FrameExcept m₁ m₂ rs) (h₂ : FrameExcept m₂ m₃ rs) : FrameExcept m₁ m₃ rs :=
  Infra.FrameExcept.mono (Infra.FrameExcept.trans h₁ h₂) (by
    intro r hr
    exact ⟨r, by simpa using hr, le_rfl, le_rfl⟩)

theorem mloadY_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs)
    {a : Nat} (ha : Infra.Avoids rs a (a + 32)) : mloadY M' a = mloadY M a := by
  rw [mloadY_eq_ofNat, mloadY_eq_ofNat, Infra.FrameExcept.word h ha]

end MlDsa44.Proofs.KeccakModel
