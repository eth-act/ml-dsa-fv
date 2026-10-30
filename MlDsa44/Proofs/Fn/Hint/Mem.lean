import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# Helpers for `encodeRow`

* `ofNat_byte`: the `BYTE` opcode on `ofNat` words (an `evm_block` lemma);
* `word_byte0`: byte 0 of the big-endian `word` at `a` is `byteAt m a`;
* `storeGroups`: memory after the `encodeRow` group loop has written `g`
  three-byte groups, with read-back and frame lemmas.
-/

namespace MlDsa44.Proofs.Hint

open EvmSemantics EvmSemantics.EVM

theorem ofNat_byte (k x : Nat) (hk : k < 32) :
    UInt256.byteAt (UInt256.ofNat k) (UInt256.ofNat x) =
      UInt256.ofNat ((x % 2 ^ 256) / 2 ^ (8 * (31 - k)) % 256) := by
  unfold UInt256.byteAt
  have hk' : (UInt256.ofNat k).toNat = k := Infra.toNat_ofNat_of_lt (by omega)
  rw [hk', if_neg (by omega), EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow]
  congr 1
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem land_255 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

theorem beNat_succ' (m : ByteArray) : ∀ (a w : Nat),
    Infra.beNat m a (w + 1) = byteAt m a * 256 ^ w + Infra.beNat m (a + 1) w
  | a, 0 => by simp [Infra.beNat]
  | a, w + 1 => by
    rw [Infra.beNat, beNat_succ' m a w, Infra.beNat, Nat.pow_succ,
      show a + (w + 1) = a + 1 + w by omega]
    rw [Nat.add_mul, Nat.mul_assoc]
    omega

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, Infra.beNat m a w < 256 ^ w
  | 0 => by simp [Infra.beNat]
  | w + 1 => by
    have h1 := beNat_lt m a w
    have h2 := Infra.byteAt_lt m (a + w)
    rw [Infra.beNat, Nat.pow_succ]
    have : (Infra.beNat m a w + 1) * 256 ≤ 256 ^ w * 256 := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul] at this
    omega

/-- `BYTE 0` of an `MLOAD`: `2^248 = 256^31`. -/
theorem word_byte0 (m : ByteArray) (a : Nat) :
    word m a / 452312848583266388373324160190187140051835877600158453279131187530910662656 % 256 =
      byteAt m a := by
  rw [Infra.word_eq_beNat, beNat_succ',
    show (452312848583266388373324160190187140051835877600158453279131187530910662656 : Nat) =
      256 ^ 31 by decide,
    Nat.mul_comm, Nat.mul_add_div (by decide), Nat.div_eq_of_lt (beNat_lt m _ 31), Nat.add_zero]
  exact Nat.mod_eq_of_lt (Infra.byteAt_lt m a)

/-- `MSTORE8` of the byte `x` (already reduced modulo 256) at `a`. -/
def wb (M : ByteArray) (a x : Nat) : ByteArray :=
  MachineState.writeBytes M { data := #[UInt8.ofNat x] } a

theorem byteAt_wb (M : ByteArray) (a x b : Nat) :
    byteAt (wb M a x) b = if b = a then x % 256 else byteAt M b := by
  have hsize : (ByteArray.mk #[UInt8.ofNat x]).size = 1 := rfl
  unfold wb
  rw [Infra.byteAt_writeBytes, hsize]
  by_cases h : b = a
  · subst h
    rw [if_pos (by omega), if_pos rfl, Nat.sub_self, byteAt, dif_pos (by rw [hsize]; omega)]
    change (UInt8.ofNat x).toNat = x % 256
    rw [UInt8.toNat_ofNat']
  · rw [if_neg (by omega), if_neg h]

/-- Memory after `g` groups: group `k` stores the low three bytes of `P k`
little-endian at `o + 3 k`. -/
def storeGroups (m : ByteArray) (o : Nat) (P : Nat → Nat) : Nat → ByteArray
  | 0 => m
  | g + 1 =>
    wb (wb (wb (storeGroups m o P g) (o + 3 * g) (P g % 256)) (o + 3 * g + 1) (P g / 256 % 256))
      (o + 3 * g + 2) (P g / 65536 % 256)

theorem byteAt_storeGroups_out (m : ByteArray) (o : Nat) (P : Nat → Nat) :
    ∀ G a, (a < o ∨ o + 3 * G ≤ a) → byteAt (storeGroups m o P G) a = byteAt m a
  | 0, _, _ => rfl
  | G + 1, a, h => by
    simp only [storeGroups, byteAt_wb]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact byteAt_storeGroups_out m o P G a (by omega)

theorem byteAt_storeGroups (m : ByteArray) (o : Nat) (P : Nat → Nat) :
    ∀ G j, j < 3 * G →
      byteAt (storeGroups m o P G) (o + j) = P (j / 3) / 256 ^ (j % 3) % 256
  | 0, _, h => absurd h (by omega)
  | G + 1, j, h => by
    simp only [storeGroups, byteAt_wb]
    by_cases h2 : o + j = o + 3 * G + 2
    · rw [if_pos h2, show j / 3 = G by omega, show j % 3 = 2 by omega, Nat.mod_mod]; rfl
    rw [if_neg h2]
    by_cases h1 : o + j = o + 3 * G + 1
    · rw [if_pos h1, show j / 3 = G by omega, show j % 3 = 1 by omega, Nat.mod_mod]; rfl
    rw [if_neg h1]
    by_cases h0 : o + j = o + 3 * G
    · rw [if_pos h0, show j / 3 = G by omega, show j % 3 = 0 by omega, Nat.mod_mod]; simp
    rw [if_neg h0]
    exact byteAt_storeGroups m o P G j (by omega)

theorem FrameExcept.storeGroups (m : ByteArray) (o : Nat) (P : Nat → Nat) (G : Nat) :
    FrameExcept m (storeGroups m o P G) [(o, o + 3 * G)] := by
  intro a ha
  exact byteAt_storeGroups_out m o P G a (by simpa using ha (o, o + 3 * G) (by simp))

end MlDsa44.Proofs.Hint
