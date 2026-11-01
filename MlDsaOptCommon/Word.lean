import MlDsaOptCommon.Basic
set_option warningAsError true
/-!
# Word algebra on `UInt256.ofNat`

After `evm_block`, stack words are `UInt256` expressions over `UInt256.ofNat`
atoms.  The `ofNat_*` lemmas below push every opcode through `ofNat`, giving
`UInt256.ofNat (natural-number expression)`; most are unconditional because
`ofNat` already reduces modulo `2^256`.  Use them as
`simp only [Infra.word_simps…]` (see `README.md`) and finish the value with a
`Nat` lemma.
-/

namespace MlDsaOptCommon

open EvmSemantics

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a :=
  (EvmProof.Word.word_eq_ofNat_toNat a).symm

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := by
  rw [EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_eq_ofNat_iff {a b : Nat} :
    UInt256.ofNat a = UInt256.ofNat b ↔ a % 2 ^ 256 = b % 2 ^ 256 := by
  constructor
  · intro h; have := congrArg UInt256.toNat h; simpa using this
  · intro h; apply EvmProof.Word.word_ext; simpa using h

theorem ofNat_mod (a : Nat) : UInt256.ofNat (a % 2 ^ 256) = UInt256.ofNat a := by
  rw [ofNat_eq_ofNat_iff, Nat.mod_mod]

theorem ofNat_land (a b : Nat) :
    (UInt256.ofNat a).land (UInt256.ofNat b) = UInt256.ofNat (a &&& b) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_land]
  simp only [EvmProof.Word.word_toNat_ofNat, Nat.and_mod_two_pow]

theorem ofNat_lor (a b : Nat) :
    (UInt256.ofNat a).lor (UInt256.ofNat b) = UInt256.ofNat (a ||| b) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_lor]
  simp only [EvmProof.Word.word_toNat_ofNat, Nat.or_mod_two_pow]

theorem ofNat_xor (a b : Nat) :
    (UInt256.ofNat a).xor (UInt256.ofNat b) = UInt256.ofNat (a ^^^ b) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_xor]
  simp only [EvmProof.Word.word_toNat_ofNat, Nat.xor_mod_two_pow]

theorem ofNat_mul (a b : Nat) :
    UInt256.ofNat a * UInt256.ofNat b = UInt256.ofNat (a * b) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.word_toNat_mul, EvmProof.Word.word_toNat_ofNat,
    EvmProof.Word.word_toNat_ofNat, EvmProof.Word.word_toNat_ofNat, ← Nat.mul_mod]

theorem ofNat_not (a : Nat) :
    UInt256.lnot (UInt256.ofNat a) = UInt256.ofNat (2 ^ 256 - 1 - a % 2 ^ 256) := by
  unfold UInt256.lnot
  rw [EvmProof.Word.word_toNat_ofNat]
  rfl

theorem ofNat_sub {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 256) :
    UInt256.ofNat a - UInt256.ofNat b = UInt256.ofNat (a - b) :=
  EvmProof.Word.ofNat_sub_ofNat hba ha

theorem ofNat_shl (a : Nat) {k : Nat} (hk : k < 256) :
    (UInt256.ofNat a).shiftLeft (UInt256.ofNat k) = UInt256.ofNat (a <<< k) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.shiftLeft_toNat _ hk]
  simp only [EvmProof.Word.word_toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem ofNat_shr (a : Nat) {k : Nat} (hk : k < 256) :
    (UInt256.ofNat a).shiftRight (UInt256.ofNat k) =
      UInt256.ofNat ((a % 2 ^ 256) >>> k) := by
  apply EvmProof.Word.word_ext
  rw [EvmProof.Word.shiftRight_toNat _ hk]
  simp only [EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.mod_lt _ (by decide)))]

theorem ofNat_lt (a b : Nat) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) =
      UInt256.ofNat (if a % 2 ^ 256 < b % 2 ^ 256 then 1 else 0) := by
  unfold UInt256.lt; simp only [EvmProof.Word.word_toNat_ofNat]; split <;> rfl

theorem ofNat_gt (a b : Nat) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) =
      UInt256.ofNat (if a % 2 ^ 256 > b % 2 ^ 256 then 1 else 0) := by
  unfold UInt256.gt; simp only [EvmProof.Word.word_toNat_ofNat]; split <;> rfl

theorem ofNat_eq (a b : Nat) :
    UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b) =
      UInt256.ofNat (if a % 2 ^ 256 = b % 2 ^ 256 then 1 else 0) := by
  unfold UInt256.eq; simp only [EvmProof.Word.word_toNat_ofNat]; split <;> rfl

theorem ofNat_isZero (a : Nat) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat (if a % 2 ^ 256 = 0 then 1 else 0) := by
  unfold UInt256.isZero; simp only [EvmProof.Word.word_toNat_ofNat]; split <;> rfl

theorem isTrue_ofNat (a : Nat) : UInt256.isTrue (UInt256.ofNat a) ↔ a % 2 ^ 256 ≠ 0 := by
  simp [UInt256.isTrue]

theorem ofNat_mod_ofNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h0 : 0 < b) :
    UInt256.ofNat a % UInt256.ofNat b = UInt256.ofNat (a % b) := by
  apply EvmProof.Word.word_ext
  change (UInt256.mod _ _).toNat = _
  unfold UInt256.mod
  simp only [EvmProof.Word.word_toNat_ofNat]
  have hb' : (UInt256.ofNat b).val.val = b := by
    change (UInt256.ofNat b).toNat = b; rw [toNat_ofNat_of_lt hb]
  rw [hb']
  split
  · omega
  · change ((UInt256.ofNat a).val % (UInt256.ofNat b).val).val = _
    rw [Fin.mod_val]
    change (UInt256.ofNat a).toNat % (UInt256.ofNat b).toNat = _
    rw [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem ofNat_div_ofNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.ofNat a / UInt256.ofNat b = UInt256.ofNat (a / b) := by
  apply EvmProof.Word.word_ext
  change (UInt256.div _ _).toNat = _
  unfold UInt256.div
  simp only [EvmProof.Word.word_toNat_ofNat]
  have hb' : (UInt256.ofNat b).val.val = b := by
    change (UInt256.ofNat b).toNat = b; rw [toNat_ofNat_of_lt hb]
  rw [hb']
  split
  · rename_i h; subst h; simp; rfl
  · change ((UInt256.ofNat a).val / (UInt256.ofNat b).val).val = _
    rw [Fin.div_val]
    change (UInt256.ofNat a).toNat / (UInt256.ofNat b).toNat = _
    rw [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_addMod (a b n : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hn : n < 2 ^ 256)
    (h0 : 0 < n) :
    UInt256.addMod (UInt256.ofNat a) (UInt256.ofNat b) (UInt256.ofNat n) =
      UInt256.ofNat ((a + b) % n) := by
  unfold UInt256.addMod
  have hn' : (UInt256.ofNat n).val.val = n := by
    change (UInt256.ofNat n).toNat = n; rw [toNat_ofNat_of_lt hn]
  rw [hn', if_neg (by omega), toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb, toNat_ofNat_of_lt hn]

theorem ofNat_mulMod (a b n : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hn : n < 2 ^ 256)
    (h0 : 0 < n) :
    UInt256.mulMod (UInt256.ofNat a) (UInt256.ofNat b) (UInt256.ofNat n) =
      UInt256.ofNat ((a * b) % n) := by
  unfold UInt256.mulMod
  have hn' : (UInt256.ofNat n).val.val = n := by
    change (UInt256.ofNat n).toNat = n; rw [toNat_ofNat_of_lt hn]
  rw [hn', if_neg (by omega), toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb, toNat_ofNat_of_lt hn]

end MlDsaOptCommon
