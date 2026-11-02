import EvmProof.Word
set_option warningAsError true
/-! `xor`, `and` and `or` on `UInt256` are associative and commutative, so
`ac_rfl` can identify terms that differ only in operand order (the
stack-resident Keccak kernels compute the round model's terms with some
operands swapped). -/

namespace MlDsaOptGlam44.Proofs

open EvmSemantics

theorem u256_ext {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; simp only [UInt256.toNat] at h; congr; exact Fin.ext h

instance xor_comm : Std.Commutative UInt256.xor := ⟨fun a b => u256_ext (by
  rw [EvmProof.Word.word_toNat_xor, EvmProof.Word.word_toNat_xor, Nat.xor_comm])⟩
instance xor_assoc : Std.Associative UInt256.xor := ⟨fun a b c => u256_ext (by
  simp only [EvmProof.Word.word_toNat_xor, Nat.xor_assoc])⟩
instance land_comm : Std.Commutative UInt256.land := ⟨fun a b => u256_ext (by
  rw [EvmProof.Word.word_toNat_land, EvmProof.Word.word_toNat_land, Nat.and_comm])⟩
instance land_assoc : Std.Associative UInt256.land := ⟨fun a b c => u256_ext (by
  simp only [EvmProof.Word.word_toNat_land, Nat.and_assoc])⟩
instance lor_comm : Std.Commutative UInt256.lor := ⟨fun a b => u256_ext (by
  rw [EvmProof.Word.word_toNat_lor, EvmProof.Word.word_toNat_lor, Nat.or_comm])⟩
instance lor_assoc : Std.Associative UInt256.lor := ⟨fun a b c => u256_ext (by
  simp only [EvmProof.Word.word_toNat_lor, Nat.or_assoc])⟩

/-- Commutativity as `simp` lemmas: `simp` applies them as ordered rewrites,
so two terms that differ only in operand order reach the same normal form
(also inside other functions' arguments, where `ac_rfl` does not look). -/
theorem u256_xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a :=
  Std.Commutative.comm a b
theorem u256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a :=
  Std.Commutative.comm a b
theorem u256_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a :=
  Std.Commutative.comm a b

end MlDsaOptGlam44.Proofs
