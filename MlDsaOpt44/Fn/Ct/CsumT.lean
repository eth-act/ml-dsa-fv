import MlDsaOpt44.Fn.Ct.CsumBlocks
import MlDsaOpt44.Fn.Ct.CsumMath
/-!
# `csum` (WP10): the 16-bit transpose

`cs4o0 … x` (two delta swaps) moves bit `64 a + 16 b + e` of `x` to
`64 b + 16 a + e` (`a, b < 4`, `e < 16`).
-/

set_option linter.unusedSimpArgs false

namespace MlDsaOpt44.Proofs.CS

open EvmSemantics
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.L10

/-- Source bit of transposed bit `i`. -/
def tp (i : Nat) : Nat := 64 * (i % 64 / 16) + 16 * (i / 64) + i % 16

theorem xl1 (a b : Bool) : (a ^^ (a ^^ b)) = b := by cases a <;> cases b <;> rfl
theorem xl2 (a b : Bool) : (a ^^ (b ^^ a)) = b := by cases a <;> cases b <;> rfl
theorem xl3 (a b c : Bool) : (a ^^ (b ^^ (a ^^ c))) = (b ^^ c) := by cases a <;> cases b <;> cases c <;> rfl

set_option maxHeartbeats 4000000 in
theorem tp_bits_ofNat (M : ByteArray) (bu cw sp : Nat) (g : UInt256) {X : Nat} (hX : X < 2 ^ 256)
    {i : Nat} (hi : i < 256) :
    (cs4o0 M bu cw sp g (UInt256.ofNat X)).toNat.testBit i = X.testBit (tp i) := by
  have hz : ∀ j, 256 ≤ j → X.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega) hj))
  simp (disch := decide) only [cs4o0, ofNat_land, ofNat_xor, ofNat_shl, ofNat_shr,
    EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hX]
  unfold tp
  interval_cases i <;>
    simp (disch := first | decide | omega) only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_lit, hz,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceLeDiff, decide_true, decide_false, ge_iff_le, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.xor_false, Bool.false_xor, Bool.xor_self, Bool.xor_true,
      Bool.true_xor, Bool.not_not, Bool.xor_assoc, xl1, xl2, xl3]

theorem tp_bits (M : ByteArray) (bu cw sp : Nat) (g x : UInt256) {i : Nat} (hi : i < 256) :
    (cs4o0 M bu cw sp g x).toNat.testBit i = x.toNat.testBit (tp i) := by
  have h := tp_bits_ofNat M bu cw sp g (X := x.toNat) x.val.isLt hi
  rwa [ofNat_toNat] at h

end MlDsaOpt44.Proofs.CS
