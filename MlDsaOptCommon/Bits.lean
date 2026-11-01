import MlDsaOptCommon.Basic
set_option warningAsError true
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
/-!
# Bit-level helpers

* `testBit_lit`: `Nat.testBit a b` on literals ↦ `true`/`false`.
* `eq_of_testBit_lt`: equality of two numbers below `2^n` from their low `n`
  bits; with `interval_cases j` this turns a mask/shift identity into one
  `simp` call per bit.
-/

namespace MlDsaOptCommon


open Lean Meta Simp in
dsimproc_decl testBit_lit (Nat.testBit _ _) := fun e => do
  unless e.isAppOfArity ``Nat.testBit 2 do return .continue
  let some a := (e.getArg! 0).nat? | return .continue
  let some b := (e.getArg! 1).nat? | return .continue
  return .done (toExpr (Nat.testBit a b))

theorem eq_of_testBit_lt {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : ∀ j, j < n → x.testBit j = y.testBit j) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

end MlDsaOptCommon
