import MlDsa44.Proofs.Layout
set_option warningAsError true
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
/-!
# Bit-level helpers

* `testBit_lit`: `Nat.testBit a b` on literals ↦ `true`/`false`.
* `eq_of_testBit_lt`: equality of two numbers below `2^n` from their low `n`
  bits; with `interval_cases j` this turns a mask/shift identity into one
  `simp` call per bit.
* `bswap_masks`: the `bswap64` subroutine's mask/shift network (in the exact
  form `evm_block` leaves it) is the byte reversal of the low 8 bytes.
-/

namespace MlDsa44.Proofs.Infra


open Lean Meta Simp in
dsimproc_decl testBit_lit (Nat.testBit _ _) := fun e => do
  unless e.isAppOfArity ``Nat.testBit 2 do return .continue
  let some a := (e.getArg! 0).nat? | return .continue
  let some b := (e.getArg! 1).nat? | return .continue
  return .done (toExpr (Nat.testBit a b))

theorem bswapRHS (x : Nat) :
    ((List.range 8).map fun i => x / 256 ^ i % 256 * 256 ^ (7 - i)).sum =
      2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (x % 2^8) + x / 2^8 % 2^8) + x / 2^16 % 2^8)
        + x / 2^24 % 2^8) + x / 2^32 % 2^8) + x / 2^40 % 2^8) + x / 2^48 % 2^8) + x / 2^56 % 2^8 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  norm_num
  ring

theorem eq_of_testBit_lt {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : ∀ j, j < n → x.testBit j = y.testBit j) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem bswap_masks (x : Nat) :
    ((((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 |||
              ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) %
                    115792089237316195423570985008687907853269984665640564039457584007913129639936 /
                  65536 &&&
                281470681808895) &&&
            4294967295) *
          4294967296 |||
        ((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 |||
              ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) %
                    115792089237316195423570985008687907853269984665640564039457584007913129639936 /
                  65536 &&&
                281470681808895) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 /
          4294967296) = ((List.range 8).map fun i => x / 256 ^ i % 256 * 256 ^ (7 - i)).sum := by
  rw [bswapRHS]
  have hQb : ((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 ||| ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536 &&& 281470681808895) < 2 ^ 64 := by
    apply Nat.or_lt_two_pow
    · have : ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895 ≤ 281470681808895 := Nat.and_le_right; simp only [Nat.reducePow]; omega
    · exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hL : (((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 ||| ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536 &&& 281470681808895) &&& 4294967295) * 4294967296 ||| ((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 ||| ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536 &&& 281470681808895) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 4294967296 < 2 ^ 64 := by
    apply Nat.or_lt_two_pow
    · have : ((((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) &&& 281470681808895) * 65536 ||| ((x &&& 71777214294589695) * 256 ||| x / 256 &&& 71777214294589695) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536 &&& 281470681808895) &&& 4294967295 ≤ 4294967295 := Nat.and_le_right; simp only [Nat.reducePow]; omega
    · rw [Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at hQb ⊢; omega)]; simp only [Nat.reducePow] at hQb ⊢; omega
  have hRb : (2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (2^8 * (x % 2^8) + x / 2^8 % 2^8) + x / 2^16 % 2^8)
        + x / 2^24 % 2^8) + x / 2^32 % 2^8) + x / 2^40 % 2^8) + x / 2^48 % 2^8) + x / 2^56 % 2^8) < 2 ^ 64 := by
    have h0 := Nat.mod_lt x (show 2^8 > 0 by positivity)
    have h1 := Nat.mod_lt (x / 2^8) (show 2^8 > 0 by positivity)
    have h2 := Nat.mod_lt (x / 2^16) (show 2^8 > 0 by positivity)
    have h3 := Nat.mod_lt (x / 2^24) (show 2^8 > 0 by positivity)
    have h4 := Nat.mod_lt (x / 2^32) (show 2^8 > 0 by positivity)
    have h5 := Nat.mod_lt (x / 2^40) (show 2^8 > 0 by positivity)
    have h6 := Nat.mod_lt (x / 2^48) (show 2^8 > 0 by positivity)
    have h7 := Nat.mod_lt (x / 2^56) (show 2^8 > 0 by positivity)
    norm_num at *
    omega
  apply eq_of_testBit_lt hL hRb
  have e8 : (256 : Nat) = 2 ^ 8 := rfl
  have e16 : (65536 : Nat) = 2 ^ 16 := rfl
  have e32 : (4294967296 : Nat) = 2 ^ 32 := rfl
  have e256 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) = 2 ^ 256 := rfl
  rw [e8, e16, e32, e256]
  intro j hj
  have hb : ∀ k, x / 2 ^ k % 2 ^ 8 < 2 ^ 8 := fun k => Nat.mod_lt _ (by positivity)
  have hb0 : x % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by positivity)
  interval_cases j <;>
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow,
      Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_mul_add _ (hb _),
      Nat.testBit_two_pow_mul_add _ hb0, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true,
      Bool.or_false, Bool.false_or, ↓reduceIte, testBit_lit]

end MlDsa44.Proofs.Infra
