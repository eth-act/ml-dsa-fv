import MlDsa44.Proofs.Fn.UnpackZetas.Bytes
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The value computed by `unpack`

`unpack_value`: four little-endian calldata bytes at `off + p / 8`, shifted
right by `p mod 8` and masked to `c` bits (in the exact form `evm_block`
leaves it), are `Fips204.bitsToInteger` of the field `[off, off + n)` at bit
`p`.
-/

namespace MlDsa44.Proofs.UnpackZetas

open Infra

theorem bitsToInteger_succ (v : ByteArray) (p c : Nat) :
    Fips204.bitsToInteger v p (c + 1) =
      Fips204.bitsToInteger v p c + Fips204.bit v (p + c) * 2 ^ c := by
  simp [Fips204.bitsToInteger, List.range_succ, List.map_append, List.sum_append]

/-- `c` bits of `x` from bit `s` are `bitsToInteger v p c` when they agree
bit by bit. -/
theorem div_mod_eq_bitsToInteger (v : ByteArray) (x s p : Nat) :
    ∀ c, (∀ t, t < c → x / 2 ^ (s + t) % 2 = Fips204.bit v (p + t)) →
      x / 2 ^ s % 2 ^ c = Fips204.bitsToInteger v p c
  | 0, _ => by simp [Fips204.bitsToInteger, Nat.mod_one]
  | c + 1, h => by
    rw [Nat.mod_pow_succ, bitsToInteger_succ,
      div_mod_eq_bitsToInteger v x s p c (fun t ht => h t (by omega)),
      Nat.div_div_eq_div_mul, ← Nat.pow_add, h c (by omega), Nat.mul_comm]

/-- Bit `u` of four little-endian bytes. -/
theorem le32_bit (b : Nat → Nat) (hb : ∀ k, b k < 256) (u : Nat) (hu : u < 32) :
    (b 0 ||| b 1 * 256 ||| (b 2 * 65536 ||| b 3 * 16777216)) / 2 ^ u % 2 =
      b (u / 8) / 2 ^ (u % 8) % 2 := by
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit]
  congr 1
  have hf : ∀ k j, 8 ≤ j → (b k).testBit j = false := fun k j hj => by
    have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    exact Nat.testBit_lt_two_pow (by have := hb k; omega)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, show (65536 : Nat) = 2 ^ 16 from rfl,
    show (16777216 : Nat) = 2 ^ 24 from rfl]
  interval_cases u <;>
    simp (disch := omega) only [Nat.testBit_or, Nat.testBit_mul_two_pow, hf, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceLeDiff, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.or_false, Bool.false_or]

theorem byteAt_eq_extract (cd : ByteArray) {off n j : Nat} (hfield : off + n ≤ cd.size)
    (hj : j < n) : byteAt cd (off + j) = (cd.extract off (off + n))[j]!.toNat := by
  have hs : j < (cd.extract off (off + n)).size := by
    rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (c := cd.extract off (off + n)) (i := j) (h := hs), ByteArray.getElem_extract, byteAt, dif_pos (by omega)]

theorem unpack_value (cd : ByteArray) {off n p c : Nat} (hc : c ≤ 18)
    (hfield : off + n ≤ cd.size) (hp : p + c ≤ 8 * n) :
    ((byteAt cd (off + p / 8 + 0) ||| byteAt cd (off + p / 8 + 1) * 256 |||
        (byteAt cd (off + p / 8 + 2) * 65536 ||| byteAt cd (off + p / 8 + 3) * 16777216)) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 /
        2 ^ (p &&& 7) &&& 1 * 2 ^ c - 1) =
      Fips204.bitsToInteger (cd.extract off (off + n)) p c := by
  have hb : ∀ k, byteAt cd (off + p / 8 + k) < 256 := fun k => byteAt_lt cd _
  have hX : (byteAt cd (off + p / 8 + 0) ||| byteAt cd (off + p / 8 + 1) * 256 |||
        (byteAt cd (off + p / 8 + 2) * 65536 ||| byteAt cd (off + p / 8 + 3) * 16777216)) <
      2 ^ 256 := by
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
    refine Nat.lt_of_lt_of_le (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_)
      (Nat.or_lt_two_pow ?_ ?_)) (Nat.pow_le_pow_right (by omega) (show 32 ≤ 256 by omega)) <;>
      simp only [Nat.reducePow] <;> omega
  rw [Nat.mod_eq_of_lt (show _ < 115792089237316195423570985008687907853269984665640564039457584007913129639936 from hX), Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
    show p &&& 7 = p % 8 from Nat.and_two_pow_sub_one_eq_mod p 3]
  apply div_mod_eq_bitsToInteger
  intro t ht
  rw [le32_bit (fun k => byteAt cd (off + p / 8 + k)) hb _ (by omega), Fips204.bit,
    ← byteAt_eq_extract cd hfield (by omega)]
  rw [show off + p / 8 + (p % 8 + t) / 8 = off + (p + t) / 8 by omega,
    show (p % 8 + t) % 8 = (p + t) % 8 by omega]

end MlDsa44.Proofs.UnpackZetas
