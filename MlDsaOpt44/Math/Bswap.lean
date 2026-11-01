import MlDsaOpt44.Layout
import MlDsaOptCommon.Memory
import MlDsaOptCommon.Bits
set_option warningAsError true
/-!
# The SIMD lane byte-swap network

The generator's `bswap4` (three masked delta swaps by 8, 16 and 32 bits,
`DUP1 PUSH s SHR DUPk AND SWAP1 DUPk AND PUSH s SHL OR`) reverses the bytes of
each 64-bit lane of a word. Applied to a `CALLDATALOAD` word it yields the four
little-endian lanes of the 32 calldata bytes, the first lane on top.

`bswapNet` is the network in the exact form `opt44_block` leaves it
(`bsw8`, `bsw16`, `bsw32`: pass them to `opt44_reach … with [...]` to match).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon

/-- Swap adjacent bytes. -/
def bsw8 (x : Nat) : Nat :=
  (450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x) * 256 |||
    450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x / 256

/-- Swap adjacent 16-bit halves. -/
def bsw16 (x : Nat) : Nat :=
  (1766820105243087041267848467410591083712559083657179364930612997358944255 &&& x) * 65536 |||
    1766820105243087041267848467410591083712559083657179364930612997358944255 &&&
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 65536

/-- Swap adjacent 32-bit halves. -/
def bsw32 (x : Nat) : Nat :=
  (26959946660873538060741835960174461801791452538186943042387869433855 &&& x) * 4294967296 |||
    26959946660873538060741835960174461801791452538186943042387869433855 &&&
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 /
        4294967296

/-- Byte reversal of every 64-bit lane. -/
def bswapNet (x : Nat) : Nat := bsw32 (bsw16 (bsw8 x))

/-! ## Bits -/

private theorem m8_bits : ∀ j, j < 256 →
    (450552876409790643671482431940419874915447411150352389258589821042463539455 : Nat).testBit j =
      decide (j / 8 % 2 = 0 ∧ j < 248) := by decide +kernel

private theorem m16_bits : ∀ j, j < 256 →
    (1766820105243087041267848467410591083712559083657179364930612997358944255 : Nat).testBit j =
      decide (j / 16 % 2 = 0 ∧ j < 240) := by decide +kernel

private theorem m32_bits : ∀ j, j < 256 →
    (26959946660873538060741835960174461801791452538186943042387869433855 : Nat).testBit j =
      decide (j / 32 % 2 = 0 ∧ j < 224) := by decide +kernel

private theorem testBit_ge {x j : Nat} (hx : x < 2 ^ 256) (hj : 256 ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))

theorem bsw8_testBit {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 256) :
    (bsw8 x).testBit j = x.testBit (if j / 8 % 2 = 0 then j + 8 else j - 8) := by
  unfold bsw8
  rw [show (256 : Nat) = 2 ^ 8 from rfl]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : j / 8 % 2 = 0
  · rw [if_pos h, m8_bits j hj]
    by_cases h8 : 8 ≤ j
    · rw [m8_bits (j - 8) (by omega)]
      simp only [show ¬ ((j - 8) / 8 % 2 = 0 ∧ j - 8 < 248) by omega, decide_false,
        Bool.false_and, Bool.and_false, Bool.false_or]
      by_cases h2 : j < 248
      · simp [h, h2]
      · rw [testBit_ge hx (by omega)]; simp [h2]
    · simp only [show ¬ (8 ≤ j) from h8, decide_false, Bool.false_and, Bool.false_or]
      by_cases h2 : j < 248
      · simp [h, h2]
      · omega
  · rw [if_neg h, m8_bits j hj]
    have h8 : 8 ≤ j := by omega
    rw [m8_bits (j - 8) (by omega)]
    simp only [show ¬ (j / 8 % 2 = 0 ∧ j < 248) by omega, decide_false, Bool.false_and, Bool.or_false,
      show (j - 8) / 8 % 2 = 0 ∧ j - 8 < 248 by omega, decide_true, Bool.true_and, h8, and_self]

theorem bsw16_testBit {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 256) :
    (bsw16 x).testBit j = x.testBit (if j / 16 % 2 = 0 then j + 16 else j - 16) := by
  unfold bsw16
  rw [show (65536 : Nat) = 2 ^ 16 from rfl,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 from rfl, Nat.mod_eq_of_lt hx]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : j / 16 % 2 = 0
  · rw [if_pos h, m16_bits j hj]
    by_cases h8 : 16 ≤ j
    · rw [m16_bits (j - 16) (by omega)]
      simp only [show ¬ ((j - 16) / 16 % 2 = 0 ∧ j - 16 < 240) by omega, decide_false,
        Bool.false_and, Bool.and_false, Bool.false_or]
      by_cases h2 : j < 240
      · simp [h, h2]
      · rw [testBit_ge hx (by omega)]; simp [h2]
    · simp only [show ¬ (16 ≤ j) from h8, decide_false, Bool.false_and, Bool.false_or]
      by_cases h2 : j < 240
      · simp [h, h2]
      · omega
  · rw [if_neg h, m16_bits j hj]
    have h8 : 16 ≤ j := by omega
    rw [m16_bits (j - 16) (by omega)]
    simp only [show ¬ (j / 16 % 2 = 0 ∧ j < 240) by omega, decide_false, Bool.false_and, Bool.or_false,
      show (j - 16) / 16 % 2 = 0 ∧ j - 16 < 240 by omega, decide_true, Bool.true_and, h8, and_self]

theorem bsw32_testBit {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 256) :
    (bsw32 x).testBit j = x.testBit (if j / 32 % 2 = 0 then j + 32 else j - 32) := by
  unfold bsw32
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl,
    show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 from rfl, Nat.mod_eq_of_lt hx]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : j / 32 % 2 = 0
  · rw [if_pos h, m32_bits j hj]
    by_cases h8 : 32 ≤ j
    · rw [m32_bits (j - 32) (by omega)]
      simp only [show ¬ ((j - 32) / 32 % 2 = 0 ∧ j - 32 < 224) by omega, decide_false,
        Bool.false_and, Bool.and_false, Bool.false_or]
      by_cases h2 : j < 224
      · simp [h, h2]
      · rw [testBit_ge hx (by omega)]; simp [h2]
    · simp only [show ¬ (32 ≤ j) from h8, decide_false, Bool.false_and, Bool.false_or]
      by_cases h2 : j < 224
      · simp [h, h2]
      · omega
  · rw [if_neg h, m32_bits j hj]
    have h8 : 32 ≤ j := by omega
    rw [m32_bits (j - 32) (by omega)]
    simp only [show ¬ (j / 32 % 2 = 0 ∧ j < 224) by omega, decide_false, Bool.false_and, Bool.or_false,
      show (j - 32) / 32 % 2 = 0 ∧ j - 32 < 224 by omega, decide_true, Bool.true_and, h8, and_self]

private theorem and_lt {m x : Nat} (n : Nat) (h : m < 2 ^ n) : m &&& x < 2 ^ n :=
  Nat.lt_of_le_of_lt Nat.and_le_left h

private theorem and_mul_lt {m x K : Nat} (h : m * K < 2 ^ 256) : (m &&& x) * K < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right K Nat.and_le_left) h

theorem bsw8_lt (x : Nat) : bsw8 x < 2 ^ 256 := by
  unfold bsw8
  apply Nat.or_lt_two_pow
  · exact and_mul_lt (by norm_num)
  · exact and_lt 256 (by norm_num)

theorem bsw16_lt (x : Nat) : bsw16 x < 2 ^ 256 := by
  unfold bsw16
  apply Nat.or_lt_two_pow
  · exact and_mul_lt (by norm_num)
  · exact and_lt 256 (by norm_num)

theorem bsw32_lt (x : Nat) : bsw32 x < 2 ^ 256 := by
  unfold bsw32
  apply Nat.or_lt_two_pow
  · exact and_mul_lt (by norm_num)
  · exact and_lt 256 (by norm_num)

theorem bswapNet_lt (x : Nat) : bswapNet x < 2 ^ 256 := bsw32_lt _

/-- Byte `p` of the net is byte `8 ⌊p/8⌋ + 7 − p mod 8` of the input. -/
theorem bswapNet_testBit {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : j < 256) :
    (bswapNet x).testBit j = x.testBit (64 * (j / 64) + 8 * (7 - j % 64 / 8) + j % 8) := by
  unfold bswapNet
  rw [bsw32_testBit (bsw16_lt _) hj]
  split
  · rw [bsw16_testBit (bsw8_lt _) (by omega)]
    split
    · rw [bsw8_testBit hx (by omega)]; congr 1; split <;> omega
    · rw [bsw8_testBit hx (by omega)]; congr 1; split <;> omega
  · rw [bsw16_testBit (bsw8_lt _) (by omega)]
    split
    · rw [bsw8_testBit hx (by omega)]; congr 1; split <;> omega
    · rw [bsw8_testBit hx (by omega)]; congr 1; split <;> omega

/-! ## Bytes -/

/-- Byte `p` (from the bottom) of `x`. -/
def byteN (x p : Nat) : Nat := x / 2 ^ (8 * p) % 2 ^ 8

theorem testBit_byteN (x j : Nat) : x.testBit j = (byteN x (j / 8)).testBit (j % 8) := by
  unfold byteN
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    show j % 8 + 8 * (j / 8) = j by omega]
  simp [Nat.mod_lt j (by omega : 8 > 0)]

theorem eq_of_byteN {x y : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256)
    (h : ∀ p, p < 32 → byteN x p = byteN y p) : x = y :=
  eq_of_testBit_lt hx hy fun j hj => by
    rw [testBit_byteN x j, testBit_byteN y j, h (j / 8) (by omega)]

theorem byteN_bswapNet {x : Nat} (hx : x < 2 ^ 256) {p : Nat} (hp : p < 32) :
    byteN (bswapNet x) p = byteN x (8 * (p / 8) + 7 - p % 8) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold byteN
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 8
  · simp only [hi, decide_true, Bool.true_and]
    rw [bswapNet_testBit hx (by omega)]
    congr 1
    omega
  · simp [hi]

theorem byteN_beNat (m : ByteArray) (a : Nat) :
    ∀ w q, q < w → byteN (beNat m a w) q = byteAt m (a + (w - 1 - q))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | w + 1, q, h => by
    have hb := byteAt_lt m (a + w)
    unfold byteN
    simp only [beNat]
    rcases q with _ | q
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      rw [show w + 1 - 1 - 0 = w by omega]
      omega
    · have := byteN_beNat m a w q (by omega)
      unfold byteN at this
      rw [show w + 1 - 1 - (q + 1) = w - 1 - q by omega, ← this,
        show 8 * (q + 1) = 8 + 8 * q by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      congr 2
      omega

theorem byteN_word (m : ByteArray) (a : Nat) {q : Nat} (hq : q < 32) :
    byteN (word m a) q = byteAt m (a + (31 - q)) := by
  rw [word_eq_beNat, byteN_beNat m a 32 q hq]

private theorem le64_eq (b : ByteArray) (a : Nat) :
    le64 b a = byteAt b a + 256 * byteAt b (a + 1) + 65536 * byteAt b (a + 2) +
      16777216 * byteAt b (a + 3) + 4294967296 * byteAt b (a + 4) +
      1099511627776 * byteAt b (a + 5) + 281474976710656 * byteAt b (a + 6) +
      72057594037927936 * byteAt b (a + 7) := by
  unfold le64
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  norm_num
  ring

private theorem le64_lt (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 64 := by
  rw [le64_eq]
  have := byteAt_lt b a; have := byteAt_lt b (a + 1); have := byteAt_lt b (a + 2)
  have := byteAt_lt b (a + 3); have := byteAt_lt b (a + 4); have := byteAt_lt b (a + 5)
  have := byteAt_lt b (a + 6); have := byteAt_lt b (a + 7)
  norm_num; omega

theorem byteN_le64 (b : ByteArray) (a : Nat) {i : Nat} (hi : i < 8) :
    byteN (le64 b a) i = byteAt b (a + i) := by
  rw [le64_eq]
  have := byteAt_lt b a; have := byteAt_lt b (a + 1); have := byteAt_lt b (a + 2)
  have := byteAt_lt b (a + 3); have := byteAt_lt b (a + 4); have := byteAt_lt b (a + 5)
  have := byteAt_lt b (a + 6); have := byteAt_lt b (a + 7)
  unfold byteN
  interval_cases i <;> norm_num <;> omega

/-- Lane `k` of four packed 64-bit values. -/
theorem pack4_div_mod {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    pack4 v / 2 ^ (64 * k) % 2 ^ 64 = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem pack4_lt' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) : pack4 v < 2 ^ 256 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem byteN_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {p : Nat} (hp : p < 32) :
    byteN (pack4 v) p = byteN (v (p / 8)) (p % 8) := by
  rw [← pack4_div_mod h (k := p / 8) (by omega)]
  unfold byteN
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 8
  · simp only [hi, decide_true, Bool.true_and, show i + 8 * (p % 8) < 64 by omega]
    congr 1; omega
  · simp [hi]

/-- **The byte-swapped calldata word**: lane `3 − j` is `LE64(cd[a + 8j …])`. -/
theorem bswapNet_word (cd : ByteArray) (a : Nat) :
    bswapNet (word cd a) = pack4 fun k => le64 cd (a + 8 * (3 - k)) := by
  have hv : ∀ k, k < 4 → le64 cd (a + 8 * (3 - k)) < 2 ^ 64 := fun k _ => le64_lt _ _
  apply eq_of_byteN (bswapNet_lt _) (pack4_lt' hv)
  intro p hp
  rw [byteN_bswapNet (word_lt cd a) hp, byteN_word cd a (by omega), byteN_pack4 hv hp,
    byteN_le64 cd _ (Nat.mod_lt _ (by omega))]
  congr 1
  omega

/-- Lane `k` of the byte-swapped calldata word. -/
theorem lane_bswapNet (cd : ByteArray) (a : Nat) {k : Nat} (hk : k < 4) :
    lane (bswapNet (word cd a)) k = le64 cd (a + 8 * (3 - k)) := by
  rw [bswapNet_word]; unfold lane
  exact pack4_div_mod (fun k _ => le64_lt _ _) hk

end MlDsaOpt44.Proofs
