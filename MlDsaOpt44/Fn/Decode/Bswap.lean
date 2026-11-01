import MlDsaOpt44.Layout
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The 32-byte reversal network of `dz` (WP8)

`dz` loads each 32-byte calldata window with `CALLDATALOAD` (big-endian) and
reverses its bytes with five mask/shift stages (`bswap256` in
`scripts/gen_opt.py`). `opt44_block` leaves the stages in the shape of
`st1 … st4` plus a final 128-bit rotation; `bsw_word` identifies the result with
the little-endian value `leNat m a 32` of the window.
-/

namespace MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-! ## Stage shapes as `opt44_block` prints them -/

def st1 (x : Nat) : Nat :=
  (450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x) * 256 |||
    450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x / 256
def st2 (x : Nat) : Nat :=
  (1766820105243087041267848467410591083712559083657179364930612997358944255 &&& x) * 65536 |||
    1766820105243087041267848467410591083712559083657179364930612997358944255 &&& x / 65536
def st3 (x : Nat) : Nat :=
  (26959946660873538060741835960174461801791452538186943042387869433855 &&& x) * 4294967296 |||
    26959946660873538060741835960174461801791452538186943042387869433855 &&& x / 4294967296
def st4 (x : Nat) : Nat :=
  (6277101735386680763495507056286727952657427581105975853055 &&& x) * 18446744073709551616 |||
    6277101735386680763495507056286727952657427581105975853055 &&& x / 18446744073709551616

theorem st1_eq (x : Nat) :
    (450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x) * 256 |||
      450552876409790643671482431940419874915447411150352389258589821042463539455 &&& x / 256 =
    st1 x := rfl
theorem st2_eq (x : Nat) :
    (1766820105243087041267848467410591083712559083657179364930612997358944255 &&& x) * 65536 |||
      1766820105243087041267848467410591083712559083657179364930612997358944255 &&& x / 65536 =
    st2 x := rfl
theorem st3_eq (x : Nat) :
    (26959946660873538060741835960174461801791452538186943042387869433855 &&& x) * 4294967296 |||
      26959946660873538060741835960174461801791452538186943042387869433855 &&& x / 4294967296 =
    st3 x := rfl
theorem st4_eq (x : Nat) :
    (6277101735386680763495507056286727952657427581105975853055 &&& x) * 18446744073709551616 |||
      6277101735386680763495507056286727952657427581105975853055 &&& x / 18446744073709551616 =
    st4 x := rfl

/-! ## Each stage swaps bit `i` with bit `i ± c` -/

/-- The partner of bit `i` in a swap stage of width `c`. -/
def sg (c i : Nat) : Nat := if i / c % 2 = 0 then i + c else i - c

theorem m8_bit (j : Nat) : Nat.testBit 450552876409790643671482431940419874915447411150352389258589821042463539455 j =
    decide (j / 8 % 2 = 0 ∧ j + 8 < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 → Nat.testBit 450552876409790643671482431940419874915447411150352389258589821042463539455 j =
        decide (j / 8 % 2 = 0 ∧ j + 8 < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem m16_bit (j : Nat) : Nat.testBit 1766820105243087041267848467410591083712559083657179364930612997358944255 j =
    decide (j / 16 % 2 = 0 ∧ j + 16 < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 → Nat.testBit 1766820105243087041267848467410591083712559083657179364930612997358944255 j =
        decide (j / 16 % 2 = 0 ∧ j + 16 < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem m32_bit (j : Nat) : Nat.testBit 26959946660873538060741835960174461801791452538186943042387869433855 j =
    decide (j / 32 % 2 = 0 ∧ j + 32 < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 → Nat.testBit 26959946660873538060741835960174461801791452538186943042387869433855 j =
        decide (j / 32 % 2 = 0 ∧ j + 32 < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem m64_bit (j : Nat) : Nat.testBit 6277101735386680763495507056286727952657427581105975853055 j =
    decide (j / 64 % 2 = 0 ∧ j + 64 < 256) := by
  by_cases hj : j < 256
  · have h : ∀ j, j < 256 → Nat.testBit 6277101735386680763495507056286727952657427581105975853055 j =
        decide (j / 64 % 2 = 0 ∧ j + 64 < 256) := by decide +kernel
    exact h j hj
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega : 256 ≤ j)))]
    exact (decide_eq_false (by omega)).symm

theorem testBit_hi {x : Nat} (hx : x < 2 ^ 256) {j : Nat} (hj : 256 ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))

/-- One swap stage of width `c` with mask `M` (bits whose `c`-block is even and
whose partner is below 256). -/
theorem stage_bit {M c x : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 32 ∨ c = 64)
    (hM : ∀ j, M.testBit j = decide (j / c % 2 = 0 ∧ j + c < 256))
    {i : Nat} (hi : i < 256) :
    ((M &&& x) * 2 ^ c ||| M &&& x / 2 ^ c).testBit i = x.testBit (sg c i) := by
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, hM, sg]
  by_cases h2 : c ≤ i <;>
  rcases hc with rfl | rfl | rfl | rfl <;> split_ifs with h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.true_and,
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  all_goals (exfalso; omega)

theorem st1_bit (x : Nat) {i : Nat} (hi : i < 256) :
    (st1 x).testBit i = x.testBit (sg 8 i) :=
  stage_bit (M := 450552876409790643671482431940419874915447411150352389258589821042463539455)
    (Or.inl rfl) m8_bit hi
theorem st2_bit (x : Nat) {i : Nat} (hi : i < 256) :
    (st2 x).testBit i = x.testBit (sg 16 i) :=
  stage_bit (M := 1766820105243087041267848467410591083712559083657179364930612997358944255)
    (Or.inr (Or.inl rfl)) m16_bit hi
theorem st3_bit (x : Nat) {i : Nat} (hi : i < 256) :
    (st3 x).testBit i = x.testBit (sg 32 i) :=
  stage_bit (M := 26959946660873538060741835960174461801791452538186943042387869433855)
    (Or.inr (Or.inr (Or.inl rfl))) m32_bit hi
theorem st4_bit (x : Nat) {i : Nat} (hi : i < 256) :
    (st4 x).testBit i = x.testBit (sg 64 i) :=
  stage_bit (M := 6277101735386680763495507056286727952657427581105975853055)
    (Or.inr (Or.inr (Or.inr rfl))) m64_bit hi

theorem and_mul_lt {M x c : Nat} (h : M * 2 ^ c < 2 ^ 256) (hM : M < 2 ^ 256) :
    (M &&& x) * 2 ^ c ||| M &&& x / 2 ^ c < 2 ^ 256 :=
  Nat.or_lt_two_pow (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ Nat.and_le_left) h)
    (Nat.lt_of_le_of_lt Nat.and_le_left hM)

theorem st1_lt (x : Nat) : st1 x < 2 ^ 256 := and_mul_lt (c := 8) (by norm_num) (by norm_num)
theorem st2_lt (x : Nat) : st2 x < 2 ^ 256 := and_mul_lt (c := 16) (by norm_num) (by norm_num)
theorem st3_lt (x : Nat) : st3 x < 2 ^ 256 := and_mul_lt (c := 32) (by norm_num) (by norm_num)
theorem st4_lt (x : Nat) : st4 x < 2 ^ 256 := and_mul_lt (c := 64) (by norm_num) (by norm_num)

theorem st1_mod (x : Nat) :
    st1 x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = st1 x :=
  Nat.mod_eq_of_lt (st1_lt x)
theorem st2_mod (x : Nat) :
    st2 x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = st2 x :=
  Nat.mod_eq_of_lt (st2_lt x)
theorem st3_mod (x : Nat) :
    st3 x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = st3 x :=
  Nat.mod_eq_of_lt (st3_lt x)
theorem st4_mod (x : Nat) :
    st4 x % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = st4 x :=
  Nat.mod_eq_of_lt (st4_lt x)

/-! ## Big- and little-endian byte strings, bit by bit -/

/-- Little-endian value of `w` bytes of `m` from `a`. -/
def leNat (m : ByteArray) : Nat → Nat → Nat
  | _, 0 => 0
  | a, w + 1 => byteAt m a + 256 * leNat m (a + 1) w

theorem leNat_lt (m : ByteArray) : ∀ a w, leNat m a w < 2 ^ (8 * w)
  | _, 0 => by simp [leNat]
  | a, w + 1 => by
    have h1 := leNat_lt m (a + 1) w
    have h2 := byteAt_lt m a
    rw [leNat, show 8 * (w + 1) = 8 * w + 8 by omega, Nat.pow_add]
    have : 256 * (leNat m (a + 1) w + 1) ≤ 256 * 2 ^ (8 * w) := Nat.mul_le_mul_left _ h1
    simp only [Nat.reducePow]; omega

theorem byteAt_lt8 (m : ByteArray) (a : Nat) : byteAt m a < 2 ^ 8 := byteAt_lt m a

theorem leNat_bit (m : ByteArray) : ∀ a w j, (leNat m a w).testBit j =
    if j < 8 * w then (byteAt m (a + j / 8)).testBit (j % 8) else false
  | a, 0, j => by simp [leNat]
  | a, w + 1, j => by
    rw [leNat, Nat.add_comm, show (256 : Nat) = 2 ^ 8 from rfl,
      Nat.testBit_two_pow_mul_add _ (byteAt_lt8 m a), leNat_bit m (a + 1) w]
    by_cases hj : j < 8
    · rw [if_pos hj, if_pos (by omega), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.add_zero]
    · rw [if_neg hj]
      by_cases hj2 : j - 8 < 8 * w
      · rw [if_pos hj2, if_pos (by omega), show a + 1 + (j - 8) / 8 = a + j / 8 by omega,
          show (j - 8) % 8 = j % 8 by omega]
      · rw [if_neg hj2, if_neg (by omega)]

theorem beNat_bit (m : ByteArray) (a : Nat) : ∀ w j, (beNat m a w).testBit j =
    if j < 8 * w then (byteAt m (a + (w - 1 - j / 8))).testBit (j % 8) else false
  | 0, j => by simp [beNat]
  | w + 1, j => by
    rw [beNat, Nat.mul_comm, show (256 : Nat) = 2 ^ 8 from rfl,
      Nat.testBit_two_pow_mul_add _ (byteAt_lt8 m (a + w)), beNat_bit m a w]
    by_cases hj : j < 8
    · rw [if_pos hj, if_pos (by omega), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj,
        show w + 1 - 1 - 0 = w by omega]
    · rw [if_neg hj]
      by_cases hj2 : j - 8 < 8 * w
      · rw [if_pos hj2, if_pos (by omega), show w - 1 - (j - 8) / 8 = w + 1 - 1 - j / 8 by omega,
          show (j - 8) % 8 = j % 8 by omega]
      · rw [if_neg hj2, if_neg (by omega)]

theorem sg_chain : ∀ i, i < 256 →
    sg 128 i < 256 ∧ sg 64 (sg 128 i) < 256 ∧ sg 32 (sg 64 (sg 128 i)) < 256 ∧
      sg 16 (sg 32 (sg 64 (sg 128 i))) < 256 ∧
      sg 8 (sg 16 (sg 32 (sg 64 (sg 128 i)))) = 8 * (31 - i / 8) + i % 8 := by
  decide +kernel

/-- The reversal network maps the big-endian window to the little-endian one. -/
theorem bsw_word (m : ByteArray) (a : Nat) :
    UInt256.ofNat (st4 (st3 (st2 (st1 (word m a)))) * 340282366920938463463374607431768211456 |||
        st4 (st3 (st2 (st1 (word m a)))) / 340282366920938463463374607431768211456) =
      UInt256.ofNat (leNat m a 32) := by
  rw [ofNat_eq_ofNat_iff, Nat.mod_eq_of_lt (leNat_lt m a 32)]
  have hw := word_lt m a
  apply eq_of_testBit_lt (Nat.mod_lt _ (by norm_num)) (leNat_lt m a 32)
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5⟩ := sg_chain i hi
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 from rfl, Nat.testBit_or,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  have e : (decide (128 ≤ i) && (st4 (st3 (st2 (st1 (word m a))))).testBit (i - 128) ||
      (st4 (st3 (st2 (st1 (word m a))))).testBit (i + 128)) =
      (st4 (st3 (st2 (st1 (word m a))))).testBit (sg 128 i) := by
    unfold sg
    by_cases hi' : i < 128
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, if_pos (by omega)]
    · rw [decide_eq_true (by omega), Bool.true_and, testBit_hi (st4_lt _) (j := i + 128) (by omega), Bool.or_false,
        if_neg (by omega)]
  rw [e, st4_bit _ h1, st3_bit _ h2, st2_bit _ h3, st1_bit _ h4, h5,
    word_eq_beNat, beNat_bit, if_pos (by omega), leNat_bit, if_pos (by omega),
    show 32 - 1 - (8 * (31 - i / 8) + i % 8) / 8 = i / 8 by omega,
    show (8 * (31 - i / 8) + i % 8) % 8 = i % 8 by omega]

end MlDsaOpt44.Proofs.DecodeZ
