import MlDsaOpt44.Fn.Ct.TBuildBlocks
import MlDsaOpt44.Fn.Decode.ZMath
set_option linter.unusedSimpArgs false
/-!
# `tbuild` (WP10): the stored words, bit by bit, and the table invariant

* `tbW_bit`: bit `i < 256` of the stored word is bit `10 (i / 64) + i % 16 + sh` of
  window `i / 16 % 4` when `i % 16 < 10` (cell `4k + r` holds field `k` of row `r`);
* `tbW_cell`, `tbN_cell`: the 16-bit cells of the `P` and `N` words;
* `le_t1v`: a field of the little-endian window is the `t1` coefficient;
* `Inv`: after the words `v < n`, the table entries of every `v < n` are in place;
  `inv_visit` is one word-loop visit, `inv_table` the final `TTable` body.
-/

namespace MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ
open MlDsa44

/-- Window `r` of four. -/
def sel (V0 V1 V2 V3 r : Nat) : Nat := if r = 0 then V0 else if r = 1 then V1 else if r = 2 then V2 else V3

theorem tb_hi {m K j : Nat} (hm : m < 2 ^ K) (hj : K ≤ j) : m.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj))

theorem m40_bit (j : Nat) : Nat.testBit 1099511627775 j = decide (j < 40) := by
  rw [show (1099511627775 : Nat) = 2 ^ 40 - 1 from rfl, Nat.testBit_two_pow_sub_one]

/-! ## Stages -/

set_option maxHeartbeats 1600000 in
theorem tgW_bit (sh V0 V1 V2 V3 i : Nat) :
    (tgW sh V0 V1 V2 V3).testBit i =
      (decide (i < 256) && (decide (i % 64 < 40) && (sel V0 V1 V2 V3 (i / 64)).testBit (i % 64 + sh))) := by
  unfold tgW
  simp only [Nat.testBit_or, Nat.testBit_and, m40_bit, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    show (6277101735386680763835789423207666416102355444464034512896 : Nat) = 2 ^ 192 from rfl,
    show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 from rfl,
    show (18446744073709551616 : Nat) = 2 ^ 64 from rfl]
  by_cases hi : i < 256
  · interval_cases i <;>
      simp only [sel, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
        Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false, ↓reduceIte, Bool.true_and, Bool.and_true,
        Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  · simp (disch := omega) only [decide_eq_false, decide_eq_true, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]

theorem ts1_bit (x i : Nat) : (ts1 x).testBit i =
    (Nat.testBit 6582011952183088782295924477334101861609978183833731334774194175 i && x.testBit i ||
      (decide (12 ≤ i) && (Nat.testBit 6901739764772334502984731304745083193639544484091638668092185431244800 (i - 12) &&
        x.testBit (i - 12)))) := by
  unfold ts1
  simp only [show (4096 : Nat) = 2 ^ 12 from rfl, Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow]

theorem ts2_bit (x i : Nat) : (ts2 x).testBit i =
    (Nat.testBit 27580025446916579586740047030762717305835781530194468456916412547466239 i && x.testBit i ||
      (decide (6 ≤ i) && (Nat.testBit 28241946057642577496821808159501022521175840286919135699882406448605428736 (i - 6) &&
        x.testBit (i - 6)))) := by
  unfold ts2
  simp only [show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_or, Nat.testBit_and, Nat.testBit_mul_two_pow]

/-- A delta swap below bit 256: bit `i` comes from `i + d` (mask bit), `i - d`
(mask bit at `i - d`) or `i`. -/
theorem tdsw_bit {m d x i : Nat} (hm : ∀ j, m.testBit j = true → m.testBit (j + d) = false) (hi : i < 256) :
    (tdsw m d x).testBit i =
      if m.testBit i then (decide (i + d < 256) && x.testBit (i + d))
      else if d ≤ i ∧ m.testBit (i - d) = true then x.testBit (i - d) else x.testBit i := by
  unfold tdsw
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow]
  by_cases h2 : d ≤ i
  · have e : i - d + d = i := by omega
    rw [e, decide_eq_true hi, decide_eq_true h2]
    cases h3 : m.testBit (i - d)
    · cases m.testBit i <;> cases x.testBit i <;> cases x.testBit (i + d) <;> cases decide (i + d < 256) <;>
        simp
    · have h1 := hm _ h3
      rw [e] at h1
      rw [h1]
      cases x.testBit i <;> cases x.testBit (i - d) <;> simp [h2]
  · rw [decide_eq_false h2]
    have hn : ¬(d ≤ i ∧ m.testBit (i - d) = true) := fun h => h2 h.1
    rw [if_neg hn]
    cases m.testBit i <;> cases x.testBit i <;> cases x.testBit (i + d) <;> cases decide (i + d < 256) <;> simp

theorem tdsw_hi {m d x i K : Nat} (hm : m < 2 ^ K) (hK : K + d ≤ 256) (hi : 256 ≤ i) :
    (tdsw m d x).testBit i = x.testBit i := by
  unfold tdsw
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow, tb_hi hm (j := i) (by omega), tb_hi hm (j := i - d) (by omega),
    Bool.false_and, Bool.and_false, Bool.false_xor]

theorem m48_ok : ∀ j, Nat.testBit 6277005955876855982367846414099012818794836107166352343040 j = true →
    Nat.testBit 6277005955876855982367846414099012818794836107166352343040 (j + 48) = false := by
  intro j hj
  by_cases h : j < 256
  · have k : ∀ j, j < 256 → Nat.testBit 6277005955876855982367846414099012818794836107166352343040 j = true →
        Nat.testBit 6277005955876855982367846414099012818794836107166352343040 (j + 48) = false := by
      decide +kernel
    exact k j h hj
  · exact tb_hi (K := 256) (by norm_num) (by omega)

theorem m96_ok : ∀ j, Nat.testBit 340282366841710300967557013907638845440 j = true →
    Nat.testBit 340282366841710300967557013907638845440 (j + 96) = false := by
  intro j hj
  by_cases h : j < 256
  · have k : ∀ j, j < 256 → Nat.testBit 340282366841710300967557013907638845440 j = true →
        Nat.testBit 340282366841710300967557013907638845440 (j + 96) = false := by
      decide +kernel
    exact k j h hj
  · exact tb_hi (K := 256) (by norm_num) (by omega)

theorem T48 (x : Nat) {i : Nat} (hi : i < 256) :
    (tdsw 6277005955876855982367846414099012818794836107166352343040 48 x).testBit i =
      if Nat.testBit 6277005955876855982367846414099012818794836107166352343040 i then
        (decide (i + 48 < 256) && x.testBit (i + 48))
      else if 48 ≤ i ∧ Nat.testBit 6277005955876855982367846414099012818794836107166352343040 (i - 48) = true then
        x.testBit (i - 48) else x.testBit i := tdsw_bit m48_ok hi

theorem T96 (x : Nat) {i : Nat} (hi : i < 256) :
    (tdsw 340282366841710300967557013907638845440 96 x).testBit i =
      if Nat.testBit 340282366841710300967557013907638845440 i then
        (decide (i + 96 < 256) && x.testBit (i + 96))
      else if 96 ≤ i ∧ Nat.testBit 340282366841710300967557013907638845440 (i - 96) = true then
        x.testBit (i - 96) else x.testBit i := tdsw_bit m96_ok hi

set_option maxHeartbeats 4000000 in
theorem tbW_bit_lo (sh V0 V1 V2 V3 : Nat) : ∀ i, i < 256 → (tbW sh V0 V1 V2 V3).testBit i =
    (decide (i % 16 < 10) && (sel V0 V1 V2 V3 (i / 16 % 4)).testBit (10 * (i / 64) + i % 16 + sh)) := by
  intro i hi
  unfold tbW
  interval_cases i <;>
    simp (disch := first | decide | omega) only [T48, T96, ts2_bit, ts1_bit, tgW_bit, testBit_lit, sel,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceLeDiff, Nat.reduceEqDiff, decide_true, decide_false, ↓reduceIte, ge_iff_le, Bool.true_and,
      Bool.and_true, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, and_true, and_false,
      true_and, false_and, Bool.false_eq_true, not_false_eq_true, Nat.zero_add]

theorem tbW_bit_hi (sh V0 V1 V2 V3 : Nat) {i : Nat} (hi : 256 ≤ i) : (tbW sh V0 V1 V2 V3).testBit i = false := by
  unfold tbW
  rw [tdsw_hi (K := 192) (by norm_num) (by norm_num) hi, tdsw_hi (K := 128) (by norm_num) (by norm_num) hi,
    ts2_bit, tb_hi (m := 27580025446916579586740047030762717305835781530194468456916412547466239) (K := 256)
      (by norm_num) hi,
    tb_hi (m := 28241946057642577496821808159501022521175840286919135699882406448605428736) (K := 250)
      (by norm_num) (by omega)]
  simp

theorem tbW_lt (sh V0 V1 V2 V3 : Nat) : tbW sh V0 V1 V2 V3 < 2 ^ 256 :=
  Nat.lt_pow_two_of_testBit _ fun _ hi => tbW_bit_hi sh V0 V1 V2 V3 hi

/-- Cell `f = 4k + r` of the stored word is field `k` of window `r`. -/
theorem tbW_cell (sh V0 V1 V2 V3 : Nat) {f : Nat} (hf : f < 16) :
    tbW sh V0 V1 V2 V3 / 2 ^ (16 * f) % 2 ^ 16 = sel V0 V1 V2 V3 (f % 4) / 2 ^ (10 * (f / 4) + sh) % 2 ^ 10 := by
  apply eq_of_testBit_lt (n := 16) (Nat.mod_lt _ (by norm_num))
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  intro b hb
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, tbW_bit_lo _ _ _ _ _ _ (by omega),
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    show (b + 16 * f) % 16 = b by omega, show (b + 16 * f) / 16 % 4 = f % 4 by omega,
    show 10 * ((b + 16 * f) / 64) + b + sh = b + (10 * (f / 4) + sh) by omega, decide_eq_true hb, Bool.true_and]

theorem c_bit : ∀ j, j < 256 →
    Nat.testBit 1807512127714571876376182462255096204072559614144354879260930929123294905343 j =
      decide (j % 16 < 10) := by
  decide +kernel

theorem xor1023 : ∀ y, y < 1024 → 1023 ^^^ y = 1023 - y := by decide +kernel

/-- Cell `f` of the `N` word is `1023 −` cell `f` of the `P` word. -/
theorem tbN_cell (X : Nat) {f : Nat} (hf : f < 16) (hc : X / 2 ^ (16 * f) % 2 ^ 16 < 1024) :
    tbN X / 2 ^ (16 * f) % 2 ^ 16 = 1023 - X / 2 ^ (16 * f) % 2 ^ 16 := by
  rw [← xor1023 _ hc]
  apply eq_of_testBit_lt (n := 16) (Nat.mod_lt _ (by norm_num))
    (Nat.xor_lt_two_pow (by norm_num) (Nat.mod_lt _ (by norm_num)))
  intro b hb
  rw [tbN, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, c_bit _ (by omega),
    show (b + 16 * f) % 16 = b by omega, decide_eq_true hb, decide_eq_true (show b + 16 * f < 256 by omega),
    show (1023 : Nat) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp

/-! ## Calldata fields -/

/-- Field `k` of word-loop visit `j` of window `r` is coefficient `4 (v0 + j) + k` of `t1_r`. -/
theorem le_t1v {cd : ByteArray} (hcd : HDR ≤ cd.size) {a v0 j k r : Nat} (ha : a = 32 + 5 * v0 + 320 * r)
    (hv : v0 + j < 64) (hj : j ≤ 5) (hk : k < 4) (hr : r < 4) :
    leNat cd a 32 / 2 ^ (10 * k + 40 * j) % 2 ^ 10 = t1v cd r (4 * (v0 + j) + k) := by
  unfold t1v
  apply div_mod_eq_bitsToInteger
  intro t ht
  have hf : 32 + 320 * r + 320 ≤ cd.size := by simp only [HDR] at hcd; omega
  rw [testBit_eq_div_mod, leNat_bit, if_pos (by omega), Fips204.bit,
    show 32 + 320 * (r + 1) = 32 + 320 * r + 320 by omega,
    byteAt_extract hf (by omega), testBit_eq_div_mod,
    show a + (10 * k + 40 * j + t) / 8 = 32 + 320 * r + (10 * (4 * (v0 + j) + k) + t) / 8 by omega,
    show (10 * k + 40 * j + t) % 8 = (10 * (4 * (v0 + j) + k) + t) % 8 by omega]

theorem t1v_lt (cd : ByteArray) (r i : Nat) : t1v cd r i < 2 ^ 10 :=
  MlDsa44.Proofs.Decode.bitsToInteger_lt _ _ 10

/-! ## Memory -/

theorem byte_of_word {m : ByteArray} {A X : Nat} (h : word m A = X) {q : Nat} (hq : q < 32) :
    byteAt m (A + q) = X / 2 ^ (8 * (31 - q)) % 2 ^ 8 := by
  apply eq_of_testBit_lt (n := 8) (byteAt_lt8 m _) (Nat.mod_lt _ (by norm_num))
  intro b hb
  have e := beNat_bit m A 32 (8 * (31 - q) + b)
  rw [← word_eq_beNat, h, if_pos (by omega), show 32 - 1 - (8 * (31 - q) + b) / 8 = q by omega,
    show (8 * (31 - q) + b) % 8 = b by omega] at e
  rw [← e, Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and, Nat.testBit_div_two_pow, Nat.add_comm]

theorem be16_of_word {m : ByteArray} {A X : Nat} (h : word m A = X) {f : Nat} (hf : f < 16) :
    be16 m (A + 30 - 2 * f) = X / 2 ^ (16 * f) % 2 ^ 16 := by
  unfold be16
  rw [show A + 30 - 2 * f = A + (30 - 2 * f) by omega, Nat.add_assoc,
    show 30 - 2 * f + 1 = 31 - 2 * f by omega, byte_of_word h (by omega), byte_of_word h (by omega),
    show 8 * (31 - (30 - 2 * f)) = 16 * f + 8 by omega, show 8 * (31 - (31 - 2 * f)) = 16 * f by omega,
    Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize X / 2 ^ (16 * f) = Y
  simp only [Nat.reducePow]
  omega

theorem be16_frame {M : ByteArray} {a b v : Nat} (h : a + 2 ≤ b ∨ b + 32 ≤ a) :
    be16 (MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) b) a = be16 M a := by
  unfold be16
  rw [byteAt_writeBytes_of_not_mem (by rw [natToBytesPadded_size]; omega),
    byteAt_writeBytes_of_not_mem (by rw [natToBytesPadded_size]; omega)]

theorem be16_st3 {M : ByteArray} {pa X a : Nat} (h1 : a + 2 ≤ pa ∨ pa + 32 ≤ a)
    (h2 : a + 2 ≤ 2048 + pa ∨ 2048 + pa + 32 ≤ a) (h3 : a + 2 ≤ pa - 2048 ∨ pa - 2048 + 32 ≤ a) :
    be16 (st3 M pa X) a = be16 M a := by
  unfold st3
  rw [be16_frame h3, be16_frame h2, be16_frame h1]

theorem word_st3_P (M : ByteArray) {pa X : Nat} (hpa : 2048 ≤ pa) (hX : X < 2 ^ 256) :
    word (st3 M pa X) pa = X := by
  unfold st3
  rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ hX]

theorem tbN_lt (X : Nat) : tbN X < 2 ^ 256 := Nat.mod_lt _ (by norm_num)

theorem word_st3_N1 (M : ByteArray) {pa X : Nat} (hpa : 2048 ≤ pa) :
    word (st3 M pa X) (2048 + pa) = tbN X := by
  unfold st3
  rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (tbN_lt X)]

theorem word_st3_N2 (M : ByteArray) (pa X : Nat) :
    word (st3 M pa X) (pa - 2048) = tbN X := by
  unfold st3
  rw [word_mstore _ _ _ (tbN_lt X)]

theorem frame_st3 (M : ByteArray) {pa X : Nat} (hpa : 22528 ≤ pa) (hpa2 : pa ≤ 24544) :
    FrameExcept M (st3 M pa X) [(20480, 26624)] := by
  unfold st3
  refine FrameExcept.mono ((FrameExcept.mstore M pa X).trans
    ((FrameExcept.mstore _ (2048 + pa) (tbN X)).trans (FrameExcept.mstore _ (pa - 2048) (tbN X)))) ?_
  intro r hr
  refine ⟨(20480, 26624), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> constructor <;> simp only <;> omega

/-! ## The table invariant -/

/-- The table entries of coefficient word `v` (`P` copy, upper and lower `N` copies). -/
def Good (cd M : ByteArray) (v : Nat) : Prop :=
  ∀ k, k < 4 → ∀ r, r < 4 →
    be16 M (24574 - 32 * v - 8 * k - 2 * r) = t1v cd r (4 * v + k) ∧
    be16 M (26622 - 32 * v - 8 * k - 2 * r) = 1023 - t1v cd r (4 * v + k) ∧
    be16 M (22526 - 32 * v - 8 * k - 2 * r) = 1023 - t1v cd r (4 * v + k)

/-- Words `v < n` done, nothing outside the table touched. -/
def Inv (cd m M : ByteArray) (n : Nat) : Prop :=
  FrameExcept m M [(20480, 26624)] ∧ ∀ v, v < n → Good cd M v

theorem inv_zero (cd m : ByteArray) : Inv cd m m 0 :=
  ⟨FrameExcept.refl m _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- One word-loop visit: word `v0 + j` of the chunk with windows at `off = 32 + 5 v0`. -/
theorem inv_visit {cd m M : ByteArray} (hcd : HDR ≤ cd.size) {n v0 j off : Nat} (hI : Inv cd m M n)
    (hoff : off = 32 + 5 * v0) (hn : v0 + j ≤ n) (hn64 : n ≤ 64) (hv : v0 + j < 64) (hj : j ≤ 5) :
    Inv cd m (st3 M (24544 - 32 * (v0 + j)) (tbW (40 * j) (leNat cd off 32) (leNat cd (320 + off) 32)
      (leNat cd (640 + off) 32) (leNat cd (960 + off) 32))) (max n (v0 + j + 1)) := by
  generalize hX : tbW (40 * j) (leNat cd off 32) (leNat cd (320 + off) 32)
      (leNat cd (640 + off) 32) (leNat cd (960 + off) 32) = X
  have hXlt : X < 2 ^ 256 := hX ▸ tbW_lt _ _ _ _ _
  -- the cells of `X`
  have hcell : ∀ k, k < 4 → ∀ r, r < 4 →
      X / 2 ^ (16 * (4 * k + r)) % 2 ^ 16 = t1v cd r (4 * (v0 + j) + k) := by
    intro k hk r hr
    rw [← hX, tbW_cell _ _ _ _ _ (by omega), show (4 * k + r) % 4 = r by omega,
      show (4 * k + r) / 4 = k by omega]
    interval_cases r
    · simp only [sel, ↓reduceIte]
      exact le_t1v hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, ↓reduceIte, Nat.one_ne_zero]
      exact le_t1v hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
      exact le_t1v hcd (by omega) hv hj hk (by norm_num)
    · simp only [sel, Nat.reduceEqDiff, ↓reduceIte]
      exact le_t1v hcd (by omega) hv hj hk (by norm_num)
  set pa := 24544 - 32 * (v0 + j) with hpa
  have wP := word_st3_P M (pa := pa) (X := X) (by omega) hXlt
  have wN1 := word_st3_N1 M (pa := pa) (X := X) (by omega)
  have wN2 := word_st3_N2 M pa X
  refine ⟨hI.1.trans (frame_st3 M (by omega) (by omega)) |>.mono ?_, fun w hw => ?_⟩
  · intro r hr; exact ⟨(20480, 26624), by simp, by simp at hr; subst hr; simp⟩
  intro k hk r hr
  by_cases hwv : w = v0 + j
  · subst hwv
    have hc := hcell k hk r hr
    have hc' : X / 2 ^ (16 * (4 * k + r)) % 2 ^ 16 < 1024 := by rw [hc]; exact t1v_lt _ _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [show 24574 - 32 * (v0 + j) - 8 * k - 2 * r = pa + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wP (by omega), hc]
    · rw [show 26622 - 32 * (v0 + j) - 8 * k - 2 * r = 2048 + pa + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wN1 (by omega), tbN_cell X (by omega) hc', hc]
    · rw [show 22526 - 32 * (v0 + j) - 8 * k - 2 * r = pa - 2048 + 30 - 2 * (4 * k + r) by omega,
        be16_of_word wN2 (by omega), tbN_cell X (by omega) hc', hc]
  · have hw' : w < n := by omega
    obtain ⟨g1, g2, g3⟩ := hI.2 w hw' k hk r hr
    refine ⟨?_, ?_, ?_⟩
    · rw [be16_st3 (by omega) (by omega) (by omega), g1]
    · rw [be16_st3 (by omega) (by omega) (by omega), g2]
    · rw [be16_st3 (by omega) (by omega) (by omega), g3]

/-- The final table. -/
theorem inv_table {cd m M : ByteArray} (hI : Inv cd m M 64) :
    ∀ e, e < 768 → ∀ r, r < 4 → be16 M (TT + 6142 - 8 * e - 2 * r) =
      (if 256 ≤ e ∧ e < 512 then t1v cd r (e - 256) else 1023 - t1v cd r (e % 256)) := by
  intro e he r hr
  split_ifs with h
  · obtain ⟨g, -, -⟩ := hI.2 ((e - 256) / 4) (by omega) ((e - 256) % 4) (by omega) r hr
    rw [show TT + 6142 - 8 * e - 2 * r = 24574 - 32 * ((e - 256) / 4) - 8 * ((e - 256) % 4) - 2 * r by
      unfold TT; omega, g, show 4 * ((e - 256) / 4) + (e - 256) % 4 = e - 256 by omega]
  · by_cases hlo : e < 256
    · obtain ⟨-, g, -⟩ := hI.2 (e / 4) (by omega) (e % 4) (by omega) r hr
      rw [show TT + 6142 - 8 * e - 2 * r = 26622 - 32 * (e / 4) - 8 * (e % 4) - 2 * r by unfold TT; omega,
        g, show 4 * (e / 4) + e % 4 = e % 256 by omega]
    · obtain ⟨-, -, g⟩ := hI.2 ((e - 512) / 4) (by omega) ((e - 512) % 4) (by omega) r hr
      rw [show TT + 6142 - 8 * e - 2 * r = 22526 - 32 * ((e - 512) / 4) - 8 * ((e - 512) % 4) - 2 * r by
        unfold TT; omega, g, show 4 * ((e - 512) / 4) + (e - 512) % 4 = e % 256 by omega]

end MlDsaOpt44.Proofs.TB
