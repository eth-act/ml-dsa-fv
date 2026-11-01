import MlDsaOpt44.Fn.Hint.PackIter
/-!
# `pack` (WP10): the stored words, bit by bit

`Xl V j` is lane `j` of a word; the code stores `rep (Xl V_k j)` for the
three stream words `V_k` of a chunk. `Aw M wp n r` is lane `r` of the `n`-th
coefficient word of the chunk at `wp`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOpt44.Proofs.PK

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.L10

/-- Lane `j` of a word. -/
def Xl (V : UInt256) (j : Nat) : Nat := (V.toNat >>> (64 * j)) % 2 ^ 64

/-- Lane `r` of coefficient word `n` of the chunk at `wp`. -/
def Aw (M : ByteArray) (wp n r : Nat) : Nat := lane (word M (32 * n + wp)) r

theorem u_toNat_lt (V : UInt256) : V.toNat < 2 ^ 256 := V.val.isLt

theorem rep_toNat {X : Nat} (hX : X < 2 ^ 64) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 * UInt256.ofNat X).toNat =
      rep X := by
  have e : REP = 6277101735386680764176071790128604879584176795969512275969 := by
    unfold REP pack4; norm_num
  rw [ofNat_mul, toNat_ofNat_of_lt (by omega), rep, e, Nat.mul_comm]

theorem st_lane (V : UInt256) {k j : Nat} (hk : k = 64 * j) (hk' : k < 256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      (UInt256.ofNat 18446744073709551615).land (V.shiftRight (UInt256.ofNat k))).toNat = rep (Xl V j) := by
  rw [← ofNat_toNat V, ofNat_shr _ hk', Nat.mod_eq_of_lt (u_toNat_lt V), ofNat_land,
    show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    rep_toNat (Nat.mod_lt _ (by positivity)), Xl, toNat_ofNat_of_lt (u_toNat_lt V), hk]

theorem st_lane0 (V : UInt256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      (UInt256.ofNat 18446744073709551615).land V).toNat = rep (Xl V 0) := by
  rw [← ofNat_toNat V, ofNat_land, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, rep_toNat (Nat.mod_lt _ (by positivity)), Xl,
    toNat_ofNat_of_lt (u_toNat_lt V)]
  simp

theorem st_lane3 (V : UInt256) :
    (UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 *
      V.shiftRight (UInt256.ofNat 192)).toNat = rep (Xl V 3) := by
  have h := u_toNat_lt V
  have hs : V.toNat >>> 192 < 2 ^ 64 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [← ofNat_toNat V, ofNat_shr _ (by norm_num), Nat.mod_eq_of_lt h, rep_toNat hs, Xl,
    toNat_ofNat_of_lt h, Nat.mod_eq_of_lt hs]

theorem tb_word (M : ByteArray) (wp : Nat) {c : Nat} (q : Nat) (hc : c % 32 = 0) :
    (word M (c + wp)).testBit q = (decide (q < 256) && (Aw M wp (c / 32) (q / 64)).testBit (q % 64)) := by
  have e : 32 * (c / 32) + wp = c + wp := by omega
  unfold Aw; rw [e, ← testBit_pk (lanes_lane _), pk_lanes (word_lt _ _)]

theorem tb_word0 (M : ByteArray) (wp q : Nat) :
    (word M wp).testBit q = (decide (q < 256) && (Aw M wp 0 (q / 64)).testBit (q % 64)) := by
  have := tb_word M wp q (c := 0) (by norm_num)
  simpa using this

theorem tb_hi {a e : Nat} (ha : a < 64) (he : 6 ≤ e) : a.testBit e = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he))

set_option maxHeartbeats 1600000 in
/-- Stream word 0 of a chunk. -/
theorem v0_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q2o0 M wp fp) j).testBit b = (Aw M wp (b / 6) j).testBit (b % 6) := by
  have hz : ∀ n r e, n < 32 → r < 4 → 6 ≤ e → (Aw M wp n r).testBit e = false :=
    fun n r e hn hr he => tb_hi (hA n r hn hr) he
  simp only [Xl, q2o0, q1o0, q1o1, pk2o0, pk1o0, pk1o1, ofNat_lor, ofNat_land,
    ofNat_shl _ (show (6 : Nat) < 256 by norm_num), ofNat_shl _ (show (12 : Nat) < 256 by norm_num),
    ofNat_shl _ (show (18 : Nat) < 256 by norm_num), ofNat_shl _ (show (24 : Nat) < 256 by norm_num),
    ofNat_shl _ (show (30 : Nat) < 256 by norm_num), ofNat_shl _ (show (36 : Nat) < 256 by norm_num),
    ofNat_shl _ (show (42 : Nat) < 256 by norm_num), ofNat_shl _ (show (48 : Nat) < 256 by norm_num),
    ofNat_shl _ (show (54 : Nat) < 256 by norm_num), ofNat_shl _ (show (60 : Nat) < 256 by norm_num),
    EvmProof.Word.word_toNat_ofNat]
  interval_cases j <;> interval_cases b <;>
    simp (disch := first | decide | omega) only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_lit, tb_word M wp, tb_word0 M wp, hz,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceLeDiff, decide_true, decide_false, ge_iff_le, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, Nat.zero_testBit, Nat.zero_add]

set_option maxHeartbeats 1600000 in
/-- Stream word 1 of a chunk. -/
theorem v1_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (hq2 : ∀ n r, n < 32 → Aw (qm2 M wp fp) wp n r = Aw M wp n r)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q4o0 M wp fp) j).testBit b = (Aw M wp ((64 + b) / 6) j).testBit ((64 + b) % 6) := by
  have hz : ∀ n r e, n < 32 → r < 4 → 6 ≤ e → (Aw M wp n r).testBit e = false :=
    fun n r e hn hr he => tb_hi (hA n r hn hr) he
  simp (disch := decide) only [Xl, q4o0, q3o0, q3o1, q2o0, q2o1, q1o0, q1o1, pk4o0, pk3o0, pk3o1, pk2o0,
    pk2o1, pk1o0, pk1o1, ofNat_lor, ofNat_land, ofNat_shl, ofNat_shr, EvmProof.Word.word_toNat_ofNat]
  interval_cases j <;> interval_cases b <;>
    simp (disch := first | decide | omega) only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_lit, tb_word M wp, tb_word0 M wp,
      tb_word (qm2 M wp fp) wp, hq2, hz,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceLeDiff, decide_true, decide_false, ge_iff_le, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, Nat.zero_testBit, Nat.zero_add]

set_option maxHeartbeats 1600000 in
/-- Stream word 2 of a chunk. -/
theorem v2_bits (M : ByteArray) (wp fp : Nat) (hA : ∀ n r, n < 32 → r < 4 → Aw M wp n r < 64)
    (hq2 : ∀ n r, n < 32 → Aw (qm2 M wp fp) wp n r = Aw M wp n r)
    (hq4 : ∀ n r, n < 32 → Aw (qm4 M wp fp) wp n r = Aw M wp n r)
    {j : Nat} (hj : j < 4) {b : Nat} (hb : b < 64) :
    (Xl (q5o0 M wp fp) j).testBit b = (Aw M wp ((128 + b) / 6) j).testBit ((128 + b) % 6) := by
  have hz : ∀ n r e, n < 32 → r < 4 → 6 ≤ e → (Aw M wp n r).testBit e = false :=
    fun n r e hn hr he => tb_hi (hA n r hn hr) he
  simp (disch := decide) only [Xl, q5o0, q4o1, q3o0, pk5o0, pk4o1, pk3o0, ofNat_lor, ofNat_land, ofNat_shl,
    ofNat_shr, EvmProof.Word.word_toNat_ofNat]
  interval_cases j <;> interval_cases b <;>
    simp (disch := first | decide | omega) only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_lit,
      tb_word (qm2 M wp fp) wp, tb_word (qm4 M wp fp) wp, hq2, hq4, hz,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceLeDiff, decide_true, decide_false, ge_iff_le, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, Nat.zero_testBit, Nat.zero_add]

end MlDsaOpt44.Proofs.PK
