import MlDsaOpt44.Fn.Sponge.Defs
import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt44.Fn.Sponge.Mem
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `ginit`: one block lemma per stored lane, chained
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

theorem wb_congr {M : ByteArray} {e v a a' : Nat} (he : e = v) (ha : a = a') :
    MachineState.writeBytes M (Data.Bytes.natToBytesPadded e 32) a =
      MachineState.writeBytes M (Data.Bytes.natToBytesPadded v 32) a' := by
  subst he ha; rfl

theorem padTop_eq : padTop = 2 ^ 252 := by
  unfold padTop spread; decide +kernel

theorem or_modL (a b : Nat) :
    (a ||| b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 |||
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.or_mod_two_pow (n := 256)

theorem xor_modL (a b : Nat) :
    (a ^^^ b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 ^^^
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.xor_mod_two_pow (n := 256)

theorem and_modL (a b : Nat) :
    (a &&& b) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 &&&
        b % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  Nat.and_mod_two_pow (n := 256)

theorem xor_left_comm' (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

set_option hygiene false in
/-- Close the value goal of a `ginit` lane block. -/
macro "ginit_value" : tactic => `(tactic| (
  have hkL : keep % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = keep :=
    Nat.mod_eq_of_lt hk
  have hlL : l4 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = l4 :=
    Nat.mod_eq_of_lt hl
  have hnL : (115792089237316195423570985008687907853269984665640564039457584007913129639935 - keep) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      115792089237316195423570985008687907853269984665640564039457584007913129639935 - keep :=
    Nat.mod_eq_of_lt (by omega)
  simp only [ginitWord, padTop_eq, complemented, RHO1, KS, List.mem_cons, List.mem_nil_iff,
    Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
    or_false, or_true, false_or, if_true, if_false, Nat.lt_irrefl, ↓reduceIte,
    or_modL, xor_modL, and_modL, Nat.mod_mod, word_mod, hkL, hlL, hnL,
    Nat.xor_zero, Nat.zero_xor, Nat.zero_or, Nat.or_zero, Nat.zero_mod, Nat.mul_comm, Nat.xor_comm,
    Nat.xor_assoc, xor_left_comm', Nat.and_comm, Nat.or_comm]))

set_option maxRecDepth 100000 in
theorem ginit_lane0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 10911 (wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 0))
      (callState s 10934 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1)) 57 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4560, 4561, 4562, 4563, 4564, 4565, 4566, 4567, 4568, 4569, 4570, 4571, 4572, 4573, 4574, 4575, 4576, 4577, 4578] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 0]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 10934 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1))
      (callState s 10958 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4579, 4580, 4581, 4582, 4583, 4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591, 4592, 4593, 4594, 4595, 4596] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 1]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 10958 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2))
      (callState s 10982 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4597, 4598, 4599, 4600, 4601, 4602, 4603, 4604, 4605, 4606, 4607, 4608, 4609, 4610, 4611, 4612, 4613, 4614] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 2]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 10982 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3))
      (callState s 11004 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4)) 52 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4615, 4616, 4617, 4618, 4619, 4620, 4621, 4622, 4623, 4624, 4625, 4626, 4627, 4628, 4629, 4630] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 3]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11004 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4))
      (callState s 11014 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 4]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11014 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5))
      (callState s 11024 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4639, 4640, 4641, 4642, 4643, 4644, 4645, 4646] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 5]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11024 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6))
      (callState s 11034 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 6]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11034 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7))
      (callState s 11044 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4655, 4656, 4657, 4658, 4659, 4660, 4661, 4662] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 7]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11044 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8))
      (callState s 11056 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 8]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11056 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9))
      (callState s 11068 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4671, 4672, 4673, 4674, 4675, 4676, 4677, 4678] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 9]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11068 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10))
      (callState s 11080 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 10]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11080 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11))
      (callState s 11092 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4687, 4688, 4689, 4690, 4691, 4692, 4693, 4694] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 11]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane12 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11092 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12))
      (callState s 11104 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 12]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane13 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11104 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13))
      (callState s 11116 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 13]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane14 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11116 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14))
      (callState s 11128 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 14]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane15 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11128 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15))
      (callState s 11140 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 15]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane16 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11140 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16))
      (callState s 11186 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17)) 32 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 16]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane17 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11186 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17))
      (callState s 11198 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4737, 4738, 4739, 4740, 4741, 4742, 4743, 4744] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 17]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane18 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11198 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18))
      (callState s 11210 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 18]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane19 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11210 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19))
      (callState s 11222 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4753, 4754, 4755, 4756, 4757, 4758, 4759, 4760] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 19]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane20 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11222 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20))
      (callState s 11270 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21)) 38 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4761, 4762, 4763, 4764, 4765, 4766, 4767, 4768, 4769, 4770, 4771, 4772] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 20]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane21 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11270 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21))
      (callState s 11282 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4773, 4774, 4775, 4776, 4777, 4778, 4779, 4780] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 21]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane22 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11282 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22))
      (callState s 11294 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4781, 4782, 4783, 4784, 4785, 4786, 4787, 4788] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 22]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane23 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11294 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23))
      (callState s 11306 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4789, 4790, 4791, 4792, 4793, 4794, 4795, 4796] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 23]
  opt44_block [word_storeWords_out]
  refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane24 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11306 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24))
      (callState s ret tail (storeWords m 0 (ginitWord m keep amult cmult l4) 25)) 41 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  refine reach_block hs [4797, 4798, 4799, 4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810] (by decide +kernel) ?_
  rw [storeWords_succ _ _ _ 24]
  opt44_block [word_storeWords_out, hj]
  refine wb_congr ?_ (by norm_num); ginit_value

theorem ginitWord_lt (m : ByteArray) {keep amult cmult l4 : Nat} (hk : keep < 2 ^ 256)
    (hl : l4 < 2 ^ 256) (x : Nat) : ginitWord m keep amult cmult l4 x < 2 ^ 256 := by
  have hw := word_lt m (KS + 32 * x)
  have h0 : ∀ a b : Nat, a % 2 ^ 256 ^^^ b % 2 ^ 256 < 2 ^ 256 := fun a b =>
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  unfold ginitWord
  refine Nat.or_lt_two_pow ?_ (Nat.lt_of_le_of_lt Nat.and_le_left hw)
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_) ?_
  · split
    · exact h0 _ _
    · norm_num
  · split <;> omega
  · split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  · split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  · split <;> omega

theorem ginit_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit := by
  refine ⟨storeWords m 0 (ginitWord m keep amult cmult l4) 25, fun x hx => ?_,
    storeWords_mono_frame (by simp [KS]) (by simp [KS]), ?_⟩
  · have := word_storeWords_get (m := m) (base := 0) (ginitWord_lt (amult := amult) (cmult := cmult) m hk hl x) hx
    simpa [KS] using this
  · rw [call_iff, Entry.ginit, Gas.ginit]
    exact ((((((((((((((((((((((((ginit_lane0 hs hr m hk hl).trans (ginit_lane1 hs hr m hk hl)).trans (ginit_lane2 hs hr m hk hl)).trans (ginit_lane3 hs hr m hk hl)).trans (ginit_lane4 hs hr m hk hl)).trans (ginit_lane5 hs hr m hk hl)).trans (ginit_lane6 hs hr m hk hl)).trans (ginit_lane7 hs hr m hk hl)).trans (ginit_lane8 hs hr m hk hl)).trans (ginit_lane9 hs hr m hk hl)).trans (ginit_lane10 hs hr m hk hl)).trans (ginit_lane11 hs hr m hk hl)).trans (ginit_lane12 hs hr m hk hl)).trans (ginit_lane13 hs hr m hk hl)).trans (ginit_lane14 hs hr m hk hl)).trans (ginit_lane15 hs hr m hk hl)).trans (ginit_lane16 hs hr m hk hl)).trans (ginit_lane17 hs hr m hk hl)).trans (ginit_lane18 hs hr m hk hl)).trans (ginit_lane19 hs hr m hk hl)).trans (ginit_lane20 hs hr m hk hl)).trans (ginit_lane21 hs hr m hk hl)).trans (ginit_lane22 hs hr m hk hl)).trans (ginit_lane23 hs hr m hk hl)).trans (ginit_lane24 hs hr m hk hl)


end MlDsaOpt44.Proofs.WP4
