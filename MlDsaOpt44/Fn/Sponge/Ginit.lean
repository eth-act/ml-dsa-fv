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
    Reach (callState s 11084 (wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 0))
      (callState s 11107 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1)) 57 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11107 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 1))
      (callState s 11131 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11131 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 2))
      (callState s 11155 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3)) 58 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741, 4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11155 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 3))
      (callState s 11177 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4)) 52 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4752, 4753, 4754, 4755, 4756, 4757, 4758, 4759, 4760, 4761, 4762, 4763, 4764, 4765, 4766, 4767] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11177 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 4))
      (callState s 11187 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4768, 4769, 4770, 4771, 4772, 4773, 4774, 4775] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11187 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 5))
      (callState s 11197 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11197 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 6))
      (callState s 11207 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11207 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 7))
      (callState s 11217 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4792, 4793, 4794, 4795, 4796, 4797, 4798, 4799] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11217 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 8))
      (callState s 11229 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11229 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 9))
      (callState s 11241 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11241 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 10))
      (callState s 11253 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11253 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 11))
      (callState s 11265 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane12 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11265 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 12))
      (callState s 11277 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane13 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11277 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 13))
      (callState s 11289 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane14 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11289 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 14))
      (callState s 11301 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane15 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11301 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 15))
      (callState s 11313 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane16 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11313 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 16))
      (callState s 11359 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17)) 32 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane17 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11359 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 17))
      (callState s 11371 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18)) 24 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4874, 4875, 4876, 4877, 4878, 4879, 4880, 4881] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane18 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11371 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 18))
      (callState s 11383 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane19 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11383 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 19))
      (callState s 11395 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4890, 4891, 4892, 4893, 4894, 4895, 4896, 4897] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane20 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11395 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 20))
      (callState s 11443 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21)) 38 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4898, 4899, 4900, 4901, 4902, 4903, 4904, 4905, 4906, 4907, 4908, 4909] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane21 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11443 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 21))
      (callState s 11455 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4910, 4911, 4912, 4913, 4914, 4915, 4916, 4917] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane22 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11455 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 22))
      (callState s 11467 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4918, 4919, 4920, 4921, 4922, 4923, 4924, 4925] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane23 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11467 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 23))
      (callState s 11479 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24)) 23 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  refine reach_block hs [4926, 4927, 4928, 4929, 4930, 4931, 4932, 4933] (by decide +kernel) ?_
  opt44_block [word_storeWords_out]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

set_option maxRecDepth 100000 in
theorem ginit_lane24 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    Reach (callState s 11479 (wd (2 ^ 256 - 1 - keep) :: wd l4 :: wd cmult :: wd amult :: wd keep :: wd ret :: tail) (storeWords m 0 (ginitWord m keep amult cmult l4) 24))
      (callState s ret tail (storeWords m 0 (ginitWord m keep amult cmult l4) 25)) 41 := by
  have := hr.depth; simp only [Stack.ginit, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  refine reach_block hs [4934, 4935, 4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943, 4944, 4945, 4946, 4947] (by decide +kernel) ?_
  opt44_block [word_storeWords_out, hj]
  rw [storeWords_succ]; refine wb_congr ?_ (by norm_num); ginit_value

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
