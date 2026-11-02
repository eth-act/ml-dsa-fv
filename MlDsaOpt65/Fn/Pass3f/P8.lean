import MlDsaOpt65.Fn.Group.Defs
import MlDsaOpt65.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f8` (ML-DSA-65): row group 1 (rows 4, 5)

128 iterations at `p = CW + 64 j`, two words each; `ACC + 0x2000` is disjoint
from every region read. `pass3f8_call_aux` states the post as the body of
`p3f8Word` (`Fn/Group.lean`) with `bzl`, `bzr` unfolded.
-/

namespace MlDsaOpt65.Proofs.Pass3fP8

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

/-- Value stored at `p + 0xb900` by a word block (`p` in `CW`). -/
def v (M : ByteArray) (p : Nat) : Nat :=
  let z0 := word M (p + 0x5000)
  let z1 := word M (p + 0x7000)
  ((word M p &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z0 0 +
    (word M p &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * lane z0 1 +
    (word M (p + 0xd900) &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * lane z0 1 +
    (word M (p + 0xd900) &&& (2 ^ 192 - 2 ^ 64)) / 2 ^ (64 * 1) * lane z0 2 +
    (word M (p + 0xf900) &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z0 3 +
    (word M (p + 0xf900) &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * lane z1 0 +
    (word M (p + 0x2000) &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * lane z1 0) % 2 ^ 256

/-- The block's arithmetic (in the normal form of `opt_reach`) is `v`'s. -/
theorem arith {z0 z1 x h g a : Nat} (hz : z0 < 2 ^ 256) :
    ((M64 &&& a) * 2 ^ 64 * (M64 &&& z1) +
      ((2 ^ 192 - 2 ^ 128 &&& g) % 2 ^ 256 / 2 ^ 128 * (M64 &&& z1) +
        ((2 ^ 192 - 2 ^ 64 &&& h) % 2 ^ 256 / 2 ^ 64 * (M64 &&& z0 / 2 ^ 128) +
            ((2 ^ 192 - 2 ^ 128 &&& x) % 2 ^ 256 / 2 ^ 128 * (M64 &&& z0 / 2 ^ 64) +
                (2 ^ 128 - 1 &&& x) * (M64 &&& z0) +
              (M64 &&& h) * 2 ^ 64 * (M64 &&& z0 / 2 ^ 64)) +
          (2 ^ 128 - 1 &&& g) * (z0 / 2 ^ 192)))) % 2 ^ 256 =
    ((x &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z0 0 +
      (x &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * lane z0 1 +
      (h &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * lane z0 1 +
      (h &&& (2 ^ 192 - 2 ^ 64)) / 2 ^ (64 * 1) * lane z0 2 +
      (g &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * lane z0 3 +
      (g &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * lane z1 0 +
      (a &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * lane z1 0) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have hM' : ∀ x, x &&& (2 ^ 64 - 1) = x % 2 ^ 64 := fun x => Nat.and_two_pow_sub_one_eq_mod x 64
  have hL : ∀ x, x &&& (2 ^ 128 - 1) = x % 2 ^ 128 := fun x => Nat.and_two_pow_sub_one_eq_mod x 128
  have hC : ∀ x C, C < 2 ^ 256 → (C &&& x) % 2 ^ 256 = x &&& C := fun x C hC => by
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hC), Nat.and_comm]
  have h3 : z0 / 2 ^ 192 % 2 ^ 64 = z0 / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  have hs : ∀ y, y % 2 ^ 64 * 2 ^ 64 % 2 ^ 256 = y % 2 ^ 64 * 2 ^ 64 := fun y => by
    have := Nat.mod_lt y (show 2 ^ 64 > 0 by norm_num)
    exact Nat.mod_eq_of_lt (by omega)
  have h1 : ∀ y, y % 2 ^ 128 % 2 ^ 256 = y % 2 ^ 128 := fun y => by
    have := Nat.mod_lt y (show 2 ^ 128 > 0 by norm_num)
    exact Nat.mod_eq_of_lt (by omega)
  rw [hC g _ (by norm_num), hC h _ (by norm_num), hC x _ (by norm_num),
    Nat.and_comm (2 ^ 128 - 1) x, Nat.and_comm (2 ^ 128 - 1) g]
  simp only [hM, hM', hL, lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.mul_one, h3, hs, h1]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev K (ret : Nat) (tail : List UInt256) : List UInt256 := wd (2 ^ 192 - 2 ^ 64) :: wd M64 :: wd (2 ^ 192 - 2 ^ 128) :: wd (2 ^ 128 - 1) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 11300 (wd p :: K ret tail) M)
      (callState s 11428 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M p) 32) (p + 0xb900))) 331 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4772, 4773, 4774, 4775, 4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783, 4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791, 4792, 4793, 4794, 4795, 4796, 4797, 4798, 4799, 4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873, 4874, 4875, 4876, 4877, 4878] with [v, M64]
  rw [show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega,
    show 28672 + p = p + 28672 by omega,
    show 47360 + p = p + 47360 by omega,
    show 55552 + p = p + 55552 by omega,
    show 63744 + p = p + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 11428 (wd p :: K ret tail) M)
      (callState s 11558 (wd p :: K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v M (p + 32)) 32) (p + 32 + 0xb900))) 336 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4879, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890, 4891, 4892, 4893, 4894, 4895, 4896, 4897, 4898, 4899, 4900, 4901, 4902, 4903, 4904, 4905, 4906, 4907, 4908, 4909, 4910, 4911, 4912, 4913, 4914, 4915, 4916, 4917, 4918, 4919, 4920, 4921, 4922, 4923, 4924, 4925, 4926, 4927, 4928, 4929, 4930, 4931, 4932, 4933, 4934, 4935, 4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943, 4944, 4945, 4946, 4947, 4948, 4949, 4950, 4951, 4952, 4953, 4954, 4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986] with [v, M64]
  rw [show 32 + p = p + 32 by omega,
    show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega,
    show 28704 + p = p + 32 + 28672 by omega,
    show 47392 + p = p + 32 + 47360 by omega,
    show 55584 + p = p + 32 + 55552 by omega,
    show 63776 + p = p + 32 + 63744 by omega]
  congr 2
  exact arith (word_lt M _)

theorem tl {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 11558 (wd p :: K ret tail) M)
      (callState s 11300 (wd (p + 64) :: K ret tail) M) 28 := by
  opt65_reach [4987, 4988, 4989, 4990, 4991, 4992, 4993]
  simp only [Nat.add_comm, and_self]

theorem ex {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 11558 (wd 0x4fc0 :: K ret tail) M) (callState s ret tail M) 48 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999, 5000] with [hj]

theorem en {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (M : ByteArray) :
    Reach (callState s 11211 (wd ret :: tail) M) (callState s 11300 (wd 0x3000 :: K ret tail) M) 19 := by
  have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this
  opt65_reach [4765, 4766, 4767, 4768, 4769, 4770, 4771] with [M64]

/-- Words outside the stored prefix are untouched. -/
theorem word_storeWords_out {m : ByteArray} {base : Nat} {f : Nat → Nat} {n a : Nat}
    (h : a + 32 ≤ base ∨ base + 32 * n ≤ a) : word (storeWords m base f n) a = word m a :=
  FrameExcept.word (FrameExcept.storeWords m base f n) (by
    simp only [Avoids, List.mem_singleton, forall_eq]; exact h)

/-- `(ACC + 8192)[t]`'s value as a function of `t`. -/
def f (m : ByteArray) (t : Nat) : Nat := v m (CW + 32 * t)

/-- `v` of a memory that differs from `m` only in `(ACC + 8192)[0, n)`, `n ≤ t`. -/
theorem v_store (m : ByteArray) {n t : Nat} (hn : n ≤ t) (ht : t < 256) :
    v (storeWords m (ACC + 8192) (f m) n) (CW + 32 * t) = f m t := by
  unfold f v
  simp only [CW, ACC] at *
  rw [word_storeWords_out (a := 12288 + 32 * t) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 8192) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 28672) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 55552) (by omega),
    word_storeWords_out (a := 12288 + 32 * t + 63744) (by omega)]

theorem next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m (ACC + 8192) (f m) n)
        (Data.Bytes.natToBytesPadded (v (storeWords m (ACC + 8192) (f m) n) p) 32) (p + 0xb900) =
      storeWords m (ACC + 8192) (f m) (n + 1) := by
  rw [storeWords_succ, hp, v_store m (Nat.le_refl n) hn]
  congr 1
  unfold CW ACC; omega

theorem iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 11300 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j)))
      (callState s 11558 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j + 2))) 667 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have h0 := w0 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j)) hp
  rw [next m (by omega) (by omega)] at h0
  have h1 := w1 hs htail (ret := ret) (storeWords m (ACC + 8192) (f m) (2 * j + 1)) hp
  rw [next m (by omega) (by omega)] at h1
  exact h0.trans h1

theorem reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f8 (wd ret :: tail) m)
      (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) Gas.pass3f8 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 11300 (wd (CW + 64 * j) :: K ret tail) (storeWords m (ACC + 8192) (f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 695 := by
    intro j hj
    have h := (iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (tl hs htail (storeWords m (ACC + 8192) (f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m (ACC + 8192) (f m) 256)) 715 :=
    (iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (ex hs hr (storeWords m (ACC + 8192) (f m) 256))
  have hentry : Reach (callState s Entry.pass3f8 (wd ret :: tail) m) (I 0) 19 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW, Entry.pass3f8]
    exact en hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f8; omega)

end MlDsaOpt65.Proofs.Pass3fP8

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f8** with the post stated as the body of `p3f8Word` (`Fn/Group.lean`). -/
theorem pass3f8_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' ((ACC + 8192) + 32 * t) =
      ((word m (CW + 32 * t) &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 0 t +
        (word m (CW + 32 * t) &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * zl m 1 t +
        (word m (HP + 32 * t) &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * zl m 1 t +
        (word m (HP + 32 * t) &&& (2 ^ 192 - 2 ^ 64)) / 2 ^ (64 * 1) * zl m 2 t +
        (word m (HP + 8192 + 32 * t) &&& (2 ^ 128 - 1)) * 2 ^ (64 * 0) % 2 ^ 256 * zl m 3 t +
        (word m (HP + 8192 + 32 * t) &&& (2 ^ 192 - 2 ^ 128)) / 2 ^ (64 * 2) * zl m 4 t +
        (word m (ABUF + 32 * t) &&& (2 ^ 64 - 1)) * 2 ^ (64 * 1) % 2 ^ 256 * zl m 4 t) % 2 ^ 256) ∧
      FrameExcept m m' [((ACC + 8192), (ACC + 8192) + 8192)] ∧
      Call s Entry.pass3f8 [] ret tail m [] m' Gas.pass3f8 := by
  have hv : ∀ t, Pass3fP8.f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m (ACC + 8192) (Pass3fP8.f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold Pass3fP8.f Pass3fP8.v
    simp only [zl, CW, ZH, HP, ACC, ABUF, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add]
    rw [show 12288 + 32 * t + 8192 = 20480 + 32 * t by omega,
      show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 28672 = 40960 + 32 * t by omega,
      show 12288 + 32 * t + 55552 = 67840 + 32 * t by omega,
      show 12288 + 32 * t + 63744 = 76032 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m (ACC + 8192) (Pass3fP8.f m) 256
  · exact Pass3fP8.reach hs hr m

end MlDsaOpt65.Proofs
