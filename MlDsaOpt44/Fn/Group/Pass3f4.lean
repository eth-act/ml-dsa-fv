import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOpt44.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `pass3f4`: the fused accumulation pass (WP C)

128 iterations at `p = CW + 64 j`, two words each: `ACC[t] := f4v m (CW + 32 t)`
(reads of the original memory: `ACC` is disjoint from every region read).
`pass3f4_call_aux` states the post as the body of `acc4Word` (`Fn/Group.lean`).
-/

namespace MlDsaOpt44.Proofs.GroupP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

/-- Value stored at `p + 0x7900` by a word block reading `M` at `p + o` (`p` in `CW`). -/
def f4v (M : ByteArray) (p : Nat) : Nat :=
  let z := word M (p + 0x5000)
  (word M p * lane z 0 + word M (p + 0x9900) * lane z 1 +
    word M (p + 0xd700) / 2 ^ 64 * lane z 2 +
    ((word M (p + 0xf700) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
      (M64 * 2 ^ 192)) +
    word M (p + 0x2000) / 2 ^ 64 * lane z 3) % 2 ^ 256

theorem and_mod_of_lt {a b n : Nat} (hb : b < 2 ^ n) : a % 2 ^ n &&& b = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < n
  · simp [hj]
  · have : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

/-- The block's arithmetic (in the normal form of `opt44_reach`) is `f4v`'s. -/
theorem f4_arith {z c h s1 s2 a : Nat} (hz : z < 2 ^ 256) :
    (a / 2 ^ 64 * (z / 2 ^ 192) +
      ((M64 * 2 ^ 192 &&& ((2 ^ 256 - 2 ^ 128) &&& s2) * (z / 2 ^ 128)) +
        (s1 / 2 ^ 64 * (M64 &&& z / 2 ^ 128) +
          (h * (M64 &&& z / 2 ^ 64) + c * (M64 &&& z))))) % 2 ^ 256 =
    (c * lane z 0 + h * lane z 1 + s1 / 2 ^ 64 * lane z 2 +
      ((s2 &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192)) +
      a / 2 ^ 64 * lane z 3) % 2 ^ 256 := by
  have hM : ∀ x, M64 &&& x = x % 2 ^ 64 := fun x => by
    rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64
  have h3 : z / 2 ^ 192 % 2 ^ 64 = z / 2 ^ 192 := Nat.mod_eq_of_lt (by omega)
  rw [and_mod_of_lt (by unfold M64; norm_num), hM, hM, hM]
  simp only [lane, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, h3]
  rw [Nat.and_comm (M64 * 2 ^ 192), Nat.and_comm (2 ^ 256 - 2 ^ 128)]
  congr 1
  ring

/-- The loop's constant stack below the pointer. -/
abbrev f4K (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd (M64 * 2 ^ 192) :: wd (2 ^ 256 - 2 ^ 128) :: wd M64 :: wd ret :: tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f4_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 10308 (wd p :: f4K ret tail) M)
      (callState s 10395 (wd p :: f4K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f4v M p) 32) (p + 0x7900))) 214 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4165, 4166, 4167, 4168, 4169, 4170, 4171, 4172, 4173, 4174, 4175, 4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223, 4224, 4225, 4226, 4227, 4228, 4229, 4230, 4231, 4232, 4233] with [f4v, M64]
  rw [show 30976 + p = p + 30976 by omega, show 8192 + p = p + 8192 by omega,
    show 20480 + p = p + 20480 by omega, show 63232 + p = p + 63232 by omega,
    show 55040 + p = p + 55040 by omega, show 39168 + p = p + 39168 by omega]
  congr 2
  exact f4_arith (word_lt M _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem f4_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 ≤ 0x5000) :
    Reach (callState s 10395 (wd p :: f4K ret tail) M)
      (callState s 10484 (wd p :: f4K ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (f4v M (p + 32)) 32) (p + 32 + 0x7900))) 219 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263, 4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4290, 4291, 4292, 4293, 4294, 4295, 4296, 4297, 4298, 4299, 4300, 4301, 4302, 4303] with [f4v, M64]
  rw [show 31008 + p = p + 32 + 30976 by omega, show 8224 + p = p + 32 + 8192 by omega,
    show 20512 + p = p + 32 + 20480 by omega, show 63264 + p = p + 32 + 63232 by omega,
    show 55072 + p = p + 32 + 55040 by omega, show 39200 + p = p + 32 + 39168 by omega,
    show 32 + p = p + 32 by omega]
  congr 2
  exact f4_arith (word_lt M _)

theorem f4_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {p ret : Nat} (M : ByteArray) (hp : p + 64 < 0x5000) :
    Reach (callState s 10484 (wd p :: f4K ret tail) M)
      (callState s 10308 (wd (p + 64) :: f4K ret tail) M) 28 := by
  opt44_reach [4304, 4305, 4306, 4307, 4308, 4309, 4310]
  simp only [Nat.add_comm, and_self]

theorem f4_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (M : ByteArray) :
    Reach (callState s 10484 (wd 0x4fc0 :: f4K ret tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [4304, 4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315] with [hj]

theorem f4_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (M : ByteArray) :
    Reach (callState s 10229 (wd ret :: tail) M) (callState s 10308 (wd 0x3000 :: f4K ret tail) M) 13 := by
  have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this
  opt44_reach [4160, 4161, 4162, 4163, 4164] with [M64]

/-- `ACC[t]`'s value as a function of `t`. -/
def f4f (m : ByteArray) (t : Nat) : Nat := f4v m (CW + 32 * t)

/-- `f4v` of a memory that differs from `m` only in `ACC[0, n)`. -/
theorem f4v_store (m : ByteArray) {n t : Nat} (hn : n ≤ 256) (ht : t < 256) :
    f4v (storeWords m ACC (f4f m) n) (CW + 32 * t) = f4f m t := by
  unfold f4f f4v
  simp only [CW, ACC] at *
  rw [WP4.word_storeWords_out (a := 12288 + 32 * t) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 20480) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x9900) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xd700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0xf700) (by omega),
    WP4.word_storeWords_out (a := 12288 + 32 * t + 0x2000) (by omega)]

theorem f4_next (m : ByteArray) {n : Nat} (hn : n < 256) {p : Nat} (hp : p = CW + 32 * n) :
    MachineState.writeBytes (storeWords m ACC (f4f m) n)
        (Data.Bytes.natToBytesPadded (f4v (storeWords m ACC (f4f m) n) p) 32) (p + 0x7900) =
      storeWords m ACC (f4f m) (n + 1) := by
  rw [storeWords_succ, hp, f4v_store m (by omega) hn]
  congr 1
  unfold CW ACC; omega

theorem f4_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {ret j : Nat} (m : ByteArray) (hj : j < 128) :
    Reach (callState s 10308 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j)))
      (callState s 10484 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j + 2))) 433 := by
  have hp : CW + 64 * j + 64 ≤ 0x5000 := by unfold CW; omega
  have w0 := f4_w0 hs htail (ret := ret) (storeWords m ACC (f4f m) (2 * j)) hp
  rw [f4_next m (by omega) (by omega)] at w0
  have w1 := f4_w1 hs htail (ret := ret) (storeWords m ACC (f4f m) (2 * j + 1)) hp
  rw [f4_next m (by omega) (by omega)] at w1
  exact w0.trans w1

theorem pass3f4_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (m : ByteArray) :
    Reach (callState s Entry.pass3f4 (wd ret :: tail) m)
      (callState s ret tail (storeWords m ACC (f4f m) 256)) Gas.pass3f4 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3f4, Stack.leaf] at this; omega
  let I : Nat → State := fun j =>
    callState s 10308 (wd (CW + 64 * j) :: f4K ret tail) (storeWords m ACC (f4f m) (2 * j))
  have hbody : ∀ j, j < 127 → Reach (I j) (I (j + 1)) 461 := by
    intro j hj
    have h := (f4_iter hs htail (ret := ret) m (j := j) (by omega)).trans
      (f4_tail hs htail (storeWords m ACC (f4f m) (2 * j + 2)) (p := CW + 64 * j) (ret := ret)
        (by unfold CW; omega))
    simp only [I]
    rw [show CW + 64 * (j + 1) = CW + 64 * j + 64 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    exact h
  have hlast : Reach (I 127) (callState s ret tail (storeWords m ACC (f4f m) 256)) 477 :=
    (f4_iter hs htail (ret := ret) m (j := 127) (by omega)).trans
      (f4_exit hs hr (storeWords m ACC (f4f m) 256))
  have hentry : Reach (callState s Entry.pass3f4 (wd ret :: tail) m) (I 0) 13 := by
    simp only [I, Nat.mul_zero, Nat.add_zero, storeWords_zero, CW]
    exact f4_entry hs hr m
  exact ((hentry.trans (Reach.loop 127 hbody)).trans hlast).mono (by unfold Gas.pass3f4; omega)

end MlDsaOpt44.Proofs.GroupP

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **pass3f4** with the post stated as the body of `acc4Word` (`Fn/Group.lean`). -/
theorem pass3f4_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f4 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        let z := word m (ZH + 32 * t)
        (word m (CW + 32 * t) * lane z 0 + word m (HP + 32 * t) * lane z 1 +
          word m (SB + 32 * t) / 2 ^ 64 * lane z 2 +
          ((word m (SB + 8192 + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&&
            (M64 * 2 ^ 192)) +
          word m (ABUF + 32 * t) / 2 ^ 64 * lane z 3) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3f4 [] ret tail m [] m' Gas.pass3f4 := by
  have hv : ∀ t, GroupP.f4f m t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨storeWords m ACC (GroupP.f4f m) 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]
    unfold GroupP.f4f GroupP.f4v
    simp only [CW, ZH, HP, SB, ABUF]
    rw [show 12288 + 32 * t + 20480 = 32768 + 32 * t by omega,
      show 12288 + 32 * t + 0x9900 = 51456 + 32 * t by omega,
      show 12288 + 32 * t + 0xd700 = 67328 + 32 * t by omega,
      show 12288 + 32 * t + 0xf700 = 67328 + 8192 + 32 * t by omega,
      show 12288 + 32 * t + 0x2000 = 20480 + 32 * t by omega]
  · simpa using FrameExcept.storeWords m ACC (GroupP.f4f m) 256
  · exact GroupP.pass3f4_reach hs hr m

end MlDsaOpt44.Proofs
