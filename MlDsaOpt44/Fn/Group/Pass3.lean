import MlDsaOpt44.Fn.Group.Common
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-! # `pass3`: 32 iterations of an 8-word unrolled `ACC[t] += ABUF[t] · lane k of ZH[t]` (WP6) -/

namespace MlDsaOpt44.Proofs.GroupP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

/-- Value `pass3` stores at `ACC[t]`. -/
def p3f (m : ByteArray) (sh t : Nat) : Nat :=
  (word m (ACC + 32 * t) + word m (ABUF + 32 * t) * (word m (ZH + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

/-- Value a word block stores at `c + o` (reads of the current memory). -/
def p3v (M : ByteArray) (a z c sh o : Nat) : Nat :=
  (word M (c + o) + word M (a + o) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

theorem p3_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10066 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10090 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 0)) 32) (c + 32 * 0))) 48 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4079, 4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10090 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10122 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 1)) 32) (c + 32 * 1))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w2 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10122 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10154 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 2)) 32) (c + 32 * 2))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w3 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10154 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10186 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 3)) 32) (c + 32 * 3))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4155, 4156, 4157] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10186 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10218 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 4)) 32) (c + 32 * 4))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169, 4170, 4171, 4172, 4173, 4174, 4175, 4176, 4177, 4178] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10218 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10250 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 5)) 32) (c + 32 * 5))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197, 4198, 4199] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10250 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10282 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 6)) 32) (c + 32 * 6))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10282 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10314 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 7)) 32) (c + 32 * 7))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4221, 4222, 4223, 4224, 4225, 4226, 4227, 4228, 4229, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hlt : a + 256 < 28672) :
    Reach (callState s 10314 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10066 (wd (a + 256) :: wd sh :: wd (z + 256) :: wd (c + 256) :: wd ret :: tail) M) 52 := by
  opt44_reach [4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256]
  simp only [Nat.add_comm, and_self]

theorem p3_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {z c sh ret : Nat} (M : ByteArray) :
    Reach (callState s 10314 (wd (28416) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M) (callState s 10343 (wd ret :: tail) M) 60 := by
  opt44_reach [4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260]

theorem p3_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {sh ret j : Nat} (m : ByteArray) (hsh : sh < 256) (hj : j < 32) :
    Reach (callState s 10066 (wd (ABUF + 256 * j) :: wd sh :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (storeWords m ACC (p3f m sh) (8 * j)))
      (callState s 10314 (wd (ABUF + 256 * j) :: wd sh :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (storeWords m ACC (p3f m sh) (8 * j + 8))) 503 := by
  have hb : ∀ i, i < 8 → p3v (storeWords m ACC (p3f m sh) (8 * j + i)) (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) sh (32 * i) = p3f m sh (8 * j + i) := by
    intro i hi
    unfold p3v p3f
    rw [show ABUF + 256 * j + 32 * i = ABUF + 32 * (8 * j + i) by omega,
      show ZH + 256 * j + 32 * i = ZH + 32 * (8 * j + i) by omega,
      show ACC + 256 * j + 32 * i = ACC + 32 * (8 * j + i) by omega,
      word_storeWords_out (a := ABUF + 32 * (8 * j + i)) (by unfold ABUF ACC; omega),
      word_storeWords_out (a := ZH + 32 * (8 * j + i)) (by unfold ZH ACC; omega),
      word_storeWords_out (a := ACC + 32 * (8 * j + i)) (by omega)]
  have e : ∀ i, i < 8 → MachineState.writeBytes (storeWords m ACC (p3f m sh) (8 * j + i))
      (Data.Bytes.natToBytesPadded (p3v (storeWords m ACC (p3f m sh) (8 * j + i)) (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) sh (32 * i)) 32) (ACC + 256 * j + 32 * i) =
      storeWords m ACC (p3f m sh) (8 * j + i + 1) := fun i hi =>
    storeWords_next rfl (by omega) (hb i hi)
  have ha1 : 20480 ≤ ABUF + 256 * j := by unfold ABUF; omega
  have ha2 : ABUF + 256 * j + 256 ≤ 28672 := by unfold ABUF; omega
  have hz1 : 32768 ≤ ZH + 256 * j := by unfold ZH; omega
  have hz2 : ZH + 256 * j + 256 ≤ 40960 := by unfold ZH; omega
  have hc1 : 43264 ≤ ACC + 256 * j := by unfold ACC; omega
  have hc2 : ACC + 256 * j + 256 ≤ 51456 := by unfold ACC; omega

  have w0 := p3_w0 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 0)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 0 (by norm_num)] at w0
  have w1 := p3_w1 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 1)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 1 (by norm_num)] at w1
  have w2 := p3_w2 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 2)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 2 (by norm_num)] at w2
  have w3 := p3_w3 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 3)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 3 (by norm_num)] at w3
  have w4 := p3_w4 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 4)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 4 (by norm_num)] at w4
  have w5 := p3_w5 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 5)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 5 (by norm_num)] at w5
  have w6 := p3_w6 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 6)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 6 (by norm_num)] at w6
  have w7 := p3_w7 hs htail (ret := ret) (storeWords m ACC (p3f m sh) (8 * j + 7)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 7 (by norm_num)] at w7
  exact (((((((w0.trans w1).trans w2).trans w3).trans w4).trans w5).trans w6).trans w7)

theorem pass3_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3 ret tail) (m : ByteArray) {k : Nat} (hk : k < 4) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        (word m (ACC + 32 * t) + word m (ABUF + 32 * t) * lane (word m (ZH + 32 * t)) k) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3 [wd (64 * k), wd ZH, wd ACC] ret tail m [] m' Gas.pass3 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3, Stack.leaf] at this; omega
  have hret := hr.small
  have hsh : 64 * k < 256 := by omega
  let Mem : Nat → ByteArray := storeWords m ACC (p3f m (64 * k))
  let I : Nat → State := fun j => callState s 10066
    (wd (ABUF + 256 * j) :: wd (64 * k) :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (Mem (8 * j))
  have hentry : Reach (callState s 10062 (wd (64 * k) :: wd ZH :: wd ACC :: wd ret :: tail) m) (I 0) 4 := by
    simp only [I, Mem, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    opt44_reach [4077, 4078] with [ABUF]
  have hbody : ∀ j, j < 31 → Reach (I j) (I (j + 1)) 555 := by
    intro j hj
    have h := (p3_iter hs htail (ret := ret) m hsh (j := j) (by omega)).trans
      (p3_tail hs htail (Mem (8 * j + 8)) (a := ABUF + 256 * j) (z := ZH + 256 * j) (c := ACC + 256 * j)
        (sh := 64 * k) (ret := ret) (by unfold ABUF; omega))
    simp only [I, Mem]
    rw [show ABUF + 256 * (j + 1) = ABUF + 256 * j + 256 by ring, show ZH + 256 * (j + 1) = ZH + 256 * j + 256 by ring,
      show ACC + 256 * (j + 1) = ACC + 256 * j + 256 by ring, show 8 * (j + 1) = 8 * j + 8 by ring]
    exact h
  have hlast : Reach (I 31) (callState s ret tail (Mem 256)) 571 :=
    (p3_iter hs htail (ret := ret) m hsh (j := 31) (by omega)).trans
      ((p3_exit hs htail (sh := 64 * k) (z := ZH + 256 * 31) (c := ACC + 256 * 31) (ret := ret) (Mem 256)).trans
        (reach_ret hs 4261 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
          (by norm_num) hr.jumpdest hret (by omega)))
  have hv : ∀ t, p3f m (64 * k) t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m ACC (p3f m (64 * k)) 256
  · rw [call_iff, Entry.pass3, Gas.pass3]
    exact ((hentry.trans (Reach.loop 31 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt44.Proofs.GroupP
