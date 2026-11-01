import MlDsaOpt44.Fn.Group.Common
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `pass3m`: as `pass3` with the candidate words masked by `lm` (WP6) -/

namespace MlDsaOpt44.Proofs.GroupP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

/-- Value `pass3m` stores at `ACC[t]`. -/
def p3mf (m : ByteArray) (lm sh t : Nat) : Nat :=
  (word m (ACC + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * (word m (ZH + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

/-- Value a word block stores at `c + o` (reads of the current memory). -/
def p3mv (M : ByteArray) (a z c lm sh o : Nat) : Nat :=
  (word M (c + o) + (word M (a + o) &&& lm) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

theorem p3m_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10348 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10374 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 0)) 32) (c + 32 * 0))) 54 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4281] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10374 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10408 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 1)) 32) (c + 32 * 1))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4290, 4291, 4292, 4293, 4294, 4295, 4296, 4297, 4298, 4299, 4300, 4301, 4302, 4303, 4304] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w2 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10408 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10442 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 2)) 32) (c + 32 * 2))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315, 4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w3 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10442 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10476 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 3)) 32) (c + 32 * 3))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4344, 4345, 4346, 4347, 4348, 4349, 4350] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10476 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10510 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 4)) 32) (c + 32 * 4))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4351, 4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10510 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10544 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 5)) 32) (c + 32 * 5))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4374, 4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392, 4393, 4394, 4395, 4396] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10544 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10578 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 6)) 32) (c + 32 * 6))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4405, 4406, 4407, 4408, 4409, 4410, 4411, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)
    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456) :
    Reach (callState s 10578 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10612 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 7)) 32) (c + 32 * 7))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439, 4440, 4441, 4442] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hlt : a + 256 < 28672) :
    Reach (callState s 10612 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 10348 (wd (a + 256) :: wd lm :: wd sh :: wd (z + 256) :: wd (c + 256) :: wd ret :: tail) M) 52 := by
  opt44_reach [4443, 4444, 4445, 4446, 4447, 4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457]
  simp only [Nat.add_comm, and_self]

theorem p3m_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {z c sh ret lm : Nat} (M : ByteArray) :
    Reach (callState s 10612 (wd (28416) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M) (callState s 10642 (wd ret :: tail) M) 62 := by
  opt44_reach [4443, 4444, 4445, 4446, 4447, 4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462]

theorem p3m_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {sh ret lm j : Nat} (m : ByteArray) (hsh : sh < 256) (hj : j < 32) :
    Reach (callState s 10348 (wd (ABUF + 256 * j) :: wd lm :: wd sh :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (storeWords m ACC (p3mf m lm sh) (8 * j)))
      (callState s 10612 (wd (ABUF + 256 * j) :: wd lm :: wd sh :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (storeWords m ACC (p3mf m lm sh) (8 * j + 8))) 551 := by
  have hb : ∀ i, i < 8 → p3mv (storeWords m ACC (p3mf m lm sh) (8 * j + i)) (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) lm sh (32 * i) = p3mf m lm sh (8 * j + i) := by
    intro i hi
    unfold p3mv p3mf
    rw [show ABUF + 256 * j + 32 * i = ABUF + 32 * (8 * j + i) by omega,
      show ZH + 256 * j + 32 * i = ZH + 32 * (8 * j + i) by omega,
      show ACC + 256 * j + 32 * i = ACC + 32 * (8 * j + i) by omega,
      word_storeWords_out (a := ABUF + 32 * (8 * j + i)) (by unfold ABUF ACC; omega),
      word_storeWords_out (a := ZH + 32 * (8 * j + i)) (by unfold ZH ACC; omega),
      word_storeWords_out (a := ACC + 32 * (8 * j + i)) (by omega)]
  have e : ∀ i, i < 8 → MachineState.writeBytes (storeWords m ACC (p3mf m lm sh) (8 * j + i))
      (Data.Bytes.natToBytesPadded (p3mv (storeWords m ACC (p3mf m lm sh) (8 * j + i)) (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) lm sh (32 * i)) 32) (ACC + 256 * j + 32 * i) =
      storeWords m ACC (p3mf m lm sh) (8 * j + i + 1) := fun i hi =>
    storeWords_next rfl (by omega) (hb i hi)
  have ha1 : 20480 ≤ ABUF + 256 * j := by unfold ABUF; omega
  have ha2 : ABUF + 256 * j + 256 ≤ 28672 := by unfold ABUF; omega
  have hz1 : 32768 ≤ ZH + 256 * j := by unfold ZH; omega
  have hz2 : ZH + 256 * j + 256 ≤ 40960 := by unfold ZH; omega
  have hc1 : 43264 ≤ ACC + 256 * j := by unfold ACC; omega
  have hc2 : ACC + 256 * j + 256 ≤ 51456 := by unfold ACC; omega

  have w0 := p3m_w0 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 0)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 0 (by norm_num)] at w0
  have w1 := p3m_w1 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 1)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 1 (by norm_num)] at w1
  have w2 := p3m_w2 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 2)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 2 (by norm_num)] at w2
  have w3 := p3m_w3 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 3)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 3 (by norm_num)] at w3
  have w4 := p3m_w4 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 4)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 4 (by norm_num)] at w4
  have w5 := p3m_w5 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 5)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 5 (by norm_num)] at w5
  have w6 := p3m_w6 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 6)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 6 (by norm_num)] at w6
  have w7 := p3m_w7 hs htail (ret := ret) (lm := lm) (storeWords m ACC (p3mf m lm sh) (8 * j + 7)) hsh ha1 ha2 hz1 hz2 hc1 hc2
  rw [e 7 (by norm_num)] at w7
  exact (((((((w0.trans w1).trans w2).trans w3).trans w4).trans w5).trans w6).trans w7)

theorem pass3m_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3m ret tail) (m : ByteArray) {k lm : Nat} (hk : k < 4)
    (_hlm : lm < 2 ^ 256) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        (word m (ACC + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * lane (word m (ZH + 32 * t)) k) %
          2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3m [wd lm, wd (64 * k), wd ZH, wd ACC] ret tail m [] m' Gas.pass3m := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3m, Stack.leaf] at this; omega
  have hret := hr.small
  have hsh : 64 * k < 256 := by omega
  let Mem : Nat → ByteArray := storeWords m ACC (p3mf m lm (64 * k))
  let I : Nat → State := fun j => callState s 10348
    (wd (ABUF + 256 * j) :: wd lm :: wd (64 * k) :: wd (ZH + 256 * j) :: wd (ACC + 256 * j) :: wd ret :: tail) (Mem (8 * j))
  have hentry : Reach (callState s 10344 (wd lm :: wd (64 * k) :: wd ZH :: wd ACC :: wd ret :: tail) m) (I 0) 4 := by
    simp only [I, Mem, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    opt44_reach [4262, 4263] with [ABUF]
  have hbody : ∀ j, j < 31 → Reach (I j) (I (j + 1)) 603 := by
    intro j hj
    have h := (p3m_iter hs htail (ret := ret) (lm := lm) m hsh (j := j) (by omega)).trans
      (p3m_tail hs htail (lm := lm) (Mem (8 * j + 8)) (a := ABUF + 256 * j) (z := ZH + 256 * j) (c := ACC + 256 * j)
        (sh := 64 * k) (ret := ret) (by unfold ABUF; omega))
    simp only [I, Mem]
    rw [show ABUF + 256 * (j + 1) = ABUF + 256 * j + 256 by ring, show ZH + 256 * (j + 1) = ZH + 256 * j + 256 by ring,
      show ACC + 256 * (j + 1) = ACC + 256 * j + 256 by ring, show 8 * (j + 1) = 8 * j + 8 by ring]
    exact h
  have hlast : Reach (I 31) (callState s ret tail (Mem 256)) 621 :=
    (p3m_iter hs htail (ret := ret) (lm := lm) m hsh (j := 31) (by omega)).trans
      ((p3m_exit hs htail (lm := lm) (sh := 64 * k) (z := ZH + 256 * 31) (c := ACC + 256 * 31) (ret := ret) (Mem 256)).trans
        (reach_ret hs 4463 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
          (by norm_num) hr.jumpdest hret (by omega)))
  have hv : ∀ t, p3mf m lm (64 * k) t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m ACC (p3mf m lm (64 * k)) 256
  · rw [call_iff, Entry.pass3m, Gas.pass3m]
    exact ((hentry.trans (Reach.loop 31 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt44.Proofs.GroupP
