import MlDsaOpt65.Fn.Group.Common
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Pass3.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `pass3`: 32 iterations of an 8-word unrolled `ACC[t] += ABUF[t] · lane k of ZH[t]` (WP6) -/

namespace MlDsaOpt65.Proofs.GroupP

open MlDsaOpt44.Proofs  -- port: 44 `GroupP` is not imported

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

/-- Value `pass3` stores at `ACC[t]`. -/
def p3f (m : ByteArray) (zh acc sh t : Nat) : Nat :=  -- port: pointer arguments
  (word m (acc + 32 * t) + word m (ABUF + 32 * t) * (word m (zh + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

/-- Value a word block stores at `c + o` (reads of the current memory). -/
def p3v (M : ByteArray) (a z c sh o : Nat) : Nat :=
  (word M (c + o) + word M (a + o) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

theorem p3_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11036 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11060 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 0)) 32) (c + 32 * 0))) 48 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4529, 4530, 4531, 4532, 4533, 4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4542, 4543, 4544] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11060 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11092 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 1)) 32) (c + 32 * 1))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4545, 4546, 4547, 4548, 4549, 4550, 4551, 4552, 4553, 4554, 4555, 4556, 4557, 4558, 4559, 4560, 4561, 4562, 4563, 4564, 4565] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w2 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11092 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11124 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 2)) 32) (c + 32 * 2))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4566, 4567, 4568, 4569, 4570, 4571, 4572, 4573, 4574, 4575, 4576, 4577, 4578, 4579, 4580, 4581, 4582, 4583, 4584, 4585, 4586] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w3 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11124 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11156 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 3)) 32) (c + 32 * 3))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4587, 4588, 4589, 4590, 4591, 4592, 4593, 4594, 4595, 4596, 4597, 4598, 4599, 4600, 4601, 4602, 4603, 4604, 4605, 4606, 4607] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11156 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11188 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 4)) 32) (c + 32 * 4))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4608, 4609, 4610, 4611, 4612, 4613, 4614, 4615, 4616, 4617, 4618, 4619, 4620, 4621, 4622, 4623, 4624, 4625, 4626, 4627, 4628] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11188 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11220 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 5)) 32) (c + 32 * 5))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639, 4640, 4641, 4642, 4643, 4644, 4645, 4646, 4647, 4648, 4649] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11220 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11252 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 6)) 32) (c + 32 * 6))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4650, 4651, 4652, 4653, 4654, 4655, 4656, 4657, 4658, 4659, 4660, 4661, 4662, 4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_w7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11252 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11284 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 7)) 32) (c + 32 * 7))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4671, 4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689, 4690, 4691] with [p3v, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hlt : a + 256 < 28672) :
    Reach (callState s 11284 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11036 (wd (a + 256) :: wd sh :: wd (z + 256) :: wd (c + 256) :: wd ret :: tail) M) 52 := by
  opt65_reach [4692, 4693, 4694, 4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706]
  simp only [Nat.add_comm, and_self]

theorem p3_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {z c sh ret : Nat} (M : ByteArray) :
    Reach (callState s 11284 (wd (28416) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M) (callState s 11313 (wd ret :: tail) M) 60 := by
  opt65_reach [4692, 4693, 4694, 4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710]

theorem p3_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {sh ret j zh acc : Nat} (m : ByteArray) (hsh : sh < 256) (hj : j < 32)
    (hzh : zh + 8192 ≤ 51456) (hacc : 51456 ≤ acc) (hacc' : acc + 8192 ≤ 67840) :  -- port: pointer arguments
    Reach (callState s 11036 (wd (ABUF + 256 * j) :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3f m zh acc sh) (8 * j)))
      (callState s 11284 (wd (ABUF + 256 * j) :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3f m zh acc sh) (8 * j + 8))) 503 := by
  have hb : ∀ i, i < 8 → p3v (storeWords m acc (p3f m zh acc sh) (8 * j + i)) (ABUF + 256 * j) (zh + 256 * j) (acc + 256 * j) sh (32 * i) = p3f m zh acc sh (8 * j + i) := by
    intro i hi
    unfold p3v p3f
    rw [show ABUF + 256 * j + 32 * i = ABUF + 32 * (8 * j + i) by omega,
      show zh + 256 * j + 32 * i = zh + 32 * (8 * j + i) by omega,
      show acc + 256 * j + 32 * i = acc + 32 * (8 * j + i) by omega,
      word_storeWords_out (a := ABUF + 32 * (8 * j + i)) (by unfold ABUF; omega),
      word_storeWords_out (a := zh + 32 * (8 * j + i)) (by omega),
      word_storeWords_out (a := acc + 32 * (8 * j + i)) (by omega)]
  have e : ∀ i, i < 8 → MachineState.writeBytes (storeWords m acc (p3f m zh acc sh) (8 * j + i))
      (Data.Bytes.natToBytesPadded (p3v (storeWords m acc (p3f m zh acc sh) (8 * j + i)) (ABUF + 256 * j) (zh + 256 * j) (acc + 256 * j) sh (32 * i)) 32) (acc + 256 * j + 32 * i) =
      storeWords m acc (p3f m zh acc sh) (8 * j + i + 1) := fun i hi =>
    storeWords_next rfl (by omega) (hb i hi)
  have ha1 : 20480 ≤ ABUF + 256 * j := by unfold ABUF; omega
  have ha2 : ABUF + 256 * j + 256 ≤ 28672 := by unfold ABUF; omega
  have hz2 : zh + 256 * j + 256 ≤ 67840 := by omega  -- port: pointer bounds
  have hc2 : acc + 256 * j + 256 ≤ 67840 := by omega

  have w0 := p3_w0 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 0)) hsh ha1 ha2 hz2 hc2
  rw [e 0 (by norm_num)] at w0
  have w1 := p3_w1 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 1)) hsh ha1 ha2 hz2 hc2
  rw [e 1 (by norm_num)] at w1
  have w2 := p3_w2 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 2)) hsh ha1 ha2 hz2 hc2
  rw [e 2 (by norm_num)] at w2
  have w3 := p3_w3 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 3)) hsh ha1 ha2 hz2 hc2
  rw [e 3 (by norm_num)] at w3
  have w4 := p3_w4 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 4)) hsh ha1 ha2 hz2 hc2
  rw [e 4 (by norm_num)] at w4
  have w5 := p3_w5 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 5)) hsh ha1 ha2 hz2 hc2
  rw [e 5 (by norm_num)] at w5
  have w6 := p3_w6 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 6)) hsh ha1 ha2 hz2 hc2
  rw [e 6 (by norm_num)] at w6
  have w7 := p3_w7 hs htail (ret := ret) (storeWords m acc (p3f m zh acc sh) (8 * j + 7)) hsh ha1 ha2 hz2 hc2
  rw [e 7 (by norm_num)] at w7
  exact (((((((w0.trans w1).trans w2).trans w3).trans w4).trans w5).trans w6).trans w7)

theorem pass3_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3 ret tail) (m : ByteArray) {k zh acc : Nat} (hk : k < 4)
    (hzh : zh + 8192 ≤ ACC) (hacc : ACC ≤ acc) (hacc' : acc + 8192 ≤ HP) :  -- port: pointer arguments
    ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) =
        (word m (acc + 32 * t) + word m (ABUF + 32 * t) * lane (word m (zh + 32 * t)) k) % 2 ^ 256) ∧
      FrameExcept m m' [(acc, acc + 8192)] ∧
      Call s Entry.pass3 [wd (64 * k), wd zh, wd acc] ret tail m [] m' Gas.pass3 := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3, Stack.leaf] at this; omega
  have hzh1 : zh + 8192 ≤ 51456 := by unfold ACC at hzh; omega  -- port: pointer bounds
  have hacc1 : 51456 ≤ acc := by unfold ACC at hacc; omega
  have hacc2 : acc + 8192 ≤ 67840 := by unfold HP at hacc'; omega
  have hret := hr.small
  have hsh : 64 * k < 256 := by omega
  let Mem : Nat → ByteArray := storeWords m acc (p3f m zh acc (64 * k))
  let I : Nat → State := fun j => callState s 11036
    (wd (ABUF + 256 * j) :: wd (64 * k) :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (Mem (8 * j))
  have hentry : Reach (callState s 11032 (wd (64 * k) :: wd zh :: wd acc :: wd ret :: tail) m) (I 0) 4 := by
    simp only [I, Mem, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    opt65_reach [4527, 4528] with [ABUF]
  have hbody : ∀ j, j < 31 → Reach (I j) (I (j + 1)) 555 := by
    intro j hj
    have h := (p3_iter hs htail (ret := ret) m hsh (j := j) (by omega) hzh1 hacc1 hacc2).trans
      (p3_tail hs htail (Mem (8 * j + 8)) (a := ABUF + 256 * j) (z := zh + 256 * j) (c := acc + 256 * j)
        (sh := 64 * k) (ret := ret) (by unfold ABUF; omega))
    simp only [I, Mem]
    rw [show ABUF + 256 * (j + 1) = ABUF + 256 * j + 256 by ring, show zh + 256 * (j + 1) = zh + 256 * j + 256 by ring,
      show acc + 256 * (j + 1) = acc + 256 * j + 256 by ring, show 8 * (j + 1) = 8 * j + 8 by ring]
    exact h
  have hlast : Reach (I 31) (callState s ret tail (Mem 256)) 571 :=
    (p3_iter hs htail (ret := ret) m hsh (j := 31) (by omega) hzh1 hacc1 hacc2).trans
      ((p3_exit hs htail (sh := 64 * k) (z := zh + 256 * 31) (c := acc + 256 * 31) (ret := ret) (Mem 256)).trans
        (reach_ret hs 4711 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])  -- port: index
          (by norm_num) hr.jumpdest hret (by omega)))
  have hv : ∀ t, p3f m zh acc (64 * k) t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m acc (p3f m zh acc (64 * k)) 256
  · rw [call_iff, Entry.pass3, Gas.pass3]
    exact ((hentry.trans (Reach.loop 31 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt65.Proofs.GroupP
