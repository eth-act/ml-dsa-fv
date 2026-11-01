import MlDsaOpt87.Fn.Group.Common
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Pass3m.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # `pass3m`: as `pass3` with the candidate words masked by `lm` (WP6) -/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs  -- port: 44 `GroupP` is not imported

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- Value `pass3m` stores at `ACC[t]`. -/
def p3mf (m : ByteArray) (zh acc lm sh t : Nat) : Nat :=  -- port: pointer arguments
  (word m (acc + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * (word m (zh + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

/-- Value a word block stores at `c + o` (reads of the current memory). -/
def p3mv (M : ByteArray) (a z c lm sh o : Nat) : Nat :=
  (word M (c + o) + (word M (a + o) &&& lm) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256

theorem p3m_w0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12233 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12259 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 0)) 32) (c + 32 * 0))) 54 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12259 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12293 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 1)) 32) (c + 32 * 1))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5161, 5162, 5163, 5164] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w2 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12293 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12327 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 2)) 32) (c + 32 * 2))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5165, 5166, 5167, 5168, 5169, 5170, 5171, 5172, 5173, 5174, 5175, 5176, 5177, 5178, 5179, 5180, 5181, 5182, 5183, 5184, 5185, 5186, 5187] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w3 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12327 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12361 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 3)) 32) (c + 32 * 3))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5188, 5189, 5190, 5191, 5192, 5193, 5194, 5195, 5196, 5197, 5198, 5199, 5200, 5201, 5202, 5203, 5204, 5205, 5206, 5207, 5208, 5209, 5210] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12361 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12395 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 4)) 32) (c + 32 * 4))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5211, 5212, 5213, 5214, 5215, 5216, 5217, 5218, 5219, 5220, 5221, 5222, 5223, 5224, 5225, 5226, 5227, 5228, 5229, 5230, 5231, 5232, 5233] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12395 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12429 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 5)) 32) (c + 32 * 5))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5234, 5235, 5236, 5237, 5238, 5239, 5240, 5241, 5242, 5243, 5244, 5245, 5246, 5247, 5248, 5249, 5250, 5251, 5252, 5253, 5254, 5255, 5256] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12429 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12463 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 6)) 32) (c + 32 * 6))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5257, 5258, 5259, 5260, 5261, 5262, 5263, 5264, 5265, 5266, 5267, 5268, 5269, 5270, 5271, 5272, 5273, 5274, 5275, 5276, 5277, 5278, 5279] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_w7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12463 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12497 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3mv M a z c lm sh (32 * 7)) 32) (c + 32 * 7))) 71 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5280, 5281, 5282, 5283, 5284, 5285, 5286, 5287, 5288, 5289, 5290, 5291, 5292, 5293, 5294, 5295, 5296, 5297, 5298, 5299, 5300, 5301, 5302] with [p3mv, land_m64, land_m64']
  simp only [Nat.add_zero, Nat.add_comm, Nat.mul_comm, Nat.and_comm]

theorem p3m_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret lm : Nat} (M : ByteArray) (hlt : a + 256 < 28672) :
    Reach (callState s 12497 (wd (a) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12233 (wd (a + 256) :: wd lm :: wd sh :: wd (z + 256) :: wd (c + 256) :: wd ret :: tail) M) 52 := by
  opt87_reach [5303, 5304, 5305, 5306, 5307, 5308, 5309, 5310, 5311, 5312, 5313, 5314, 5315, 5316, 5317]
  simp only [Nat.add_comm, and_self]

theorem p3m_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {z c sh ret lm : Nat} (M : ByteArray) :
    Reach (callState s 12497 (wd (28416) :: wd lm :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M) (callState s 12527 (wd ret :: tail) M) 62 := by
  opt87_reach [5303, 5304, 5305, 5306, 5307, 5308, 5309, 5310, 5311, 5312, 5313, 5314, 5315, 5316, 5317, 5318, 5319, 5320, 5321, 5322]

theorem p3m_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {sh ret lm j zh acc : Nat} (m : ByteArray) (hsh : sh < 256) (hj : j < 32)
    (hzh : zh + 8192 ≤ 51456) (hacc : 51456 ≤ acc) (hacc' : acc + 8192 ≤ 67840) :  -- port: pointer arguments
    Reach (callState s 12233 (wd (ABUF + 256 * j) :: wd lm :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3mf m zh acc lm sh) (8 * j)))
      (callState s 12497 (wd (ABUF + 256 * j) :: wd lm :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 8))) 551 := by
  have hb : ∀ i, i < 8 → p3mv (storeWords m acc (p3mf m zh acc lm sh) (8 * j + i)) (ABUF + 256 * j) (zh + 256 * j) (acc + 256 * j) lm sh (32 * i) = p3mf m zh acc lm sh (8 * j + i) := by
    intro i hi
    unfold p3mv p3mf
    rw [show ABUF + 256 * j + 32 * i = ABUF + 32 * (8 * j + i) by omega,
      show zh + 256 * j + 32 * i = zh + 32 * (8 * j + i) by omega,
      show acc + 256 * j + 32 * i = acc + 32 * (8 * j + i) by omega,
      word_storeWords_out (a := ABUF + 32 * (8 * j + i)) (by unfold ABUF; omega),
      word_storeWords_out (a := zh + 32 * (8 * j + i)) (by omega),
      word_storeWords_out (a := acc + 32 * (8 * j + i)) (by omega)]
  have e : ∀ i, i < 8 → MachineState.writeBytes (storeWords m acc (p3mf m zh acc lm sh) (8 * j + i))
      (Data.Bytes.natToBytesPadded (p3mv (storeWords m acc (p3mf m zh acc lm sh) (8 * j + i)) (ABUF + 256 * j) (zh + 256 * j) (acc + 256 * j) lm sh (32 * i)) 32) (acc + 256 * j + 32 * i) =
      storeWords m acc (p3mf m zh acc lm sh) (8 * j + i + 1) := fun i hi =>
    storeWords_next rfl (by omega) (hb i hi)
  have ha1 : 20480 ≤ ABUF + 256 * j := by unfold ABUF; omega
  have ha2 : ABUF + 256 * j + 256 ≤ 28672 := by unfold ABUF; omega
  have hz2 : zh + 256 * j + 256 ≤ 67840 := by omega  -- port: pointer bounds
  have hc2 : acc + 256 * j + 256 ≤ 67840 := by omega

  have w0 := p3m_w0 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 0)) hsh ha1 ha2 hz2 hc2
  rw [e 0 (by norm_num)] at w0
  have w1 := p3m_w1 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 1)) hsh ha1 ha2 hz2 hc2
  rw [e 1 (by norm_num)] at w1
  have w2 := p3m_w2 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 2)) hsh ha1 ha2 hz2 hc2
  rw [e 2 (by norm_num)] at w2
  have w3 := p3m_w3 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 3)) hsh ha1 ha2 hz2 hc2
  rw [e 3 (by norm_num)] at w3
  have w4 := p3m_w4 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 4)) hsh ha1 ha2 hz2 hc2
  rw [e 4 (by norm_num)] at w4
  have w5 := p3m_w5 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 5)) hsh ha1 ha2 hz2 hc2
  rw [e 5 (by norm_num)] at w5
  have w6 := p3m_w6 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 6)) hsh ha1 ha2 hz2 hc2
  rw [e 6 (by norm_num)] at w6
  have w7 := p3m_w7 hs htail (ret := ret) (lm := lm) (storeWords m acc (p3mf m zh acc lm sh) (8 * j + 7)) hsh ha1 ha2 hz2 hc2
  rw [e 7 (by norm_num)] at w7
  exact (((((((w0.trans w1).trans w2).trans w3).trans w4).trans w5).trans w6).trans w7)

theorem pass3m_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3m ret tail) (m : ByteArray) {k lm zh acc : Nat} (hk : k < 4)
    (_hlm : lm < 2 ^ 256) (hzh : zh + 8192 ≤ ACC) (hacc : ACC ≤ acc) (hacc' : acc + 8192 ≤ HP) :  -- port: pointer arguments
    ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) =
        (word m (acc + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * lane (word m (zh + 32 * t)) k) %
          2 ^ 256) ∧
      FrameExcept m m' [(acc, acc + 8192)] ∧
      Call s Entry.pass3m [wd lm, wd (64 * k), wd zh, wd acc] ret tail m [] m' Gas.pass3m := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.pass3m, Stack.leaf] at this; omega
  have hzh1 : zh + 8192 ≤ 51456 := by unfold ACC at hzh; omega  -- port: pointer bounds
  have hacc1 : 51456 ≤ acc := by unfold ACC at hacc; omega
  have hacc2 : acc + 8192 ≤ 67840 := by unfold HP at hacc'; omega
  have hret := hr.small
  have hsh : 64 * k < 256 := by omega
  let Mem : Nat → ByteArray := storeWords m acc (p3mf m zh acc lm (64 * k))
  let I : Nat → State := fun j => callState s 12233
    (wd (ABUF + 256 * j) :: wd lm :: wd (64 * k) :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (Mem (8 * j))
  have hentry : Reach (callState s 12229 (wd lm :: wd (64 * k) :: wd zh :: wd acc :: wd ret :: tail) m) (I 0) 4 := by
    simp only [I, Mem, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    opt87_reach [5122, 5123] with [ABUF]
  have hbody : ∀ j, j < 31 → Reach (I j) (I (j + 1)) 603 := by
    intro j hj
    have h := (p3m_iter hs htail (ret := ret) (lm := lm) m hsh (j := j) (by omega) hzh1 hacc1 hacc2).trans
      (p3m_tail hs htail (lm := lm) (Mem (8 * j + 8)) (a := ABUF + 256 * j) (z := zh + 256 * j) (c := acc + 256 * j)
        (sh := 64 * k) (ret := ret) (by unfold ABUF; omega))
    simp only [I, Mem]
    rw [show ABUF + 256 * (j + 1) = ABUF + 256 * j + 256 by ring, show zh + 256 * (j + 1) = zh + 256 * j + 256 by ring,
      show acc + 256 * (j + 1) = acc + 256 * j + 256 by ring, show 8 * (j + 1) = 8 * j + 8 by ring]
    exact h
  have hlast : Reach (I 31) (callState s ret tail (Mem 256)) 621 :=
    (p3m_iter hs htail (ret := ret) (lm := lm) m hsh (j := 31) (by omega) hzh1 hacc1 hacc2).trans
      ((p3m_exit hs htail (lm := lm) (sh := 64 * k) (z := zh + 256 * 31) (c := acc + 256 * 31) (ret := ret) (Mem 256)).trans
        (reach_ret hs 5323 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])  -- port: index
          (by norm_num) hr.jumpdest hret (by omega)))
  have hv : ∀ t, p3mf m zh acc lm (64 * k) t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m acc (p3mf m zh acc lm (64 * k)) 256
  · rw [call_iff, Entry.pass3m, Gas.pass3m]
    exact ((hentry.trans (Reach.loop 31 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt87.Proofs.GroupP
