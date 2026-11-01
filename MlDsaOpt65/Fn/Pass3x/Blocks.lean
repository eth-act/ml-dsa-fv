import MlDsaOpt65.Fn.Pass3x.Common
set_option maxHeartbeats 0
set_option warningAsError true
/-!
# `pass3x5 … pass3x8`: loop bodies

Per routine: the stored value `vN M o` (the contract's word equation at offset
`o = 32 t`), one iteration with the back edge taken (`bodyN`), the last
iteration through the `POP` (`exitN`), and `readN` (iteration `t` reads only
`ACC₁[t]` among the words already stored).
-/

namespace MlDsaOpt65.Proofs.Pass3xP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra
open MlDsaOpt65.Proofs.GroupP (word_storeWords_out)

/-- Value `pass3x5` stores at `ACC + 0x2000 + o`. -/
def v5 (M : ByteArray) (o : Nat) : Nat :=
  (word M (ACC + 0x2000 + o) +
    word M (ABUF + o) % 2 ^ 128 * lane (word M (ZH + o)) 0 +
    lane (word M (ABUF + o)) 2 * lane (word M (ZH + o)) 1) % 2 ^ 256

/-- One iteration of `pass3x5` (loop back taken). -/
theorem body5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 < 8192) :
    Reach (callState s 11270 (wd o :: wd ret :: tail) M)
      (callState s 11270 (wd (o + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v5 M o) 32) (ACC + 0x2000 + o))) 150 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4694, 4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740] with [v5]
  refine ⟨?_, by rw [Nat.add_comm]⟩
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega]
  congr 3
  exact alg5 _ _ _

/-- Last iteration of `pass3x5` (loop exit), up to the returning `JUMP`. -/
theorem exit5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 = 8192) :
    Reach (callState s 11270 (wd o :: wd ret :: tail) M)
      (callState s 11389 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v5 M o) 32) (ACC + 0x2000 + o))) 152 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4694, 4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741] with [v5]
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega]
  congr 3
  exact alg5 _ _ _

/-- Iteration `j` of `pass3x5` reads nothing the earlier iterations wrote. -/
theorem read5 (m : ByteArray) (f : Nat → Nat) {j : Nat} (hj : j < 256) :
    v5 (storeWords m (ACC + 0x2000) f j) (32 * j) = v5 m (32 * j) := by
  unfold v5
  rw [word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ACC + 0x2000 + 32 * j) (Or.inr (by omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ABUF + 32 * j) (Or.inl (by unfold ABUF ACC; omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ZH + 32 * j) (Or.inl (by unfold ZH ACC; omega))]

/-- Value `pass3x6` stores at `ACC + 0x2000 + o`. -/
def v6 (M : ByteArray) (o : Nat) : Nat :=
  (word M (ACC + 0x2000 + o) +
    lane (word M (ABUF + o)) 0 * 2 ^ 64 * lane (word M (ZH + o)) 1 +
    word M (ABUF + o) / 2 ^ 64 % 2 ^ 128 * lane (word M (ZH + o)) 2) % 2 ^ 256

/-- One iteration of `pass3x6` (loop back taken). -/
theorem body6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 < 8192) :
    Reach (callState s 11392 (wd o :: wd ret :: tail) M)
      (callState s 11392 (wd (o + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v6 M o) 32) (ACC + 0x2000 + o))) 162 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756, 4757, 4758, 4759, 4760, 4761, 4762, 4763, 4764, 4765, 4766, 4767, 4768, 4769, 4770, 4771, 4772, 4773, 4774, 4775, 4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783, 4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791, 4792, 4793, 4794, 4795] with [v6]
  refine ⟨?_, by rw [Nat.add_comm]⟩
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega]
  congr 3
  exact alg6 _ _ _

/-- Last iteration of `pass3x6` (loop exit), up to the returning `JUMP`. -/
theorem exit6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 = 8192) :
    Reach (callState s 11392 (wd o :: wd ret :: tail) M)
      (callState s 11509 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v6 M o) 32) (ACC + 0x2000 + o))) 164 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756, 4757, 4758, 4759, 4760, 4761, 4762, 4763, 4764, 4765, 4766, 4767, 4768, 4769, 4770, 4771, 4772, 4773, 4774, 4775, 4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783, 4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791, 4792, 4793, 4794, 4795, 4796] with [v6]
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega]
  congr 3
  exact alg6 _ _ _

/-- Iteration `j` of `pass3x6` reads nothing the earlier iterations wrote. -/
theorem read6 (m : ByteArray) (f : Nat → Nat) {j : Nat} (hj : j < 256) :
    v6 (storeWords m (ACC + 0x2000) f j) (32 * j) = v6 m (32 * j) := by
  unfold v6
  rw [word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ACC + 0x2000 + 32 * j) (Or.inr (by omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ABUF + 32 * j) (Or.inl (by unfold ABUF ACC; omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ZH + 32 * j) (Or.inl (by unfold ZH ACC; omega))]

/-- Value `pass3x7` stores at `ACC + 0x2000 + o`. -/
def v7 (M : ByteArray) (o : Nat) : Nat :=
  (word M (ACC + 0x2000 + o) +
    word M (ABUF + o) % 2 ^ 128 * lane (word M (ZH + o)) 3 +
    lane (word M (ABUF + o)) 2 * lane (word M (ZH + 0x2000 + o)) 0) % 2 ^ 256

/-- One iteration of `pass3x7` (loop back taken). -/
theorem body7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 < 8192) :
    Reach (callState s 11512 (wd o :: wd ret :: tail) M)
      (callState s 11512 (wd (o + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v7 M o) 32) (ACC + 0x2000 + o))) 144 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844] with [v7]
  refine ⟨?_, by rw [Nat.add_comm]⟩
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega,
    show ZH + 8192 + o = o + 40960 by unfold ZH; omega]
  congr 3
  exact alg7 _ _ _ _ (word_lt M _)

/-- Last iteration of `pass3x7` (loop exit), up to the returning `JUMP`. -/
theorem exit7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 = 8192) :
    Reach (callState s 11512 (wd o :: wd ret :: tail) M)
      (callState s 11621 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v7 M o) 32) (ACC + 0x2000 + o))) 146 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844, 4845] with [v7]
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + o = o + 32768 by unfold ZH; omega,
    show ZH + 8192 + o = o + 40960 by unfold ZH; omega]
  congr 3
  exact alg7 _ _ _ _ (word_lt M _)

/-- Iteration `j` of `pass3x7` reads nothing the earlier iterations wrote. -/
theorem read7 (m : ByteArray) (f : Nat → Nat) {j : Nat} (hj : j < 256) :
    v7 (storeWords m (ACC + 0x2000) f j) (32 * j) = v7 m (32 * j) := by
  unfold v7
  rw [word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ACC + 0x2000 + 32 * j) (Or.inr (by omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ABUF + 32 * j) (Or.inl (by unfold ABUF ACC; omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ZH + 32 * j) (Or.inl (by unfold ZH ACC; omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ZH + 0x2000 + 32 * j) (Or.inl (by unfold ZH ACC; omega))]

/-- Value `pass3x8` stores at `ACC + 0x2000 + o`. -/
def v8 (M : ByteArray) (o : Nat) : Nat :=
  (word M (ACC + 0x2000 + o) +
    lane (word M (ABUF + o)) 0 * 2 ^ 64 * lane (word M (ZH + 0x2000 + o)) 0) % 2 ^ 256

/-- One iteration of `pass3x8` (loop back taken). -/
theorem body8 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 < 8192) :
    Reach (callState s 11624 (wd o :: wd ret :: tail) M)
      (callState s 11624 (wd (o + 32) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v8 M o) 32) (ACC + 0x2000 + o))) 100 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873, 4874, 4875, 4876, 4877, 4878, 4879] with [v8]
  refine ⟨?_, by rw [Nat.add_comm]⟩
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + 8192 + o = o + 40960 by unfold ZH; omega]
  congr 3
  exact alg8 _ _ _

/-- Last iteration of `pass3x8` (loop exit), up to the returning `JUMP`. -/
theorem exit8 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 1000)
    {o ret : Nat} (M : ByteArray) (ho : o + 32 = 8192) :
    Reach (callState s 11624 (wd o :: wd ret :: tail) M)
      (callState s 11684 (wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v8 M o) 32) (ACC + 0x2000 + o))) 102 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873, 4874, 4875, 4876, 4877, 4878, 4879, 4880] with [v8]
  rw [show ACC + 8192 + o = o + 59648 by unfold ACC; omega,
    show ABUF + o = o + 20480 by unfold ABUF; omega, show ZH + 8192 + o = o + 40960 by unfold ZH; omega]
  congr 3
  exact alg8 _ _ _

/-- Iteration `j` of `pass3x8` reads nothing the earlier iterations wrote. -/
theorem read8 (m : ByteArray) (f : Nat → Nat) {j : Nat} (hj : j < 256) :
    v8 (storeWords m (ACC + 0x2000) f j) (32 * j) = v8 m (32 * j) := by
  unfold v8
  rw [word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ACC + 0x2000 + 32 * j) (Or.inr (by omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ABUF + 32 * j) (Or.inl (by unfold ABUF ACC; omega)),
    word_storeWords_out (m := m) (base := ACC + 0x2000) (v := f) (n := j)
      (a := ZH + 0x2000 + 32 * j) (Or.inl (by unfold ZH ACC; omega))]

end MlDsaOpt65.Proofs.Pass3xP
