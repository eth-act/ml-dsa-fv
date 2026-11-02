import MlDsaOpt87.Fn.Group.Common
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Pass3.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-! # `pass3`: 32 iterations of an 8-word unrolled `ACC[t] += ABUF[t] · lane k of ZH[t]` (WP6) -/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs  -- port: 44 `GroupP` is not imported

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

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
    Reach (callState s 11951 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11975 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 0)) 32) (c + 32 * 0))) 48 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [4939, 4940, 4941, 4942, 4943, 4944, 4945, 4946, 4947, 4948, 4949, 4950, 4951, 4952, 4953, 4954] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 11975 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12007 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 1)) 32) (c + 32 * 1))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w2 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12007 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12039 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 2)) 32) (c + 32 * 2))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w3 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12039 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12071 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 3)) 32) (c + 32 * 3))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12071 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12103 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 4)) 32) (c + 32 * 4))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w5 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12103 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12135 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 5)) 32) (c + 32 * 5))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w6 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12135 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12167 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 6)) 32) (c + 32 * 6))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_w7 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hsh : sh < 256)
    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz2 : z + 256 ≤ 67840)
    (hc2 : c + 256 ≤ 67840) :  -- port: pointer bounds (`zh`, `acc` arguments)
    Reach (callState s 12167 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 12199 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (p3v M a z c sh (32 * 7)) 32) (c + 32 * 7))) 65 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101] with [p3v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,
    Nat.mul_comm, Nat.and_comm]

theorem p3_tail {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {a z c sh ret : Nat} (M : ByteArray) (hlt : a + 256 < 28672) :
    Reach (callState s 12199 (wd (a) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M)
      (callState s 11951 (wd (a + 256) :: wd sh :: wd (z + 256) :: wd (c + 256) :: wd ret :: tail) M) 52 := by
  opt87_reach [5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116]
  simp only [Nat.add_comm, and_self]

theorem p3_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {z c sh ret : Nat} (M : ByteArray) :
    Reach (callState s 12199 (wd (28416) :: wd sh :: wd (z) :: wd (c) :: wd ret :: tail) M) (callState s 12228 (wd ret :: tail) M) 60 := by
  opt87_reach [5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120]

theorem p3_iter {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    {sh ret j zh acc : Nat} (m : ByteArray) (hsh : sh < 256) (hj : j < 32)
    (hzh : zh + 8192 ≤ 51456) (hacc : 51456 ≤ acc) (hacc' : acc + 8192 ≤ 67840) :  -- port: pointer arguments
    Reach (callState s 11951 (wd (ABUF + 256 * j) :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3f m zh acc sh) (8 * j)))
      (callState s 12199 (wd (ABUF + 256 * j) :: wd sh :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (storeWords m acc (p3f m zh acc sh) (8 * j + 8))) 503 := by
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
  let I : Nat → State := fun j => callState s 11951
    (wd (ABUF + 256 * j) :: wd (64 * k) :: wd (zh + 256 * j) :: wd (acc + 256 * j) :: wd ret :: tail) (Mem (8 * j))
  have hentry : Reach (callState s 11947 (wd (64 * k) :: wd zh :: wd acc :: wd ret :: tail) m) (I 0) 4 := by
    simp only [I, Mem, Nat.mul_zero, Nat.add_zero, storeWords_zero]
    opt87_reach [4937, 4938] with [ABUF]
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
        (reach_ret hs 5121 (Mem 256) (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])  -- port: index
          (by norm_num) hr.jumpdest hret (by omega)))
  have hv : ∀ t, p3f m zh acc (64 * k) t < 2 ^ 256 := fun t => Nat.mod_lt _ (by norm_num)
  refine ⟨Mem 256, fun t ht => ?_, ?_, ?_⟩
  · rw [word_storeWords (hv t) 256 ht]; rfl
  · simpa using FrameExcept.storeWords m acc (p3f m zh acc (64 * k)) 256
  · rw [call_iff, Entry.pass3, Gas.pass3]
    exact ((hentry.trans (Reach.loop 31 hbody)).trans hlast).of_eq (by simp) (by simp)

end MlDsaOpt87.Proofs.GroupP
