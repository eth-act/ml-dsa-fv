import MlDsaOpt44.Fn.Blk.Bits
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Blk/Blocks.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `blk`: straight-line blocks (WP3)

Prologue (lane flips, masks), the loop body in two parts (de-interleave plus
candidate extraction, then flag store and loop test, taken or not), and the
epilogue (lane flips back, return). Every block is stated for abstract stack
values and memory; `Blk.lean` composes them.
-/

namespace MlDsaOpt87.Proofs.Blk

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10772 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10991 (wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) (flip6 m)) 111 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511, 4512, 4513, 4514, 4515, 4516, 4517, 4518, 4519, 4520, 4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528, 4529, 4530, 4531, 4532, 4533, 4534] with [flip6, flipW, U0, U1, U2, U3, U4, U5, word_mstore_disjoint]

theorem bodyB_loop {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2865) (hxp : 96 + xp < 672) :
    Reach (callState s 11857 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp ::
        wd ret :: tail) M)
      (callState s 10991 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd (96 + xp) :: wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [4875, 4876, 4877, 4878, 4879, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890, 4891, 4892, 4893, 4894, 4895, 4896]

theorem bodyB_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2865) (hxp : 96 + xp = 672) :
    Reach (callState s 11857 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp ::
        wd ret :: tail) M)
      (callState s 11887 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd (96 + xp) :: wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [4875, 4876, 4877, 4878, 4879, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890, 4891, 4892, 4893, 4894, 4895, 4896]

set_option maxRecDepth 100000 in
theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 11887 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s ret tail (flip6 M)) 116 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  
  opt87_reach [4897, 4898, 4899, 4900, 4901, 4902, 4903, 4904, 4905, 4906, 4907, 4908, 4909, 4910, 4911, 4912, 4913, 4914, 4915, 4916, 4917, 4918, 4919, 4920, 4921, 4922, 4923, 4924, 4925, 4926, 4927, 4928, 4929, 4930, 4931, 4932, 4933, 4934, 4935, 4936] with [hj, flip6, flipW, word_mstore_disjoint]

end MlDsaOpt87.Proofs.Blk
