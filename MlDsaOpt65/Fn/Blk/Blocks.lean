import MlDsaOpt44.Fn.Blk.Bits
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Blk/Blocks.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
/-!
# `blk`: straight-line blocks (WP3)

Prologue (lane flips, masks), the loop body in two parts (de-interleave plus
candidate extraction, then flag store and loop test, taken or not), and the
epilogue (lane flips back, return). Every block is stated for abstract stack
values and memory; `Blk.lean` composes them.
-/

namespace MlDsaOpt65.Proofs.Blk

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 9857 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10076 (wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) (flip6 m)) 111 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt65_reach [4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124] with [flip6, flipW, U0, U1, U2, U3, U4, U5, word_mstore_disjoint]

theorem bodyB_loop {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2833) (hxp : 96 + xp < 672) :
    Reach (callState s 10942 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp ::
        wd ret :: tail) M)
      (callState s 10076 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd (96 + xp) :: wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt65_reach [4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481, 4482, 4483, 4484, 4485, 4486]

theorem bodyB_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2833) (hxp : 96 + xp = 672) :
    Reach (callState s 10942 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp ::
        wd ret :: tail) M)
      (callState s 10972 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd (96 + xp) :: wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt65_reach [4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481, 4482, 4483, 4484, 4485, 4486]

set_option maxRecDepth 100000 in
theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (u5 u4 u3 u2 u1 u0 xp flp abp ret : Nat) (M : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 10972 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s ret tail (flip6 M)) 116 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  
  opt65_reach [4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511, 4512, 4513, 4514, 4515, 4516, 4517, 4518, 4519, 4520, 4521, 4522, 4523, 4524, 4525, 4526] with [hj, flip6, flipW, word_mstore_disjoint]

end MlDsaOpt65.Proofs.Blk
