import MlDsaOpt44.Fn.Blk.Bits
import MlDsaOpt44.Layout
/-!
# `blk`: straight-line blocks (WP3, v4)

The three entries `blk`, `blkh` and `blkt` (`Entry.blk`, `Entry.blkh`,
`Entry.blkt`) push the lane range `[xp, xe)` (and `blkt` its `abp`, `flp`) and
enter the shared body just after `blk`'s pushes: prologue (lane flips, masks),
the loop body in two parts (de-interleave plus candidate extraction, then flag
store and loop test, taken or not), and the epilogue (lane flips back, return).
Every block is stated for abstract stack values and memory; `Blk/Proof.lean`
composes them.
-/

namespace MlDsaOpt44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem ent_blk {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 9025 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 9030 (wd 672 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 6 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [3703, 3704, 3705]

theorem ent_blkh {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10203 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 9030 (wd 384 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 17 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [4146, 4147, 4148, 4149, 4150]

theorem ent_blkt {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (ret : Nat) (m : ByteArray) :
    Reach (callState s 10212 (wd ret :: tail) m)
      (callState s 9030 (wd 672 :: wd 384 :: wd 32256 :: wd 28672 :: wd ret :: tail) m) 24 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [4151, 4152, 4153, 4154, 4155, 4156, 4157]

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (xe xp flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 9030 (wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 9248 (wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd xe :: wd xp ::
        wd flp :: wd abp :: wd ret :: tail) (flip6 m)) 109 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742] with [flip6, flipW, U0, U1, U2, U3, U4, U5, word_mstore_disjoint]

theorem bodyB_loop {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2616) (hxp : 96 + xp < xe) (hxe : xe < 2 ^ 16) :
    Reach (callState s 10114 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 ::
        wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s 9248 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd (96 + xp) ::
        wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104]

theorem bodyB_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2616) (hxp : 96 + xp = xe) (hxe : xe < 2 ^ 16) :
    Reach (callState s 10114 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 ::
        wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s 10143 (wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd (96 + xp) ::
        wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 72 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104, 4105]

set_option maxRecDepth 100000 in
theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 10143 (wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp ::
        wd abp :: wd ret :: tail) M)
      (callState s ret tail (flip6 M)) 116 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt44_reach [4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145] with [hj, flip6, flipW, word_mstore_disjoint]

end MlDsaOpt44.Proofs.Blk
