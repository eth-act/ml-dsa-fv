import MlDsaOpt44.Fn.Blk.Bits
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Blk/Blocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
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

namespace MlDsaOpt87.Proofs.Blk

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem ent_blk {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10992 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10997 (wd 672 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 6 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [4659, 4660, 4661]

theorem ent_blkh {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 12170 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10997 (wd 384 :: wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 17 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [5102, 5103, 5104, 5105, 5106]

theorem ent_blkt {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (ret : Nat) (m : ByteArray) :
    Reach (callState s 12179 (wd ret :: tail) m)
      (callState s 10997 (wd 672 :: wd 384 :: wd 32256 :: wd 28672 :: wd ret :: tail) m) 24 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [5107, 5108, 5109, 5110, 5111, 5112, 5113]

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (xe xp flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10997 (wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 11215 (wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd xe :: wd xp ::
        wd flp :: wd abp :: wd ret :: tail) (flip6 m)) 109 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [4662, 4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670, 4671, 4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689, 4690, 4691, 4692, 4693, 4694, 4695, 4696, 4697, 4698] with [flip6, flipW, U0, U1, U2, U3, U4, U5, word_mstore_disjoint]

theorem bodyB_loop {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2897) (hxp : 96 + xp < xe) (hxe : xe < 2 ^ 16) :
    Reach (callState s 12081 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 ::
        wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s 11215 (wd u5 :: wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd (96 + xp) ::
        wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 70 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060]

theorem bodyB_exit {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (lf w2 w1 w0 u5 u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hflp : flp + 32 ≤ 32 * 2897) (hxp : 96 + xp = xe) (hxe : xe < 2 ^ 16) :
    Reach (callState s 12081 (wd lf :: wd w2 :: wd w1 :: wd w0 :: wd u5 :: wd u4 :: wd u3 :: wd u2 ::
        wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp :: wd abp :: wd ret :: tail) M)
      (callState s 12110 (wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd (96 + xp) ::
        wd (32 + flp) :: wd (256 + abp) :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (lf % 2 ^ 256) 32) flp)) 72 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061]

set_option maxRecDepth 100000 in
theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)
    (u4 u3 u2 u1 u0 xe xp flp abp ret : Nat) (M : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 12110 (wd u4 :: wd u3 :: wd u2 :: wd u1 :: wd u0 :: wd xe :: wd xp :: wd flp ::
        wd abp :: wd ret :: tail) M)
      (callState s ret tail (flip6 M)) 116 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [memWords] at hsz
  opt87_reach [5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101] with [hj, flip6, flipW, word_mstore_disjoint]

end MlDsaOpt87.Proofs.Blk
