import MlDsaOptGlam65.Infra.Reflect
import MlDsaOptGlam44.Fn.Blk.Defs
set_option warningAsError true
/-!
# Glam `blk`: entries, the `blkh` exit test and the epilogue

`blk` (pc 10187) pushes `h = 0`, `blkh` (10193) `h = 1`; both reach the common
prologue at 10196, which pushes the six unzip masks; iteration 0 starts at
10364. After iteration 3 (pc 13880) `DUP h; JUMPI` leaves to the epilogue
(16541) for `blkh` or continues with iteration 4 (13885). `blkt` (16552)
pushes `abp = ABUF + 1792 · 4`, `flp = FL + 224 · 4`, `h = 0` and the masks and
jumps to iteration 4.
-/

namespace MlDsaOptGlam65.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Blk
open MlDsaOptGlam44.Proofs.Blk

set_option maxRecDepth 10000

/-- The loop-free body's stack: masks, `h`, `flp`, `abp`, `ret`. -/
abbrev bstk (h flp abp ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd h :: wd flp :: wd abp :: wd ret :: tail

theorem ent_blk {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10187 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10196 (wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 14 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [4274, 4275, 4276, 4277]

theorem ent_blkh {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10193 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10196 (wd 1 :: wd flp :: wd abp :: wd ret :: tail) m) 4 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [4278, 4279]

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10196 (wd h :: wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10364 (bstk h flp abp ret tail) m) 19 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [4280, 4281, 4282, 4283, 4284, 4285, 4286] with [U0, U1, U2, U3, U4, U5]

theorem test0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 13880 (bstk 0 flp abp ret tail) m)
      (callState s 13885 (bstk 0 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [5662, 5663, 5664]

theorem test1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 13880 (bstk 1 flp abp ret tail) m)
      (callState s 16541 (bstk 1 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [5662, 5663, 5664]

theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 16541 (bstk h flp abp ret tail) m) (callState s ret tail m) 27 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [6701, 6702, 6703, 6704, 6705, 6706, 6707, 6708, 6709, 6710, 6711] with [hj]

theorem ent_blkt {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (ret : Nat) (m : ByteArray) :
    Reach (callState s 16552 (wd ret :: tail) m)
      (callState s 13885 (bstk 0 32128 27648 ret tail) m) 38 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam65_rreach [6712, 6713, 6714, 6715, 6716, 6717, 6718, 6719, 6720, 6721, 6722, 6723]
    with [U0, U1, U2, U3, U4, U5]

end MlDsaOptGlam65.Proofs.Blk
