import MlDsaOptGlam44.Infra.Reflect
import MlDsaOptGlam44.Fn.Blk.Defs
set_option warningAsError true
/-!
# Glam `blk`: entries, the `blkh` exit test and the epilogue

`blk` (pc 10481) pushes `h = 0`, `blkh` (10487) `h = 1`; both reach the common
prologue at 10490, which pushes the six unzip masks; iteration 0 starts at
10658. After iteration 3 (pc 14174) `DUP h; JUMPI` leaves to the epilogue
(16835) for `blkh` or continues with iteration 4 (14179). `blkt` (16846)
pushes `abp = ABUF + 1792 · 4`, `flp = FL + 224 · 4`, `h = 0` and the masks and
jumps to iteration 4.
-/

namespace MlDsaOptGlam44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Blk

set_option maxRecDepth 10000

/-- The loop-free body's stack: masks, `h`, `flp`, `abp`, `ret`. -/
abbrev bstk (h flp abp ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd U5 :: wd U4 :: wd U3 :: wd U2 :: wd U1 :: wd U0 :: wd h :: wd flp :: wd abp :: wd ret :: tail

theorem ent_blk {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10481 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10490 (wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 14 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [4337, 4338, 4339, 4340]

theorem ent_blkh {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10487 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10490 (wd 1 :: wd flp :: wd abp :: wd ret :: tail) m) 4 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [4341, 4342]

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10490 (wd h :: wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10658 (bstk h flp abp ret tail) m) 19 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [4343, 4344, 4345, 4346, 4347, 4348, 4349] with [U0, U1, U2, U3, U4, U5]

theorem test0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 14174 (bstk 0 flp abp ret tail) m)
      (callState s 14179 (bstk 0 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [5725, 5726, 5727]

theorem test1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 14174 (bstk 1 flp abp ret tail) m)
      (callState s 16835 (bstk 1 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [5725, 5726, 5727]

theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 16835 (bstk h flp abp ret tail) m) (callState s ret tail m) 27 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [6764, 6765, 6766, 6767, 6768, 6769, 6770, 6771, 6772, 6773, 6774] with [hj]

theorem ent_blkt {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (ret : Nat) (m : ByteArray) :
    Reach (callState s 16846 (wd ret :: tail) m)
      (callState s 14179 (bstk 0 32128 27648 ret tail) m) 38 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam44_rreach [6775, 6776, 6777, 6778, 6779, 6780, 6781, 6782, 6783, 6784, 6785, 6786]
    with [U0, U1, U2, U3, U4, U5]

end MlDsaOptGlam44.Proofs.Blk
