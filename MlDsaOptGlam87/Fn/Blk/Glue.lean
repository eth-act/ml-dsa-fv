import MlDsaOptGlam87.Infra.Reflect
import MlDsaOptGlam44.Fn.Blk.Defs
set_option warningAsError true
/-!
# Glam `blk`: entries, the `blkh` exit test and the epilogue

`blk` (pc 10846) pushes `h = 0`, `blkh` (10852) `h = 1`; both reach the common
prologue at 10855, which pushes the six unzip masks; iteration 0 starts at
11023. After iteration 3 (pc 14539) `DUP h; JUMPI` leaves to the epilogue
(17200) for `blkh` or continues with iteration 4 (14544). `blkt` (17211)
pushes `abp = ABUF + 1792 · 4`, `flp = FL + 224 · 4`, `h = 0` and the masks and
jumps to iteration 4.
-/

namespace MlDsaOptGlam87.Proofs.Blk

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
    Reach (callState s 10846 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10855 (wd 0 :: wd flp :: wd abp :: wd ret :: tail) m) 14 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [4668, 4669, 4670, 4671]

theorem ent_blkh {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10852 (wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 10855 (wd 1 :: wd flp :: wd abp :: wd ret :: tail) m) 4 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [4672, 4673]

theorem pro {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 10855 (wd h :: wd flp :: wd abp :: wd ret :: tail) m)
      (callState s 11023 (bstk h flp abp ret tail) m) 19 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [4674, 4675, 4676, 4677, 4678, 4679, 4680] with [U0, U1, U2, U3, U4, U5]

theorem test0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 14539 (bstk 0 flp abp ret tail) m)
      (callState s 14544 (bstk 0 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [6056, 6057, 6058]

theorem test1 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (flp abp ret : Nat) (m : ByteArray) :
    Reach (callState s 14539 (bstk 1 flp abp ret tail) m)
      (callState s 17200 (bstk 1 flp abp ret tail) m) 16 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [6056, 6057, 6058]

theorem epi {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (h flp abp ret : Nat) (m : ByteArray)
    (hj : Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 2 ^ 16) :
    Reach (callState s 17200 (bstk h flp abp ret tail) m) (callState s ret tail m) 27 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [7095, 7096, 7097, 7098, 7099, 7100, 7101, 7102, 7103, 7104, 7105] with [hj]

theorem ent_blkt {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 950)
    (ret : Nat) (m : ByteArray) :
    Reach (callState s 17211 (wd ret :: tail) m)
      (callState s 14544 (bstk 0 32128 27648 ret tail) m) 38 := by
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117]
    with [U0, U1, U2, U3, U4, U5]

end MlDsaOptGlam87.Proofs.Blk
