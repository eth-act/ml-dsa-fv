import MlDsaOpt87.Fn.Group.Squeeze
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-87): glue blocks between the calls (WP G1)

Ported from `MlDsaOpt44/Fn/Group/Main.lean` (instruction indices = 44 + 646):
the five `kf4` / `blk` call sites, the `gfix amask` call, the `pass3` call
with `zh = ZH + 0x2000 (col / 4)`, `acc = ACC + 0x2000 rb`, and the epilogue.
-/

namespace MlDsaOpt87.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

theorem g1_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (15291 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 22277 (wd (15299 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6870, 6871, 6872, 6873]
  · opt87_reach [6880, 6881, 6882, 6883]
  · opt87_reach [6890, 6891, 6892, 6893]
  · opt87_reach [6900, 6901, 6902, 6903]
  · opt87_reach [6910, 6911, 6912, 6913]

theorem g1_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (15299 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 10997 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (15313 + 22 * b) ::
          gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6874, 6875, 6876, 6877, 6878, 6879] with [FL, ABUF]
  · opt87_reach [6884, 6885, 6886, 6887, 6888, 6889] with [FL, ABUF]
  · opt87_reach [6894, 6895, 6896, 6897, 6898, 6899] with [FL, ABUF]
  · opt87_reach [6904, 6905, 6906, 6907, 6908, 6909] with [FL, ABUF]
  · opt87_reach [6914, 6915, 6916, 6917, 6918, 6919] with [FL, ABUF]

theorem g1_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 15401 (gB amask col rb ret tail) M)
      (callState s 12966 (wd amask :: wd 15410 :: gB amask col rb ret tail) M) 18 := by
  opt87_reach [6920, 6921, 6922, 6923, 6924]

theorem g1_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 15410 (ok :: gB amask col rb ret tail) M)
      (callState s 11947 (wd (64 * (col % 4)) :: wd (ZH + 8192 * (col / 4)) ::
        wd (MlDsaOpt87.Proofs.ACC + 8192 * rb) :: wd 15355 :: ok :: gB amask col rb ret tail) M) 66 := by
  interval_cases col <;> interval_cases rb <;>
  opt87_reach [6925, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811,
    6812, 6813, 6814, 6815, 6816, 6817, 6818] with [ZH, MlDsaOpt87.Proofs.ACC]

theorem g1_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 15355 (ok :: gB amask col rb ret tail) M)
      (callState s 15418 (wd ret :: ok :: tail) M) 19 := by
  opt87_reach [6819, 6926, 6927, 6928, 6929, 6930, 6931, 6932]

end MlDsaOpt87.Proofs.GroupP
