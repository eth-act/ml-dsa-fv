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
      Reach (callState s (15202 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 22461 (wd (15210 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6743, 6744, 6745, 6746]
  · opt87_reach [6753, 6754, 6755, 6756]
  · opt87_reach [6763, 6764, 6765, 6766]
  · opt87_reach [6773, 6774, 6775, 6776]
  · opt87_reach [6783, 6784, 6785, 6786]

theorem g1_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (15210 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 10772 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (15224 + 22 * b) ::
          gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt87_reach [6747, 6748, 6749, 6750, 6751, 6752] with [FL, ABUF]
  · opt87_reach [6757, 6758, 6759, 6760, 6761, 6762] with [FL, ABUF]
  · opt87_reach [6767, 6768, 6769, 6770, 6771, 6772] with [FL, ABUF]
  · opt87_reach [6777, 6778, 6779, 6780, 6781, 6782] with [FL, ABUF]
  · opt87_reach [6787, 6788, 6789, 6790, 6791, 6792] with [FL, ABUF]

theorem g1_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 15312 (gB amask col rb ret tail) M)
      (callState s 12615 (wd amask :: wd 15321 :: gB amask col rb ret tail) M) 18 := by
  opt87_reach [6793, 6794, 6795, 6796, 6797]

theorem g1_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 15321 (ok :: gB amask col rb ret tail) M)
      (callState s 11947 (wd (64 * (col % 4)) :: wd (ZH + 8192 * (col / 4)) ::
        wd (MlDsaOpt87.Proofs.ACC + 8192 * rb) :: wd 15355 :: ok :: gB amask col rb ret tail) M) 66 := by
  interval_cases col <;> interval_cases rb <;>
  opt87_reach [6798, 6799, 6800, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811,
    6812, 6813, 6814, 6815, 6816, 6817, 6818] with [ZH, MlDsaOpt87.Proofs.ACC]

theorem g1_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 15355 (ok :: gB amask col rb ret tail) M)
      (callState s 15363 (wd ret :: ok :: tail) M) 19 := by
  opt87_reach [6819, 6820, 6821, 6822, 6823, 6824, 6825, 6826]

end MlDsaOpt87.Proofs.GroupP
