import MlDsaOpt65.Fn.Group.Squeeze
set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-65): glue blocks between the calls (WP G1)

Ported from `MlDsaOpt44/Fn/Group/Main.lean` (instruction indices = 44 + 223):
the five `kf4` / `blk` call sites, the `gfix amask` call, the `pass3` call
with `zh = ZH + 0x2000 (col / 4)`, `acc = ACC + 0x2000 rb`, and the epilogue.
-/

namespace MlDsaOpt65.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

theorem g1_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (14359 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 20991 (wd (14367 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6320, 6321, 6322, 6323]
  · opt65_reach [6330, 6331, 6332, 6333]
  · opt65_reach [6340, 6341, 6342, 6343]
  · opt65_reach [6350, 6351, 6352, 6353]
  · opt65_reach [6360, 6361, 6362, 6363]

theorem g1_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (14367 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 9857 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (14381 + 22 * b) ::
          gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6324, 6325, 6326, 6327, 6328, 6329] with [FL, ABUF]
  · opt65_reach [6334, 6335, 6336, 6337, 6338, 6339] with [FL, ABUF]
  · opt65_reach [6344, 6345, 6346, 6347, 6348, 6349] with [FL, ABUF]
  · opt65_reach [6354, 6355, 6356, 6357, 6358, 6359] with [FL, ABUF]
  · opt65_reach [6364, 6365, 6366, 6367, 6368, 6369] with [FL, ABUF]

theorem g1_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 14469 (gB amask col rb ret tail) M)
      (callState s 11314 (wd amask :: wd 14478 :: gB amask col rb ret tail) M) 18 := by
  opt65_reach [6370, 6371, 6372, 6373, 6374]

theorem g1_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 14478 (ok :: gB amask col rb ret tail) M)
      (callState s 11032 (wd (64 * (col % 4)) :: wd (ZH + 8192 * (col / 4)) ::
        wd (MlDsaOpt65.Proofs.ACC + 8192 * rb) :: wd 14512 :: ok :: gB amask col rb ret tail) M) 66 := by
  interval_cases col <;> interval_cases rb <;>
  opt65_reach [6375, 6376, 6377, 6378, 6379, 6380, 6381, 6382, 6383, 6384, 6385, 6386, 6387, 6388,
    6389, 6390, 6391, 6392, 6393, 6394, 6395] with [ZH, MlDsaOpt65.Proofs.ACC]

theorem g1_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 14512 (ok :: gB amask col rb ret tail) M)
      (callState s 14520 (wd ret :: ok :: tail) M) 19 := by
  opt65_reach [6396, 6397, 6398, 6399, 6400, 6401, 6402, 6403]

end MlDsaOpt65.Proofs.GroupP
