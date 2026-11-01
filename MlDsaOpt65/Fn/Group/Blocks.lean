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
      Reach (callState s (14730 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 21901 (wd (14738 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6490, 6491, 6492, 6493]
  · opt65_reach [6500, 6501, 6502, 6503]
  · opt65_reach [6510, 6511, 6512, 6513]
  · opt65_reach [6520, 6521, 6522, 6523]
  · opt65_reach [6530, 6531, 6532, 6533]

theorem g1_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (14738 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 9811 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (14752 + 22 * b) ::
          gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6494, 6495, 6496, 6497, 6498, 6499] with [FL, ABUF]
  · opt65_reach [6504, 6505, 6506, 6507, 6508, 6509] with [FL, ABUF]
  · opt65_reach [6514, 6515, 6516, 6517, 6518, 6519] with [FL, ABUF]
  · opt65_reach [6524, 6525, 6526, 6527, 6528, 6529] with [FL, ABUF]
  · opt65_reach [6534, 6535, 6536, 6537, 6538, 6539] with [FL, ABUF]

theorem g1_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 14840 (gB amask col rb ret tail) M)
      (callState s 11685 (wd amask :: wd 14849 :: gB amask col rb ret tail) M) 18 := by
  opt65_reach [6540, 6541, 6542, 6543, 6544]

theorem g1_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 14849 (ok :: gB amask col rb ret tail) M)
      (callState s 10986 (wd (64 * (col % 4)) :: wd (ZH + 8192 * (col / 4)) ::
        wd (MlDsaOpt65.Proofs.ACC + 8192 * rb) :: wd 14883 :: ok :: gB amask col rb ret tail) M) 66 := by
  interval_cases col <;> interval_cases rb <;>
  opt65_reach [6545, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553, 6554, 6555, 6556, 6557, 6558,
    6559, 6560, 6561, 6562, 6563, 6564, 6565] with [ZH, MlDsaOpt65.Proofs.ACC]

theorem g1_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 14883 (ok :: gB amask col rb ret tail) M)
      (callState s 14891 (wd ret :: ok :: tail) M) 19 := by
  opt65_reach [6566, 6567, 6568, 6569, 6570, 6571, 6572, 6573]

end MlDsaOpt65.Proofs.GroupP
