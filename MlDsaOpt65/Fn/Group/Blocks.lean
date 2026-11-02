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
      Reach (callState s (14563 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 22528 (wd (14571 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6572, 6573, 6574, 6575]
  · opt65_reach [6582, 6583, 6584, 6585]
  · opt65_reach [6592, 6593, 6594, 6595]
  · opt65_reach [6602, 6603, 6604, 6605]
  · opt65_reach [6612, 6613, 6614, 6615]

theorem g1_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M,
      Reach (callState s (14571 + 22 * b) (gB amask col rb ret tail) M)
        (callState s 9820 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (14585 + 22 * b) ::
          gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt65_reach [6576, 6577, 6578, 6579, 6580, 6581] with [FL, ABUF]
  · opt65_reach [6586, 6587, 6588, 6589, 6590, 6591] with [FL, ABUF]
  · opt65_reach [6596, 6597, 6598, 6599, 6600, 6601] with [FL, ABUF]
  · opt65_reach [6606, 6607, 6608, 6609, 6610, 6611] with [FL, ABUF]
  · opt65_reach [6616, 6617, 6618, 6619, 6620, 6621] with [FL, ABUF]

theorem g1_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 14673 (gB amask col rb ret tail) M)
      (callState s 11577 (wd amask :: wd 14682 :: gB amask col rb ret tail) M) 18 := by
  opt65_reach [6622, 6623, 6624, 6625, 6626]

theorem g1_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 14682 (ok :: gB amask col rb ret tail) M)
      (callState s 10986 (wd (64 * (col % 4)) :: wd (ZH + 8192 * (col / 4)) ::
        wd (MlDsaOpt65.Proofs.ACC + 8192 * rb) :: wd 14883 :: ok :: gB amask col rb ret tail) M) 66 := by
  interval_cases col <;> interval_cases rb <;>
  opt65_reach [6627, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553, 6554, 6555, 6556, 6557, 6558,
    6559, 6560, 6561, 6562, 6236, 6564, 6565] with [ZH, MlDsaOpt65.Proofs.ACC]

theorem g1_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 14883 (ok :: gB amask col rb ret tail) M)
      (callState s 14690 (wd ret :: ok :: tail) M) 19 := by
  opt65_reach [6566, 6628, 6629, 6630, 6631, 6632, 6633, 6634]

end MlDsaOpt65.Proofs.GroupP
