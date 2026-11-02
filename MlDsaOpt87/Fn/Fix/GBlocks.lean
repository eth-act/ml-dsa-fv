import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `13164, 13213, 13265, 13317` and the exit `13369`, stack
`flags :: ok :: amask :: ret :: tail`. Bit 0 of `flags` records that `blkt`
has made the tail of block 4 (before the group's first `fix`).
-/

namespace MlDsaOpt87.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- The OR of the first 32 flag words, masked to bit 23 of each lane (as `gfix` computes it). -/
def gflags (M : ByteArray) : Nat :=
  52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232))))))))))))))))))))))))))))))))

theorem gflags_def (M : ByteArray) : 52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232)))))))))))))))))))))))))))))))) = gflags M := rfl

theorem gflags_lt (M : ByteArray) : gflags M < 2 ^ 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem gflags_mod (M : ByteArray) :
    gflags M % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = gflags M :=
  Nat.mod_eq_of_lt (gflags_lt M)

theorem gone_land (x : Nat) : 1 &&& x = x % 2 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 1

theorem gmod2_mod (x : Nat) :
    x % 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = x % 2 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

macro "gx_close" : tactic => `(tactic| (all_goals first | (congr 1; omega) | rfl | skip))


theorem gx_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 12966 (wd amask :: wd ret :: tail) M)
      (callState s 13164 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  opt87_reach [5624, 5625, 5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633, 5634, 5635, 5636, 5637, 5638, 5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647, 5648, 5649, 5650, 5651, 5652, 5653, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661, 5662, 5663, 5664, 5665, 5666, 5667, 5668, 5669, 5670, 5671, 5672, 5673, 5674, 5675, 5676, 5677, 5678, 5679, 5680, 5681, 5682, 5683, 5684, 5685, 5686, 5687, 5688, 5689, 5690, 5691, 5692, 5693, 5694, 5695, 5696, 5697, 5698, 5699, 5700, 5701, 5702, 5703, 5704, 5705, 5706, 5707, 5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 12966 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  opt87_reach [5624, 5625, 5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633, 5634, 5635, 5636, 5637, 5638, 5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647, 5648, 5649, 5650, 5651, 5652, 5653, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661, 5662, 5663, 5664, 5665, 5666, 5667, 5668, 5669, 5670, 5671, 5672, 5673, 5674, 5675, 5676, 5677, 5678, 5679, 5680, 5681, 5682, 5683, 5684, 5685, 5686, 5687, 5688, 5689, 5690, 5691, 5692, 5693, 5694, 5695, 5696, 5697, 5698, 5699, 5700, 5701, 5702, 5703, 5704, 5705, 5706, 5707, 5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727, 5864, 5865, 5866, 5867, 5868, 5869] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 13164 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13213 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  opt87_reach [5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 13164 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12179 (wd 13195 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 78 := by
  opt87_reach [5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744, 5745, 5746, 5747] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 13195 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 0 :: wd 13208 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 24 := by
  opt87_reach [5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755]
  gx_close

theorem gx_callF0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 13164 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 0 :: wd 13208 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 81 := by
  opt87_reach [5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744, 5751, 5752, 5753, 5754, 5755] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 13208 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13213 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5756, 5757, 5758, 5759, 5760]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 13213 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13265 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 13213 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12179 (wd 13246 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt87_reach [5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778, 5779, 5780, 5781] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 13246 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 64 :: wd 13260 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt87_reach [5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789]
  gx_close

theorem gx_callF1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 13213 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 64 :: wd 13260 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt87_reach [5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778, 5785, 5786, 5787, 5788, 5789] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 13260 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13265 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5790, 5791, 5792, 5793, 5794]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 13265 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13317 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5795, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 13265 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12179 (wd 13298 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt87_reach [5795, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 13298 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 128 :: wd 13312 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt87_reach [5816, 5817, 5818, 5819, 5820, 5821, 5822, 5823]
  gx_close

theorem gx_callF2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 13265 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 128 :: wd 13312 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt87_reach [5795, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5819, 5820, 5821, 5822, 5823] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 13312 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13317 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5824, 5825, 5826, 5827, 5828]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 13317 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13369 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 13317 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12179 (wd 13350 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt87_reach [5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5847, 5848, 5849] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 13350 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 192 :: wd 13364 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt87_reach [5850, 5851, 5852, 5853, 5854, 5855, 5856, 5857]
  gx_close

theorem gx_callF3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 13317 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14669 (wd 192 :: wd 13364 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt87_reach [5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5853, 5854, 5855, 5856, 5857] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 13364 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13369 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5858, 5859, 5860, 5861, 5862]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 13369 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  opt87_reach [5863, 5864, 5865, 5866, 5867, 5868, 5869]  with [hj]
  gx_close

end MlDsaOpt87.Proofs.Fix
