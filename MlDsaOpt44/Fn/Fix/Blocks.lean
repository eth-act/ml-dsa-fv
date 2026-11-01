import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
set_option warningAsError true
/-!
# `fix`: straight-line blocks

Scan head `fxf1` at pc 12989 (stack `fp :: nm :: lm :: sh :: ret :: tail`),
group-loop head `fxg` at pc 13029 (`gst`: stack
`flim :: rp :: wp :: fp :: nm :: lm :: sh :: ret :: tail`).
-/

namespace MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

theorem one_land (x : Nat) : 1 &&& x = x % 2 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 1

theorem mod2_mod (x : Nat) :
    x % 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = x % 2 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem m64_land (x : Nat) : 18446744073709551615 &&& x = x % 2 ^ 64 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 64

theorem lm_lt (sh : Nat) (hsh : sh ≤ 192) :
    18446744073709551615 * 2 ^ sh <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have : 2 ^ sh ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) hsh
  calc 18446744073709551615 * 2 ^ sh ≤ 18446744073709551615 * 2 ^ 192 := Nat.mul_le_mul_left _ this
    _ < _ := by decide

/-- Group-loop layout. -/
abbrev gst (s : State) (ret : Nat) (tail : List UInt256) (sh lm nm pc flim rp wp fp : Nat)
    (M : ByteArray) : State :=
  callState s pc (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

/-- Scan layout. -/
abbrev sst (s : State) (ret : Nat) (tail : List UInt256) (sh lm nm fp : Nat) (M : ByteArray) :
    State :=
  callState s 12989 (wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

/-- Lane read by the flagged path. -/
def lv (M : ByteArray) (a sh : Nat) : Nat := word M a / 2 ^ sh % 18446744073709551616

/-- Flagged-path write of lane `sh` of `rp` into `wp`. -/
def fw (M : ByteArray) (wp rp sh nm : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded ((nm &&& word M wp ||| lv M rp sh * 2 ^ sh) %
    115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) wp

/-- Clean-path masked copy of `rp` into `wp`. -/
def cw (M : ByteArray) (wp rp lm nm : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded ((lm &&& word M rp ||| nm &&& word M wp) %
    115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) wp

/-- Acceptance bit. -/
def ab (v : Nat) : Nat := if 8380417 > v then 1 else 0

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

macro "fx_close" : tactic => `(tactic| (all_goals first | (congr 1; omega) | (refine ⟨?_, ?_⟩ <;> (congr 1; omega)) | rfl | skip))


theorem fx_cand0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13052 flim rp wp fp M)
      (gst s ret tail sh lm nm 13089 flim rp (wp + ab (lv M (32 * 0 + rp) sh) * 32) fp (fw M wp (32 * 0 + rp) sh nm)) 74 := by
  opt44_reach [5601, 5602, 5603, 5604, 5605, 5606, 5607, 5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622, 5623, 5624, 5625] with [m64_land, lv, fw, ab, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13089 flim rp wp fp M)
      (gst s ret tail sh lm nm 13129 flim rp (wp + ab (lv M (32 * 1 + rp) sh) * 32) fp (fw M wp (32 * 1 + rp) sh nm)) 80 := by
  opt44_reach [5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633, 5634, 5635, 5636, 5637, 5638, 5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647, 5648, 5649, 5650, 5651, 5652] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13129 flim rp wp fp M)
      (gst s ret tail sh lm nm 13169 flim rp (wp + ab (lv M (32 * 2 + rp) sh) * 32) fp (fw M wp (32 * 2 + rp) sh nm)) 80 := by
  opt44_reach [5653, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661, 5662, 5663, 5664, 5665, 5666, 5667, 5668, 5669, 5670, 5671, 5672, 5673, 5674, 5675, 5676, 5677, 5678, 5679] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13169 flim rp wp fp M)
      (gst s ret tail sh lm nm 13209 flim rp (wp + ab (lv M (32 * 3 + rp) sh) * 32) fp (fw M wp (32 * 3 + rp) sh nm)) 80 := by
  opt44_reach [5680, 5681, 5682, 5683, 5684, 5685, 5686, 5687, 5688, 5689, 5690, 5691, 5692, 5693, 5694, 5695, 5696, 5697, 5698, 5699, 5700, 5701, 5702, 5703, 5704, 5705, 5706] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13209 flim rp wp fp M)
      (gst s ret tail sh lm nm 13249 flim rp (wp + ab (lv M (32 * 4 + rp) sh) * 32) fp (fw M wp (32 * 4 + rp) sh nm)) 80 := by
  opt44_reach [5707, 5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727, 5728, 5729, 5730, 5731, 5732, 5733] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13249 flim rp wp fp M)
      (gst s ret tail sh lm nm 13289 flim rp (wp + ab (lv M (32 * 5 + rp) sh) * 32) fp (fw M wp (32 * 5 + rp) sh nm)) 80 := by
  opt44_reach [5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744, 5745, 5746, 5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5756, 5757, 5758, 5759, 5760] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13289 flim rp wp fp M)
      (gst s ret tail sh lm nm 13329 flim rp (wp + ab (lv M (32 * 6 + rp) sh) * 32) fp (fw M wp (32 * 6 + rp) sh nm)) 80 := by
  opt44_reach [5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778, 5779, 5780, 5781, 5782, 5783, 5784, 5785, 5786, 5787] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13329 flim rp wp fp M)
      (gst s ret tail sh lm nm 13369 flim rp (wp + ab (lv M (32 * 7 + rp) sh) * 32) fp (fw M wp (32 * 7 + rp) sh nm)) 80 := by
  opt44_reach [5788, 5789, 5790, 5791, 5792, 5793, 5794, 5795, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13379 flim rp wp fp M)
      (gst s ret tail sh lm nm 13394 flim rp wp fp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 43 := by
  opt44_reach [5821, 5822, 5823, 5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13394 flim rp wp fp M)
      (gst s ret tail sh lm nm 13414 flim rp wp fp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 54 := by
  opt44_reach [5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5847, 5848, 5849, 5850, 5851, 5852, 5853] with [cw]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13414 flim rp wp fp M)
      (gst s ret tail sh lm nm 13434 flim rp wp fp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 54 := by
  opt44_reach [5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863, 5864, 5865, 5866, 5867, 5868, 5869, 5870, 5871] with [cw]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13434 flim rp wp fp M)
      (gst s ret tail sh lm nm 13454 flim rp wp fp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 54 := by
  opt44_reach [5872, 5873, 5874, 5875, 5876, 5877, 5878, 5879, 5880, 5881, 5882, 5883, 5884, 5885, 5886, 5887, 5888, 5889] with [cw]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13454 flim rp wp fp M)
      (gst s ret tail sh lm nm 13474 flim rp wp fp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 54 := by
  opt44_reach [5890, 5891, 5892, 5893, 5894, 5895, 5896, 5897, 5898, 5899, 5900, 5901, 5902, 5903, 5904, 5905, 5906, 5907] with [cw]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13474 flim rp wp fp M)
      (gst s ret tail sh lm nm 13494 flim rp wp fp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 54 := by
  opt44_reach [5908, 5909, 5910, 5911, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925] with [cw]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13494 flim rp wp fp M)
      (gst s ret tail sh lm nm 13514 flim rp wp fp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 54 := by
  opt44_reach [5926, 5927, 5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943] with [cw]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm 13514 flim rp wp fp M)
      (gst s ret tail sh lm nm 13534 flim rp wp fp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 54 := by
  opt44_reach [5944, 5945, 5946, 5947, 5948, 5949, 5950, 5951, 5952, 5953, 5954, 5955, 5956, 5957, 5958, 5959, 5960, 5961] with [cw]
  fx_close

theorem fx_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 12972 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh) 31232 m) 19 := by
  have hlm := lm_lt sh hsh
  opt44_reach [5551, 5552, 5553, 5554, 5555, 5556, 5557] 
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 66080) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (sst s ret tail sh lm nm fp M)
      (sst s ret tail sh lm nm (32 + fp) M) 55 := by
  opt44_reach [5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 66080) (hfl : 31232 ≤ fp) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (sst s ret tail sh lm nm fp M)
      (gst s ret tail sh lm nm 13029 32352 (20480 + (fp - 31232) * 8) (20480 + (fp - 31232) * 8) fp M) 69 := by
  opt44_reach [5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565, 5566, 5567, 5568, 5573, 5574, 5575, 5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfe : fp = flim) (hfp : fp + 32 ≤ 66080) (hfl : flim < 65536) :
    Reach (gst s ret tail sh lm nm 13029 flim rp wp fp M)
      (gst s ret tail sh lm nm 13565 flim rp wp fp M) 23 := by
  opt44_reach [5584, 5585, 5586, 5587, 5588, 5589] 
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 66080) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (gst s ret tail sh lm nm 13029 flim rp wp fp M)
      (gst s ret tail sh lm nm 13052 flim rp wp fp M) 63 := by
  opt44_reach [5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591, 5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 66080) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (gst s ret tail sh lm nm 13029 flim rp wp fp M)
      (gst s ret tail sh lm nm 13379 flim rp wp fp M) 63 := by
  opt44_reach [5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591, 5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) :
    Reach (gst s ret tail sh lm nm 13369 flim rp wp fp M)
      (gst s ret tail sh lm nm 13546 flim (256 + rp) wp fp M) 23 := by
  opt44_reach [5815, 5816, 5817, 5818, 5819, 5820] 
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) (hwp : wp < 65536) :
    Reach (gst s ret tail sh lm nm 13534 flim rp wp fp M)
      (gst s ret tail sh lm nm 13546 flim (256 + rp) (256 + wp) fp M) 24 := by
  opt44_reach [5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969] 
  fx_close

theorem fx_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : wp ≤ 28671) :
    Reach (gst s ret tail sh lm nm 13546 flim rp wp fp M)
      (gst s ret tail sh lm nm 13029 flim rp wp (32 + fp) M) 46 := by
  opt44_reach [5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981] 
  fx_close

theorem fx_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : 28671 < wp) (hwp : wp < 65536) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 13546 flim rp wp fp M)
      (callState s ret (wd 1 :: tail) M) 64 := by
  opt44_reach [5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028] with [hj]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm rp wp fp : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 13565 32576 rp wp fp M)
      (callState s ret (wd 0 :: tail) M) 51 := by
  opt44_reach [5982, 5983, 5984, 5985, 5986, 5987, 6029, 6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037, 6038, 6039] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm 13565 flim rp wp fp M)
      (gst s ret tail sh lm nm 13627 flim rp wp fp M) 42 := by
  opt44_reach [5982, 5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991] with [h6]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (gst s ret tail sh lm nm 13627 flim rp wp fp M)
      (gst s ret tail sh lm nm 13029 32576 rp wp fp M) 17 := by
  opt44_reach [6013, 6014, 6015, 6016, 6017] 
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm 13565 flim rp wp fp M)
      (callState s 13596 (wd 65280 :: wd 0 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt44_reach [5982, 5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991, 5992, 5993, 5994, 5995, 5996, 5997] with [h6]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 13597 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 21570 (wd 13604 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 14 := by
  opt44_reach [5999, 6000, 6001] 
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 13604 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 8887 (wd 32352 :: wd 29440 :: wd 13618 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt44_reach [6002, 6003, 6004, 6005, 6006, 6007] 
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2097 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 13618 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 13626 (wd 0 :: wd 65280 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt44_reach [6008, 6009, 6010, 6011] 
  fx_close

end MlDsaOpt44.Proofs.Fix
