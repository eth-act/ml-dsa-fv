import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py 65` --sub 65280=89856 --sub 66080=90656; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`(pc := _)`/`(ret := _)` and the `reach_mcopy` index relocated by hand
set_option warningAsError true
/-!
# `fix`: straight-line blocks

Scan head `fxf1` at pc 12989 (stack `fp :: nm :: lm :: sh :: ret :: tail`),
group-loop head `fxg` at pc 13029 (`gst`: stack
`flim :: rp :: wp :: fp :: nm :: lm :: sh :: ret :: tail`).
-/

namespace MlDsaOpt65.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

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
  callState s 13584 (wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

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
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13647 flim rp wp fp M)
      (gst s ret tail sh lm nm 13684 flim rp (wp + ab (lv M (32 * 0 + rp) sh) * 32) fp (fw M wp (32 * 0 + rp) sh nm)) 74 := by
  opt65_reach [5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5847, 5848] with [m64_land, lv, fw, ab, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13684 flim rp wp fp M)
      (gst s ret tail sh lm nm 13724 flim rp (wp + ab (lv M (32 * 1 + rp) sh) * 32) fp (fw M wp (32 * 1 + rp) sh nm)) 80 := by
  opt65_reach [5849, 5850, 5851, 5852, 5853, 5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863, 5864, 5865, 5866, 5867, 5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13724 flim rp wp fp M)
      (gst s ret tail sh lm nm 13764 flim rp (wp + ab (lv M (32 * 2 + rp) sh) * 32) fp (fw M wp (32 * 2 + rp) sh nm)) 80 := by
  opt65_reach [5876, 5877, 5878, 5879, 5880, 5881, 5882, 5883, 5884, 5885, 5886, 5887, 5888, 5889, 5890, 5891, 5892, 5893, 5894, 5895, 5896, 5897, 5898, 5899, 5900, 5901, 5902] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13764 flim rp wp fp M)
      (gst s ret tail sh lm nm 13804 flim rp (wp + ab (lv M (32 * 3 + rp) sh) * 32) fp (fw M wp (32 * 3 + rp) sh nm)) 80 := by
  opt65_reach [5903, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5911, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927, 5928, 5929] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13804 flim rp wp fp M)
      (gst s ret tail sh lm nm 13844 flim rp (wp + ab (lv M (32 * 4 + rp) sh) * 32) fp (fw M wp (32 * 4 + rp) sh nm)) 80 := by
  opt65_reach [5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943, 5944, 5945, 5946, 5947, 5948, 5949, 5950, 5951, 5952, 5953, 5954, 5955, 5956] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13844 flim rp wp fp M)
      (gst s ret tail sh lm nm 13884 flim rp (wp + ab (lv M (32 * 5 + rp) sh) * 32) fp (fw M wp (32 * 5 + rp) sh nm)) 80 := by
  opt65_reach [5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981, 5982, 5983] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13884 flim rp wp fp M)
      (gst s ret tail sh lm nm 13924 flim rp (wp + ab (lv M (32 * 6 + rp) sh) * 32) fp (fw M wp (32 * 6 + rp) sh nm)) 80 := by
  opt65_reach [5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991, 5992, 5993, 5994, 5995, 5996, 5997, 5998, 5999, 6000, 6001, 6002, 6003, 6004, 6005, 6006, 6007, 6008, 6009, 6010] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13924 flim rp wp fp M)
      (gst s ret tail sh lm nm 13964 flim rp (wp + ab (lv M (32 * 7 + rp) sh) * 32) fp (fw M wp (32 * 7 + rp) sh nm)) 80 := by
  opt65_reach [6011, 6012, 6013, 6014, 6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029, 6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13974 flim rp wp fp M)
      (gst s ret tail sh lm nm 13989 flim rp wp fp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 43 := by
  opt65_reach [6044, 6045, 6046, 6047, 6048, 6049, 6050, 6051, 6052, 6053, 6054, 6055, 6056, 6057, 6058] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 13989 flim rp wp fp M)
      (gst s ret tail sh lm nm 14009 flim rp wp fp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 54 := by
  opt65_reach [6059, 6060, 6061, 6062, 6063, 6064, 6065, 6066, 6067, 6068, 6069, 6070, 6071, 6072, 6073, 6074, 6075, 6076] with [cw]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14009 flim rp wp fp M)
      (gst s ret tail sh lm nm 14029 flim rp wp fp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 54 := by
  opt65_reach [6077, 6078, 6079, 6080, 6081, 6082, 6083, 6084, 6085, 6086, 6087, 6088, 6089, 6090, 6091, 6092, 6093, 6094] with [cw]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14029 flim rp wp fp M)
      (gst s ret tail sh lm nm 14049 flim rp wp fp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 54 := by
  opt65_reach [6095, 6096, 6097, 6098, 6099, 6100, 6101, 6102, 6103, 6104, 6105, 6106, 6107, 6108, 6109, 6110, 6111, 6112] with [cw]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14049 flim rp wp fp M)
      (gst s ret tail sh lm nm 14069 flim rp wp fp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 54 := by
  opt65_reach [6113, 6114, 6115, 6116, 6117, 6118, 6119, 6120, 6121, 6122, 6123, 6124, 6125, 6126, 6127, 6128, 6129, 6130] with [cw]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14069 flim rp wp fp M)
      (gst s ret tail sh lm nm 14089 flim rp wp fp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 54 := by
  opt65_reach [6131, 6132, 6133, 6134, 6135, 6136, 6137, 6138, 6139, 6140, 6141, 6142, 6143, 6144, 6145, 6146, 6147, 6148] with [cw]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14089 flim rp wp fp M)
      (gst s ret tail sh lm nm 14109 flim rp wp fp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 54 := by
  opt65_reach [6149, 6150, 6151, 6152, 6153, 6154, 6155, 6156, 6157, 6158, 6159, 6160, 6161, 6162, 6163, 6164, 6165, 6166] with [cw]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm 14109 flim rp wp fp M)
      (gst s ret tail sh lm nm 14129 flim rp wp fp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 54 := by
  opt65_reach [6167, 6168, 6169, 6170, 6171, 6172, 6173, 6174, 6175, 6176, 6177, 6178, 6179, 6180, 6181, 6182, 6183, 6184] with [cw]
  fx_close

theorem fx_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 13567 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh) 31232 m) 19 := by
  have hlm := lm_lt sh hsh
  opt65_reach [5774, 5775, 5776, 5777, 5778, 5779, 5780] 
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 90656) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (sst s ret tail sh lm nm fp M)
      (sst s ret tail sh lm nm (32 + fp) M) 55 := by
  opt65_reach [5781, 5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789, 5790, 5791, 5792, 5793, 5794, 5795] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 90656) (hfl : 31232 ≤ fp) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (sst s ret tail sh lm nm fp M)
      (gst s ret tail sh lm nm 13624 32352 (20480 + (fp - 31232) * 8) (20480 + (fp - 31232) * 8) fp M) 69 := by
  opt65_reach [5781, 5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789, 5790, 5791, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfe : fp = flim) (hfp : fp + 32 ≤ 90656) (hfl : flim < 65536) :
    Reach (gst s ret tail sh lm nm 13624 flim rp wp fp M)
      (gst s ret tail sh lm nm 14160 flim rp wp fp M) 23 := by
  opt65_reach [5807, 5808, 5809, 5810, 5811, 5812] 
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 90656) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (gst s ret tail sh lm nm 13624 flim rp wp fp M)
      (gst s ret tail sh lm nm 13647 flim rp wp fp M) 63 := by
  opt65_reach [5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817, 5818, 5819, 5820, 5821, 5822, 5823] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 90656) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (gst s ret tail sh lm nm 13624 flim rp wp fp M)
      (gst s ret tail sh lm nm 13974 flim rp wp fp M) 63 := by
  opt65_reach [5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817, 5818, 5819, 5820, 5821, 5822, 5823] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) :
    Reach (gst s ret tail sh lm nm 13964 flim rp wp fp M)
      (gst s ret tail sh lm nm 14141 flim (256 + rp) wp fp M) 23 := by
  opt65_reach [6038, 6039, 6040, 6041, 6042, 6043] 
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) (hwp : wp < 65536) :
    Reach (gst s ret tail sh lm nm 14129 flim rp wp fp M)
      (gst s ret tail sh lm nm 14141 flim (256 + rp) (256 + wp) fp M) 24 := by
  opt65_reach [6185, 6186, 6187, 6188, 6189, 6190, 6191, 6192] 
  fx_close

theorem fx_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : wp ≤ 28671) :
    Reach (gst s ret tail sh lm nm 14141 flim rp wp fp M)
      (gst s ret tail sh lm nm 13624 flim rp wp (32 + fp) M) 46 := by
  opt65_reach [6193, 6194, 6195, 6196, 6197, 6198, 6199, 6200, 6201, 6202, 6203, 6204] 
  fx_close

theorem fx_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : 28671 < wp) (hwp : wp < 65536) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 14141 flim rp wp fp M)
      (callState s ret (wd 1 :: tail) M) 64 := by
  opt65_reach [6193, 6194, 6195, 6196, 6197, 6198, 6199, 6200, 6201, 6202, 6241, 6242, 6243, 6244, 6245, 6246, 6247, 6248, 6249, 6250, 6251] with [hj]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm rp wp fp : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 14160 32576 rp wp fp M)
      (callState s ret (wd 0 :: tail) M) 51 := by
  opt65_reach [6205, 6206, 6207, 6208, 6209, 6210, 6252, 6253, 6254, 6255, 6256, 6257, 6258, 6259, 6260, 6261, 6262] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm 14160 flim rp wp fp M)
      (gst s ret tail sh lm nm 14224 flim rp wp fp M) 42 := by
  opt65_reach [6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212, 6213, 6214] with [h6]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (gst s ret tail sh lm nm 14224 flim rp wp fp M)
      (gst s ret tail sh lm nm 13624 32576 rp wp fp M) 17 := by
  opt65_reach [6236, 6237, 6238, 6239, 6240] 
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm 14160 flim rp wp fp M)
      (callState s 14192 (wd 89856 :: wd 0 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt65_reach [6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212, 6213, 6214, 6215, 6216, 6217, 6218, 6219, 6220] with [h6]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 14193 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 20991 (wd 14200 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 14 := by
  opt65_reach [6222, 6223, 6224] 
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 14200 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 9857 (wd 32352 :: wd 29440 :: wd 14214 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt65_reach [6225, 6226, 6227, 6228, 6229, 6230] 
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2833 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 14214 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 14223 (wd 0 :: wd 89856 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt65_reach [6231, 6232, 6233, 6234] 
  fx_close

end MlDsaOpt65.Proofs.Fix
