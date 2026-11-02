import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
set_option warningAsError true
/-!
# `fix`: straight-line blocks (v4)

Entry at pc 13206 (`[sh, ret]`); first-flag scan head `fxf1` at pc 13238
(`sst`: stack `rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`);
group-loop head `fxg` at pc 13264 (`gst`: stack
`wp :: rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`). The flag
word of the group at `rp` is read at `rp / 8 + 28672` (`FL − ABUF / 8`).
-/

namespace MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

theorem lm_lt (sh : Nat) (hsh : sh ≤ 192) :
    18446744073709551615 * 2 ^ sh <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have : 2 ^ sh ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) hsh
  calc 18446744073709551615 * 2 ^ sh ≤ 18446744073709551615 * 2 ^ 192 := Nat.mul_le_mul_left _ this
    _ < _ := by decide

theorem qs_lt (sh : Nat) (hsh : sh ≤ 192) :
    8380417 * 2 ^ sh <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have : 2 ^ sh ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) hsh
  calc 8380417 * 2 ^ sh ≤ 8380417 * 2 ^ 192 := Nat.mul_le_mul_left _ this
    _ < _ := by decide

theorem fm_lt (sh : Nat) (hsh : sh ≤ 192) :
    8388608 * 2 ^ sh <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have : 2 ^ sh ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) hsh
  calc 8388608 * 2 ^ sh ≤ 8388608 * 2 ^ 192 := Nat.mul_le_mul_left _ this
    _ < _ := by decide

theorem land_word_mod (a : Nat) (M : ByteArray) (x : Nat) :
    (a &&& word M x) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      a &&& word M x :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (word_lt M x))

/-- Group-loop layout. -/
abbrev gst (s : State) (ret : Nat) (tail : List UInt256) (sh lm nm qs fm pc rlim rp wp : Nat)
    (M : ByteArray) : State :=
  callState s pc (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh :: wd ret ::
    tail) M

/-- Scan layout. -/
abbrev sst (s : State) (ret : Nat) (tail : List UInt256) (sh lm nm qs fm rp : Nat) (M : ByteArray) :
    State :=
  callState s 13238 (wd rp :: wd 29440 :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

/-- Masked copy of lane `lm` of `rp` into `wp` (the other lanes of `wp` kept):
both the clean-group copies and the flagged-group writes. -/
def cw (M : ByteArray) (wp rp lm nm : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded ((lm &&& word M rp ||| nm &&& word M wp) %
    115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) wp

/-- Acceptance bit of the flagged path: `q << sh > x`. -/
def acc (qs x : Nat) : Nat := if qs > x then 1 else 0

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

macro "fx_close" : tactic => `(tactic| (all_goals first | (congr 1; omega) | (refine ⟨?_, ?_⟩ <;> (congr 1; omega)) | rfl | skip))

theorem fx_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 13206 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh)
        (8380417 * 2 ^ sh) (8388608 * 2 ^ sh) 20480 m) 40 := by
  have hlm := lm_lt sh hsh
  have hqs := qs_lt sh hsh
  have hfm := fm_lt sh hsh
  opt44_reach [5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775, 5776, 5777, 5778, 5779]
    with [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlm, Nat.mod_eq_of_lt hqs, Nat.mod_eq_of_lt hfm]
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (sst s ret tail sh lm nm qs fm (256 + rp) M) 55 := by
  opt44_reach [5780, 5781, 5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789, 5790, 5791, 5792, 5793, 5794]
    with [land_word_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (gst s ret tail sh lm nm qs fm 13264 29440 rp rp M) 42 := by
  opt44_reach [5780, 5781, 5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789, 5790, 5795, 5796]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 13264 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13455 rlim rp wp M) 38 := by
  opt44_reach [5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (gst s ret tail sh lm nm qs fm 13264 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13280 rlim rp wp M) 38 := by
  opt44_reach [5797, 5798, 5799, 5800, 5801, 5802, 5803, 5804, 5805, 5806, 5807]
    with [land_word_mod, hf]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13280 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13292 rlim rp wp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 36 := by
  opt44_reach [5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817, 5818, 5819] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13292 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13310 rlim rp wp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 48 := by
  opt44_reach [5820, 5821, 5822, 5823, 5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13310 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13328 rlim rp wp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 48 := by
  opt44_reach [5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5847, 5848, 5849, 5850, 5851] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13328 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13346 rlim rp wp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 48 := by
  opt44_reach [5852, 5853, 5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863, 5864, 5865, 5866, 5867] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13346 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13364 rlim rp wp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 48 := by
  opt44_reach [5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875, 5876, 5877, 5878, 5879, 5880, 5881, 5882, 5883] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13364 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13382 rlim rp wp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 48 := by
  opt44_reach [5884, 5885, 5886, 5887, 5888, 5889, 5890, 5891, 5892, 5893, 5894, 5895, 5896, 5897, 5898, 5899] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13382 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13400 rlim rp wp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 48 := by
  opt44_reach [5900, 5901, 5902, 5903, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5911, 5912, 5913, 5914, 5915] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 66080) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13400 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13418 rlim rp wp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 48 := by
  opt44_reach [5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927, 5928, 5929, 5930, 5931] with [cw, Nat.zero_add]
  fx_close

theorem fx_cand0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13455 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13474 rlim rp (wp + acc qs (lm &&& word M (32 * 0 + rp)) * 32)
        (cw M wp (32 * 0 + rp) lm nm)) 52 := by
  opt44_reach [5955, 5956, 5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13474 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13495 rlim rp (wp + acc qs (lm &&& word M (32 * 1 + rp)) * 32)
        (cw M wp (32 * 1 + rp) lm nm)) 57 := by
  opt44_reach [5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981, 5982, 5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13495 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13516 rlim rp (wp + acc qs (lm &&& word M (32 * 2 + rp)) * 32)
        (cw M wp (32 * 2 + rp) lm nm)) 57 := by
  opt44_reach [5992, 5993, 5994, 5995, 5996, 5997, 5998, 5999, 6000, 6001, 6002, 6003, 6004, 6005, 6006, 6007, 6008, 6009, 6010] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13516 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13537 rlim rp (wp + acc qs (lm &&& word M (32 * 3 + rp)) * 32)
        (cw M wp (32 * 3 + rp) lm nm)) 57 := by
  opt44_reach [6011, 6012, 6013, 6014, 6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13537 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13558 rlim rp (wp + acc qs (lm &&& word M (32 * 4 + rp)) * 32)
        (cw M wp (32 * 4 + rp) lm nm)) 57 := by
  opt44_reach [6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037, 6038, 6039, 6040, 6041, 6042, 6043, 6044, 6045, 6046, 6047, 6048] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13558 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13579 rlim rp (wp + acc qs (lm &&& word M (32 * 5 + rp)) * 32)
        (cw M wp (32 * 5 + rp) lm nm)) 57 := by
  opt44_reach [6049, 6050, 6051, 6052, 6053, 6054, 6055, 6056, 6057, 6058, 6059, 6060, 6061, 6062, 6063, 6064, 6065, 6066, 6067] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13579 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13600 rlim rp (wp + acc qs (lm &&& word M (32 * 6 + rp)) * 32)
        (cw M wp (32 * 6 + rp) lm nm)) 57 := by
  opt44_reach [6068, 6069, 6070, 6071, 6072, 6073, 6074, 6075, 6076, 6077, 6078, 6079, 6080, 6081, 6082, 6083, 6084, 6085, 6086] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 66080) (hwp : wp + 32 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13600 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13621 rlim rp (wp + acc qs (lm &&& word M (32 * 7 + rp)) * 32)
        (cw M wp (32 * 7 + rp) lm nm)) 57 := by
  opt44_reach [6087, 6088, 6089, 6090, 6091, 6092, 6093, 6094, 6095, 6096, 6097, 6098, 6099, 6100, 6101, 6102, 6103, 6104, 6105] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hwp : wp + 256 ≤ 66080) :
    Reach (gst s ret tail sh lm nm qs fm 13418 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13422 rlim rp (256 + wp) M) 6 := by
  opt44_reach [5932, 5933]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 13621 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13422 rlim rp wp M) 11 := by
  opt44_reach [6106, 6107]
  fx_close

theorem fx_gn_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : 256 + rp < rlim) :
    Reach (gst s ret tail sh lm nm qs fm 13422 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13264 rlim (256 + rp) wp M) 47 := by
  opt44_reach [5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943, 5944, 5945, 5946, 5947]
  fx_close

theorem fx_gn_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : rlim ≤ 256 + rp) :
    Reach (gst s ret tail sh lm nm qs fm 13422 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13625 rlim (256 + rp) wp M) 80 := by
  opt44_reach [5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943, 5944, 5945, 5946, 5947, 5948, 5949, 5950, 5951, 5952, 5953, 5954]
  fx_close

theorem fx_gn_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : 28672 ≤ wp) (hwp' : wp < 65536)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 13422 rlim rp wp M)
      (callState s ret (wd 1 :: tail) M) 100 := by
  opt44_reach [5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943, 5944, 5945, 5946, 5947, 5948, 5949, 5950, 5951, 5952, 6146, 6147, 6148, 6149, 6150, 6151, 6152, 6153, 6154, 6155, 6156, 6157] with [hj, Nat.and_zero, Nat.zero_and]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp wp : Nat)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 13625 31232 rp wp M)
      (callState s ret (wd 0 :: tail) M) 53 := by
  opt44_reach [6108, 6109, 6110, 6111, 6112, 6113, 6158, 6159, 6160, 6161, 6162, 6163, 6164, 6165, 6166, 6167, 6168, 6169] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 13625 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13687 rlim rp wp M) 42 := by
  opt44_reach [6108, 6109, 6110, 6111, 6112, 6113, 6114, 6115, 6116, 6117]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 13687 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13264 31232 rp wp M) 23 := by
  opt44_reach [6139, 6140, 6141, 6142, 6143, 6144, 6145]
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm qs fm 13625 rlim rp wp M)
      (callState s 13656 (wd 65280 :: wd 0 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt44_reach [6108, 6109, 6110, 6111, 6112, 6113, 6114, 6115, 6116, 6117, 6118, 6119, 6120, 6121, 6122, 6123]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 13657 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 22529 (wd 13664 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm ::
        wd sh :: wd ret :: tail) M) 14 := by
  opt44_reach [6125, 6126, 6127]
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 13664 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 9025 (wd 32352 :: wd 29440 :: wd 13678 :: wd wp :: wd rp :: wd rlim :: wd fm ::
        wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt44_reach [6128, 6129, 6130, 6131, 6132, 6133]
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 13678 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 13686 (wd 0 :: wd 65280 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt44_reach [6134, 6135, 6136, 6137]
  fx_close

end MlDsaOpt44.Proofs.Fix
