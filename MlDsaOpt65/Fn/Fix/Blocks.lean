import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py 65` --sub 65280=89856 --sub 66080=90656; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`G`/`(pc := _)`/`(ret := _)`/`(rT := _)`/`(rF := _)` and the `reach_mcopy` index relocated by hand (`proofgen_port.maps 65`)
set_option warningAsError true
/-!
# `fix`: straight-line blocks (v4)

Entry at pc 13941 (`[sh, ret]`); first-flag scan head `fxf1` at pc 13973
(`sst`: stack `rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`);
group-loop head `fxg` at pc 13999 (`gst`: stack
`wp :: rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`). The flag
word of the group at `rp` is read at `rp / 8 + 28672` (`FL − ABUF / 8`).
-/

namespace MlDsaOpt65.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

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
  callState s 13973 (wd rp :: wd 29440 :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

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
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 13941 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh)
        (8380417 * 2 ^ sh) (8388608 * 2 ^ sh) 20480 m) 40 := by
  have hlm := lm_lt sh hsh
  have hqs := qs_lt sh hsh
  have hfm := fm_lt sh hsh
  opt65_reach [6111, 6112, 6113, 6114, 6115, 6116, 6117, 6118, 6119, 6120, 6121, 6122, 6123, 6124]
    with [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlm, Nat.mod_eq_of_lt hqs, Nat.mod_eq_of_lt hfm]
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (sst s ret tail sh lm nm qs fm (256 + rp) M) 55 := by
  opt65_reach [6125, 6126, 6127, 6128, 6129, 6130, 6131, 6132, 6133, 6134, 6135, 6136, 6137, 6138, 6139]
    with [land_word_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (gst s ret tail sh lm nm qs fm 13999 29440 rp rp M) 42 := by
  opt65_reach [6125, 6126, 6127, 6128, 6129, 6130, 6131, 6132, 6133, 6134, 6135, 6140, 6141]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 13999 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14190 rlim rp wp M) 38 := by
  opt65_reach [6142, 6143, 6144, 6145, 6146, 6147, 6148, 6149, 6150, 6151, 6152]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (gst s ret tail sh lm nm qs fm 13999 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14015 rlim rp wp M) 38 := by
  opt65_reach [6142, 6143, 6144, 6145, 6146, 6147, 6148, 6149, 6150, 6151, 6152]
    with [land_word_mod, hf]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14015 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14027 rlim rp wp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 36 := by
  opt65_reach [6153, 6154, 6155, 6156, 6157, 6158, 6159, 6160, 6161, 6162, 6163, 6164] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14027 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14045 rlim rp wp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 48 := by
  opt65_reach [6165, 6166, 6167, 6168, 6169, 6170, 6171, 6172, 6173, 6174, 6175, 6176, 6177, 6178, 6179, 6180] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14045 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14063 rlim rp wp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 48 := by
  opt65_reach [6181, 6182, 6183, 6184, 6185, 6186, 6187, 6188, 6189, 6190, 6191, 6192, 6193, 6194, 6195, 6196] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14063 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14081 rlim rp wp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 48 := by
  opt65_reach [6197, 6198, 6199, 6200, 6201, 6202, 6203, 6204, 6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14081 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14099 rlim rp wp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 48 := by
  opt65_reach [6213, 6214, 6215, 6216, 6217, 6218, 6219, 6220, 6221, 6222, 6223, 6224, 6225, 6226, 6227, 6228] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14099 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14117 rlim rp wp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 48 := by
  opt65_reach [6229, 6230, 6231, 6232, 6233, 6234, 6235, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243, 6244] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14117 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14135 rlim rp wp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 48 := by
  opt65_reach [6245, 6246, 6247, 6248, 6249, 6250, 6251, 6252, 6253, 6254, 6255, 6256, 6257, 6258, 6259, 6260] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 90656) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14135 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14153 rlim rp wp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 48 := by
  opt65_reach [6261, 6262, 6263, 6264, 6265, 6266, 6267, 6268, 6269, 6270, 6271, 6272, 6273, 6274, 6275, 6276] with [cw, Nat.zero_add]
  fx_close

theorem fx_cand0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14190 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14209 rlim rp (wp + acc qs (lm &&& word M (32 * 0 + rp)) * 32)
        (cw M wp (32 * 0 + rp) lm nm)) 52 := by
  opt65_reach [6300, 6301, 6302, 6303, 6304, 6305, 6306, 6307, 6308, 6309, 6310, 6311, 6312, 6313, 6314, 6315, 6316, 6317] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14209 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14230 rlim rp (wp + acc qs (lm &&& word M (32 * 1 + rp)) * 32)
        (cw M wp (32 * 1 + rp) lm nm)) 57 := by
  opt65_reach [6318, 6319, 6320, 6321, 6322, 6323, 6324, 6325, 6326, 6327, 6328, 6329, 6330, 6331, 6332, 6333, 6334, 6335, 6336] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14230 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14251 rlim rp (wp + acc qs (lm &&& word M (32 * 2 + rp)) * 32)
        (cw M wp (32 * 2 + rp) lm nm)) 57 := by
  opt65_reach [6337, 6338, 6339, 6340, 6341, 6342, 6343, 6344, 6345, 6346, 6347, 6348, 6349, 6350, 6351, 6352, 6353, 6354, 6355] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14251 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14272 rlim rp (wp + acc qs (lm &&& word M (32 * 3 + rp)) * 32)
        (cw M wp (32 * 3 + rp) lm nm)) 57 := by
  opt65_reach [6356, 6357, 6358, 6359, 6360, 6361, 6362, 6363, 6364, 6365, 6366, 6367, 6368, 6369, 6370, 6371, 6372, 6373, 6374] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14272 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14293 rlim rp (wp + acc qs (lm &&& word M (32 * 4 + rp)) * 32)
        (cw M wp (32 * 4 + rp) lm nm)) 57 := by
  opt65_reach [6375, 6376, 6377, 6378, 6379, 6380, 6381, 6382, 6383, 6384, 6385, 6386, 6387, 6388, 6389, 6390, 6391, 6392, 6393] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14293 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14314 rlim rp (wp + acc qs (lm &&& word M (32 * 5 + rp)) * 32)
        (cw M wp (32 * 5 + rp) lm nm)) 57 := by
  opt65_reach [6394, 6395, 6396, 6397, 6398, 6399, 6400, 6401, 6402, 6403, 6404, 6405, 6406, 6407, 6408, 6409, 6410, 6411, 6412] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14314 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14335 rlim rp (wp + acc qs (lm &&& word M (32 * 6 + rp)) * 32)
        (cw M wp (32 * 6 + rp) lm nm)) 57 := by
  opt65_reach [6413, 6414, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422, 6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 90656) (hwp : wp + 32 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14335 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14356 rlim rp (wp + acc qs (lm &&& word M (32 * 7 + rp)) * 32)
        (cw M wp (32 * 7 + rp) lm nm)) 57 := by
  opt65_reach [6432, 6433, 6434, 6435, 6436, 6437, 6438, 6439, 6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hwp : wp + 256 ≤ 90656) :
    Reach (gst s ret tail sh lm nm qs fm 14153 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14157 rlim rp (256 + wp) M) 6 := by
  opt65_reach [6277, 6278]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 14356 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14157 rlim rp wp M) 11 := by
  opt65_reach [6451, 6452]
  fx_close

theorem fx_gn_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : 256 + rp < rlim) :
    Reach (gst s ret tail sh lm nm qs fm 14157 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13999 rlim (256 + rp) wp M) 47 := by
  opt65_reach [6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292]
  fx_close

theorem fx_gn_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : rlim ≤ 256 + rp) :
    Reach (gst s ret tail sh lm nm qs fm 14157 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14360 rlim (256 + rp) wp M) 80 := by
  opt65_reach [6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292, 6293, 6294, 6295, 6296, 6297, 6298, 6299]
  fx_close

theorem fx_gn_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : 28672 ≤ wp) (hwp' : wp < 65536)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 14157 rlim rp wp M)
      (callState s ret (wd 1 :: tail) M) 100 := by
  opt65_reach [6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292, 6293, 6294, 6295, 6296, 6297, 6491, 6492, 6493, 6494, 6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502] with [hj, Nat.and_zero, Nat.zero_and]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp wp : Nat)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 14360 31232 rp wp M)
      (callState s ret (wd 0 :: tail) M) 53 := by
  opt65_reach [6453, 6454, 6455, 6456, 6457, 6458, 6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512, 6513, 6514] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 14360 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14424 rlim rp wp M) 42 := by
  opt65_reach [6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460, 6461, 6462]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 14424 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 13999 31232 rp wp M) 23 := by
  opt65_reach [6484, 6485, 6486, 6487, 6488, 6489, 6490]
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm qs fm 14360 rlim rp wp M)
      (callState s 14392 (wd 89856 :: wd 0 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt65_reach [6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460, 6461, 6462, 6463, 6464, 6465, 6466, 6467, 6468]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 14393 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 22528 (wd 14400 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm ::
        wd sh :: wd ret :: tail) M) 14 := by
  opt65_reach [6470, 6471, 6472]
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 14400 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 9815 (wd 32352 :: wd 29440 :: wd 14414 :: wd wp :: wd rp :: wd rlim :: wd fm ::
        wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt65_reach [6473, 6474, 6475, 6476, 6477, 6478]
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2865 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 14414 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 14423 (wd 0 :: wd 89856 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt65_reach [6479, 6480, 6481, 6482]
  fx_close

end MlDsaOpt65.Proofs.Fix
