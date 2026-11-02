import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`(pc := _)`/`(ret := _)` and the `reach_mcopy` index relocated by hand
set_option warningAsError true
/-!
# `fix`: straight-line blocks

Scan head `fxf1` at pc 12989 (stack `fp :: nm :: lm :: sh :: ret :: tail`),
group-loop head `fxg` at pc 13029 (`gst`: stack
`flim :: rp :: wp :: fp :: nm :: lm :: sh :: ret :: tail`).
-/

namespace MlDsaOpt87.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

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
  callState s 14701 (wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

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
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14490 flim rp wp fp M)
      (gst s ret tail sh lm nm 14527 flim rp (wp + ab (lv M (32 * 0 + rp) sh) * 32) fp (fw M wp (32 * 0 + rp) sh nm)) 74 := by
  opt87_reach [6247, 6248, 6249, 6250, 6251, 6252, 6451, 6254, 6255, 6256, 6257, 6258, 6259, 6260, 6261, 6262, 6263, 6264, 6265, 6266, 6267, 6268, 6269, 6270, 6271] with [m64_land, lv, fw, ab, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14527 flim rp wp fp M)
      (gst s ret tail sh lm nm 14567 flim rp (wp + ab (lv M (32 * 1 + rp) sh) * 32) fp (fw M wp (32 * 1 + rp) sh nm)) 80 := by
  opt87_reach [6272, 6273, 6274, 6275, 6276, 6277, 6278, 6279, 6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292, 6293, 6294, 6295, 6296, 6297, 6298] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14567 flim rp wp fp M)
      (gst s ret tail sh lm nm 14607 flim rp (wp + ab (lv M (32 * 2 + rp) sh) * 32) fp (fw M wp (32 * 2 + rp) sh nm)) 80 := by
  opt87_reach [6299, 6300, 6301, 6302, 6303, 6304, 6305, 6306, 6307, 6308, 6309, 6310, 6311, 6312, 6313, 6314, 6315, 6316, 6317, 6318, 6319, 6320, 6321, 6322, 6323, 6324, 6325] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14607 flim rp wp fp M)
      (gst s ret tail sh lm nm 14647 flim rp (wp + ab (lv M (32 * 3 + rp) sh) * 32) fp (fw M wp (32 * 3 + rp) sh nm)) 80 := by
  opt87_reach [6326, 6327, 6328, 6329, 6330, 6331, 6332, 6333, 6334, 6335, 6336, 6337, 6338, 6339, 6340, 6341, 6342, 6343, 6344, 6345, 6346, 6347, 6348, 6349, 6350, 6351, 6352] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14647 flim rp wp fp M)
      (gst s ret tail sh lm nm 14687 flim rp (wp + ab (lv M (32 * 4 + rp) sh) * 32) fp (fw M wp (32 * 4 + rp) sh nm)) 80 := by
  opt87_reach [6353, 6354, 6355, 6356, 6357, 6358, 6359, 6360, 6361, 6362, 6363, 6364, 6365, 6366, 6367, 6368, 6369, 6370, 6371, 6372, 6373, 6374, 6375, 6376, 6377, 6378, 6379] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14687 flim rp wp fp M)
      (gst s ret tail sh lm nm 14727 flim rp (wp + ab (lv M (32 * 5 + rp) sh) * 32) fp (fw M wp (32 * 5 + rp) sh nm)) 80 := by
  opt87_reach [6380, 6381, 6382, 6383, 6384, 6385, 6386, 6387, 6388, 6389, 6390, 6391, 6392, 6393, 6394, 6395, 6396, 6397, 6398, 6399, 6400, 6401, 6402, 6403, 6404, 6405, 6406] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14727 flim rp wp fp M)
      (gst s ret tail sh lm nm 14767 flim rp (wp + ab (lv M (32 * 6 + rp) sh) * 32) fp (fw M wp (32 * 6 + rp) sh nm)) 80 := by
  opt87_reach [6407, 6408, 6409, 6410, 6411, 6412, 6413, 6414, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422, 6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431, 6432, 6433] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14767 flim rp wp fp M)
      (gst s ret tail sh lm nm 14807 flim rp (wp + ab (lv M (32 * 7 + rp) sh) * 32) fp (fw M wp (32 * 7 + rp) sh nm)) 80 := by
  opt87_reach [6434, 6435, 6436, 6437, 6438, 6439, 6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450, 6451, 6452, 6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460] with [m64_land, lv, fw, ab]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14817 flim rp wp fp M)
      (gst s ret tail sh lm nm 14832 flim rp wp fp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 43 := by
  opt87_reach [6467, 6468, 6469, 6470, 6471, 6472, 6452, 6453, 6454, 6455, 6477, 6478, 6460, 6461, 6462] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14832 flim rp wp fp M)
      (gst s ret tail sh lm nm 14852 flim rp wp fp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 54 := by
  opt87_reach [6482, 6483, 6484, 6485, 6486, 6487, 6488, 6464, 6465, 6466, 6467, 6468, 6469, 6495, 6496, 6476, 6477, 6478] with [cw]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14852 flim rp wp fp M)
      (gst s ret tail sh lm nm 14872 flim rp wp fp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 54 := by
  opt87_reach [6500, 6501, 6502, 6503, 6504, 6505, 6506, 6480, 6481, 6482, 6483, 6484, 6485, 6513, 6514, 6492, 6493, 6494] with [cw]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14872 flim rp wp fp M)
      (gst s ret tail sh lm nm 14892 flim rp wp fp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 54 := by
  opt87_reach [6518, 6519, 6520, 6521, 6522, 6523, 6524, 6496, 6497, 6498, 6499, 6500, 6501, 6531, 6532, 6508, 6509, 6510] with [cw]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14892 flim rp wp fp M)
      (gst s ret tail sh lm nm 14912 flim rp wp fp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 54 := by
  opt87_reach [6536, 6537, 6538, 6539, 6540, 6541, 6542, 6512, 6513, 6514, 6515, 6516, 6517, 6549, 6550, 6524, 6525, 6526] with [cw]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14912 flim rp wp fp M)
      (gst s ret tail sh lm nm 14932 flim rp wp fp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 54 := by
  opt87_reach [6554, 6555, 6556, 6557, 6558, 6559, 6560, 6528, 6529, 6530, 6531, 6532, 6533, 6567, 6568, 6540, 6541, 6542] with [cw]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14932 flim rp wp fp M)
      (gst s ret tail sh lm nm 14952 flim rp wp fp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 54 := by
  opt87_reach [6572, 6573, 6574, 6575, 6576, 6577, 6578, 6544, 6545, 6546, 6547, 6548, 6549, 6585, 6586, 6556, 6557, 6558] with [cw]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm 14952 flim rp wp fp M)
      (gst s ret tail sh lm nm 14972 flim rp wp fp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 54 := by
  opt87_reach [6590, 6591, 6592, 6593, 6594, 6595, 6596, 6560, 6561, 6562, 6563, 6564, 6565, 6603, 6604, 6572, 6573, 6574] with [cw]
  fx_close

theorem fx_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 14669 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh) 31232 m) 19 := by
  have hlm := lm_lt sh hsh
  opt87_reach [6409, 6410, 6411, 6412, 6413, 6414, 6422] 
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 91680) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (sst s ret tail sh lm nm fp M)
      (sst s ret tail sh lm nm (32 + fp) M) 55 := by
  opt87_reach [6423, 6424, 6429, 6207, 6208, 6209, 6210, 6211, 6431, 6432, 6433, 6215, 6435, 6436, 6437] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm fp : Nat) (hsh : sh ≤ 192) (hfp : fp + 32 ≤ 91680) (hfl : 31232 ≤ fp) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (sst s ret tail sh lm nm fp M)
      (gst s ret tail sh lm nm 14467 32352 (20480 + (fp - 31232) * 8) (20480 + (fp - 31232) * 8) fp M) 69 := by
  opt87_reach [6423, 6424, 6429, 6207, 6208, 6209, 6210, 6211, 6431, 6432, 6433, 6438, 6439, 6221, 6222, 6223, 6442, 6225, 6444, 6445, 6228, 6229] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfe : fp = flim) (hfp : fp + 32 ≤ 91680) (hfl : flim < 65536) :
    Reach (gst s ret tail sh lm nm 14467 flim rp wp fp M)
      (gst s ret tail sh lm nm 14918 flim rp wp fp M) 23 := by
  opt87_reach [6230, 6231, 6232, 6233, 6449, 6450] 
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 91680) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 1) :
    Reach (gst s ret tail sh lm nm 14467 flim rp wp fp M)
      (gst s ret tail sh lm nm 14490 flim rp wp fp M) 63 := by
  opt87_reach [6230, 6231, 6232, 6233, 6449, 6450, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243, 6244, 6245, 6246] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hsh : sh ≤ 192) (hfe : fp ≠ flim) (hfp : fp + 32 ≤ 91680) (hfl : flim < 65536) (hf : word M fp / 2 ^ (23 + sh) % 2 = 0) :
    Reach (gst s ret tail sh lm nm 14467 flim rp wp fp M)
      (gst s ret tail sh lm nm 14817 flim rp wp fp M) 63 := by
  opt87_reach [6230, 6231, 6232, 6233, 6449, 6450, 6236, 6237, 6238, 6239, 6240, 6241, 6242, 6243, 6244, 6245, 6246] with [one_land, mod2_mod, hf]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) :
    Reach (gst s ret tail sh lm nm 14807 flim rp wp fp M)
      (gst s ret tail sh lm nm 14984 flim (256 + rp) wp fp M) 23 := by
  opt87_reach [6461, 6462, 6463, 6464, 6465, 6466] 
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hrp : rp < 65536) (hwp : wp < 65536) :
    Reach (gst s ret tail sh lm nm 14972 flim rp wp fp M)
      (gst s ret tail sh lm nm 14984 flim (256 + rp) (256 + wp) fp M) 24 := by
  opt87_reach [6608, 6575, 6576, 6611, 6578, 6579, 6580, 6581] 
  fx_close

theorem fx_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : wp ≤ 28671) :
    Reach (gst s ret tail sh lm nm 14984 flim rp wp fp M)
      (gst s ret tail sh lm nm 14467 flim rp wp (32 + fp) M) 46 := by
  opt87_reach [6616, 6617, 6618, 6619, 6620, 6582, 6585, 6593, 6594, 6595, 6596, 6597] 
  fx_close

theorem fx_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfp : fp < 65536) (hw : 28671 < wp) (hwp : wp < 65536) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 14984 flim rp wp fp M)
      (callState s ret (wd 1 :: tail) M) 64 := by
  opt87_reach [6616, 6617, 6618, 6619, 6620, 6582, 6585, 6593, 6594, 6595, 6789, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800] with [hj]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm rp wp fp : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm 14918 32576 rp wp fp M)
      (callState s ret (wd 0 :: tail) M) 51 := by
  opt87_reach [6598, 6629, 6753, 6754, 6755, 6756, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6810, 6811, 6812] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm 14918 flim rp wp fp M)
      (gst s ret tail sh lm nm 15152 flim rp wp fp M) 42 := by
  opt87_reach [6598, 6629, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760] with [h6]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (gst s ret tail sh lm nm 15152 flim rp wp fp M)
      (gst s ret tail sh lm nm 14467 32576 rp wp fp M) 17 := by
  opt87_reach [6782, 6784, 6785, 6787, 6788] 
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) (hfl : flim ≠ 32576) (hfl' : flim < 65536) (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm 14918 flim rp wp fp M)
      (callState s 15120 (wd 90880 :: wd 0 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt87_reach [6598, 6629, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766] with [h6]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 15121 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 22277 (wd 15128 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 14 := by
  opt87_reach [6768, 6769, 6770] 
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 15128 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 10997 (wd 32352 :: wd 29440 :: wd 15142 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt87_reach [6771, 6772, 6773, 6774, 6775, 6776] 
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm flim rp wp fp : Nat) :
    Reach (callState s 15142 (wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M)
      (callState s 15151 (wd 0 :: wd 90880 :: wd 800 :: wd flim :: wd rp :: wd wp :: wd fp :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt87_reach [6777, 6778, 6779, 6780] 
  fx_close

end MlDsaOpt87.Proofs.Fix
