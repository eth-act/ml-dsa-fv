import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`G`/`cst`/`(pc := _)`/`(ret := _)`/`(rT := _)`/`(rF := _)` and the `reach_mcopy` index relocated by hand (`proofgen_port.maps 87`)
set_option warningAsError true
/-!
# `fix`: straight-line blocks (v4)

Entry at pc 14669 (`[sh, ret]`); first-flag scan head `fxf1` at pc 14701
(`sst`: stack `rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`);
group-loop head `fxg` at pc 14727 (`gst`: stack
`wp :: rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`). The flag
word of the group at `rp` is read at `rp / 8 + 28672` (`FL − ABUF / 8`).
-/

namespace MlDsaOpt87.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

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
  callState s 14701 (wd rp :: wd 29440 :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

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
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (m : ByteArray) (sh : Nat) (hsh : sh ≤ 192) :
    Reach (callState s 14669 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh)
        (8380417 * 2 ^ sh) (8388608 * 2 ^ sh) 20480 m) 40 := by
  have hlm := lm_lt sh hsh
  have hqs := qs_lt sh hsh
  have hfm := fm_lt sh hsh
  opt87_reach [6409, 6410, 6411, 6412, 6413, 6414, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422]
    with [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlm, Nat.mod_eq_of_lt hqs, Nat.mod_eq_of_lt hfm]
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (sst s ret tail sh lm nm qs fm (256 + rp) M) 55 := by
  opt87_reach [6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431, 6432, 6433, 6434, 6435, 6436, 6437]
    with [land_word_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (gst s ret tail sh lm nm qs fm 14727 29440 rp rp M) 42 := by
  opt87_reach [6423, 6424, 6425, 6426, 6427, 6428, 6429, 6430, 6431, 6432, 6433, 6438, 6439]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 14727 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14918 rlim rp wp M) 38 := by
  opt87_reach [6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (gst s ret tail sh lm nm qs fm 14727 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14743 rlim rp wp M) 38 := by
  opt87_reach [6440, 6441, 6442, 6443, 6444, 6445, 6446, 6447, 6448, 6449, 6450]
    with [land_word_mod, hf]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14743 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14755 rlim rp wp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 36 := by
  opt87_reach [6451, 6452, 6453, 6454, 6455, 6456, 6457, 6458, 6459, 6460, 6461, 6462] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14755 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14773 rlim rp wp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 48 := by
  opt87_reach [6463, 6464, 6465, 6466, 6467, 6468, 6469, 6470, 6471, 6472, 6473, 6474, 6475, 6476, 6477, 6478] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14773 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14791 rlim rp wp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 48 := by
  opt87_reach [6479, 6480, 6481, 6482, 6483, 6484, 6485, 6486, 6487, 6488, 6489, 6490, 6491, 6492, 6493, 6494] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14791 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14809 rlim rp wp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 48 := by
  opt87_reach [6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502, 6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14809 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14827 rlim rp wp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 48 := by
  opt87_reach [6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6520, 6521, 6522, 6523, 6524, 6525, 6526] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14827 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14845 rlim rp wp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 48 := by
  opt87_reach [6527, 6528, 6529, 6530, 6531, 6532, 6533, 6534, 6535, 6536, 6537, 6538, 6539, 6540, 6541, 6542] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14845 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14863 rlim rp wp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 48 := by
  opt87_reach [6543, 6544, 6545, 6546, 6547, 6548, 6549, 6550, 6551, 6552, 6553, 6554, 6555, 6556, 6557, 6558] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14863 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14881 rlim rp wp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 48 := by
  opt87_reach [6559, 6560, 6561, 6562, 6563, 6564, 6565, 6566, 6567, 6568, 6569, 6570, 6571, 6572, 6573, 6574] with [cw, Nat.zero_add]
  fx_close

theorem fx_cand0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14918 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14937 rlim rp (wp + acc qs (lm &&& word M (32 * 0 + rp)) * 32)
        (cw M wp (32 * 0 + rp) lm nm)) 52 := by
  opt87_reach [6598, 6599, 6600, 6601, 6602, 6603, 6604, 6605, 6606, 6607, 6608, 6609, 6610, 6611, 6612, 6613, 6614, 6615] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14937 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14958 rlim rp (wp + acc qs (lm &&& word M (32 * 1 + rp)) * 32)
        (cw M wp (32 * 1 + rp) lm nm)) 57 := by
  opt87_reach [6616, 6617, 6618, 6619, 6620, 6621, 6622, 6623, 6624, 6625, 6626, 6627, 6628, 6629, 6630, 6631, 6632, 6633, 6634] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14958 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14979 rlim rp (wp + acc qs (lm &&& word M (32 * 2 + rp)) * 32)
        (cw M wp (32 * 2 + rp) lm nm)) 57 := by
  opt87_reach [6635, 6636, 6637, 6638, 6639, 6640, 6641, 6642, 6643, 6644, 6645, 6646, 6647, 6648, 6649, 6650, 6651, 6652, 6653] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14979 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15000 rlim rp (wp + acc qs (lm &&& word M (32 * 3 + rp)) * 32)
        (cw M wp (32 * 3 + rp) lm nm)) 57 := by
  opt87_reach [6654, 6655, 6656, 6657, 6658, 6659, 6660, 6661, 6662, 6663, 6664, 6665, 6666, 6667, 6668, 6669, 6670, 6671, 6672] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 15000 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15021 rlim rp (wp + acc qs (lm &&& word M (32 * 4 + rp)) * 32)
        (cw M wp (32 * 4 + rp) lm nm)) 57 := by
  opt87_reach [6673, 6674, 6675, 6676, 6677, 6678, 6679, 6680, 6681, 6682, 6683, 6684, 6685, 6686, 6687, 6688, 6689, 6690, 6691] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 15021 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15042 rlim rp (wp + acc qs (lm &&& word M (32 * 5 + rp)) * 32)
        (cw M wp (32 * 5 + rp) lm nm)) 57 := by
  opt87_reach [6692, 6693, 6694, 6695, 6696, 6697, 6698, 6699, 6700, 6701, 6702, 6703, 6704, 6705, 6706, 6707, 6708, 6709, 6710] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 15042 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15063 rlim rp (wp + acc qs (lm &&& word M (32 * 6 + rp)) * 32)
        (cw M wp (32 * 6 + rp) lm nm)) 57 := by
  opt87_reach [6711, 6712, 6713, 6714, 6715, 6716, 6717, 6718, 6719, 6720, 6721, 6722, 6723, 6724, 6725, 6726, 6727, 6728, 6729] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 15063 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15084 rlim rp (wp + acc qs (lm &&& word M (32 * 7 + rp)) * 32)
        (cw M wp (32 * 7 + rp) lm nm)) 57 := by
  opt87_reach [6730, 6731, 6732, 6733, 6734, 6735, 6736, 6737, 6738, 6739, 6740, 6741, 6742, 6743, 6744, 6745, 6746, 6747, 6748] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 14881 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14885 rlim rp (256 + wp) M) 6 := by
  opt87_reach [6575, 6576]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 15084 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14885 rlim rp wp M) 11 := by
  opt87_reach [6749, 6750]
  fx_close

theorem fx_gn_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : 256 + rp < rlim) :
    Reach (gst s ret tail sh lm nm qs fm 14885 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14727 rlim (256 + rp) wp M) 47 := by
  opt87_reach [6577, 6578, 6579, 6580, 6581, 6582, 6583, 6584, 6585, 6586, 6587, 6588, 6589, 6590]
  fx_close

theorem fx_gn_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : rlim ≤ 256 + rp) :
    Reach (gst s ret tail sh lm nm qs fm 14885 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15088 rlim (256 + rp) wp M) 80 := by
  opt87_reach [6577, 6578, 6579, 6580, 6581, 6582, 6583, 6584, 6585, 6586, 6587, 6588, 6589, 6590, 6591, 6592, 6593, 6594, 6595, 6596, 6597]
  fx_close

theorem fx_gn_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : 28672 ≤ wp) (hwp' : wp < 65536)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 14885 rlim rp wp M)
      (callState s ret (wd 1 :: tail) M) 100 := by
  opt87_reach [6577, 6578, 6579, 6580, 6581, 6582, 6583, 6584, 6585, 6586, 6587, 6588, 6589, 6590, 6591, 6592, 6593, 6594, 6595, 6789, 6790, 6791, 6792, 6793, 6794, 6795, 6796, 6797, 6798, 6799, 6800] with [hj, Nat.and_zero, Nat.zero_and]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp wp : Nat)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 15088 31232 rp wp M)
      (callState s ret (wd 0 :: tail) M) 53 := by
  opt87_reach [6751, 6752, 6753, 6754, 6755, 6756, 6801, 6802, 6803, 6804, 6805, 6806, 6807, 6808, 6809, 6810, 6811, 6812] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 15088 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 15152 rlim rp wp M) 42 := by
  opt87_reach [6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 15152 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 14727 31232 rp wp M) 23 := by
  opt87_reach [6782, 6783, 6784, 6785, 6786, 6787, 6788]
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm qs fm 15088 rlim rp wp M)
      (callState s 15120 (wd 90880 :: wd 0 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  opt87_reach [6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6760, 6761, 6762, 6763, 6764, 6765, 6766]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 15121 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 22277 (wd 15128 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm ::
        wd sh :: wd ret :: tail) M) 14 := by
  opt87_reach [6768, 6769, 6770]
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 15128 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 10992 (wd 32352 :: wd 29440 :: wd 15142 :: wd wp :: wd rp :: wd rlim :: wd fm ::
        wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  opt87_reach [6771, 6772, 6773, 6774, 6775, 6776]
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 15142 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 15151 (wd 0 :: wd 90880 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  opt87_reach [6777, 6778, 6779, 6780]
  fx_close

end MlDsaOpt87.Proofs.Fix
