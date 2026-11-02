import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Fix/Blocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`G`/`cst`/`(pc := _)`/`(ret := _)`/`(rT := _)`/`(rF := _)` and the `reach_mcopy` index relocated by hand (`proofgen_port.maps 87`)
set_option warningAsError true
/-!
# `fix`: straight-line blocks (v4)

Entry at pc 19863 (`[sh, ret]`); first-flag scan head `fxf1` at pc 19895
(`sst`: stack `rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`);
group-loop head `fxg` at pc 19921 (`gst`: stack
`wp :: rp :: rlim :: fm :: qs :: nm :: lm :: sh :: ret :: tail`). The flag
word of the group at `rp` is read at `rp / 8 + 28672` (`FL − ABUF / 8`).
-/

namespace MlDsaOptGlam87.Proofs.Fix

open MlDsaOpt87.Proofs

-- port: the 44 `Fix` namespace is not imported here
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

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
  callState s 19895 (wd rp :: wd 29440 :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M

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
    Reach (callState s 19863 (wd sh :: wd ret :: tail) m)
      (sst s ret tail sh (18446744073709551615 * 2 ^ sh) (2 ^ 256 - 1 - 18446744073709551615 * 2 ^ sh)
        (8380417 * 2 ^ sh) (8388608 * 2 ^ sh) 20480 m) 40 := by
  have hlm := lm_lt sh hsh
  have hqs := qs_lt sh hsh
  have hfm := fm_lt sh hsh
  glam87_rreach [8413, 8414, 8415, 8416, 8417, 8418, 8419, 8420, 8421, 8422, 8423, 8424, 8425, 8426]
    with [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlm, Nat.mod_eq_of_lt hqs, Nat.mod_eq_of_lt hfm]
  fx_close

theorem fx_scan_next {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (sst s ret tail sh lm nm qs fm (256 + rp) M) 55 := by
  glam87_rreach [8427, 8428, 8429, 8430, 8431, 8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8441]
    with [land_word_mod, hf]
  fx_close

theorem fx_scan_hit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (sst s ret tail sh lm nm qs fm rp M)
      (gst s ret tail sh lm nm qs fm 19921 29440 rp rp M) 42 := by
  glam87_rreach [8427, 8428, 8429, 8430, 8431, 8432, 8433, 8434, 8435, 8436, 8437, 8442, 8443]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_flag {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 19921 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20112 rlim rp wp M) 38 := by
  glam87_rreach [8444, 8445, 8446, 8447, 8448, 8449, 8450, 8451, 8452, 8453, 8454]
    with [land_word_mod, hf]
  fx_close

theorem fx_gl_clean {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536)
    (hf : fm &&& word M (28672 + rp / 8) = 0) :
    Reach (gst s ret tail sh lm nm qs fm 19921 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19937 rlim rp wp M) 38 := by
  glam87_rreach [8444, 8445, 8446, 8447, 8448, 8449, 8450, 8451, 8452, 8453, 8454]
    with [land_word_mod, hf]
  fx_close

theorem fx_copy0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 19937 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19949 rlim rp wp (cw M (32 * 0 + wp) (32 * 0 + rp) lm nm)) 36 := by
  glam87_rreach [8455, 8456, 8457, 8458, 8459, 8460, 8461, 8462, 8463, 8464, 8465, 8466] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 19949 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19967 rlim rp wp (cw M (32 * 1 + wp) (32 * 1 + rp) lm nm)) 48 := by
  glam87_rreach [8467, 8468, 8469, 8470, 8471, 8472, 8473, 8474, 8475, 8476, 8477, 8478, 8479, 8480, 8481, 8482] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 19967 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19985 rlim rp wp (cw M (32 * 2 + wp) (32 * 2 + rp) lm nm)) 48 := by
  glam87_rreach [8483, 8484, 8485, 8486, 8487, 8488, 8489, 8490, 8491, 8492, 8493, 8494, 8495, 8496, 8497, 8498] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 19985 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20003 rlim rp wp (cw M (32 * 3 + wp) (32 * 3 + rp) lm nm)) 48 := by
  glam87_rreach [8499, 8500, 8501, 8502, 8503, 8504, 8505, 8506, 8507, 8508, 8509, 8510, 8511, 8512, 8513, 8514] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20003 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20021 rlim rp wp (cw M (32 * 4 + wp) (32 * 4 + rp) lm nm)) 48 := by
  glam87_rreach [8515, 8516, 8517, 8518, 8519, 8520, 8521, 8522, 8523, 8524, 8525, 8526, 8527, 8528, 8529, 8530] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20021 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20039 rlim rp wp (cw M (32 * 5 + wp) (32 * 5 + rp) lm nm)) 48 := by
  glam87_rreach [8531, 8532, 8533, 8534, 8535, 8536, 8537, 8538, 8539, 8540, 8541, 8542, 8543, 8544, 8545, 8546] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20039 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20057 rlim rp wp (cw M (32 * 6 + wp) (32 * 6 + rp) lm nm)) 48 := by
  glam87_rreach [8547, 8548, 8549, 8550, 8551, 8552, 8553, 8554, 8555, 8556, 8557, 8558, 8559, 8560, 8561, 8562] with [cw, Nat.zero_add]
  fx_close

theorem fx_copy7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp + 256 ≤ 91680) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20057 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20075 rlim rp wp (cw M (32 * 7 + wp) (32 * 7 + rp) lm nm)) 48 := by
  glam87_rreach [8563, 8564, 8565, 8566, 8567, 8568, 8569, 8570, 8571, 8572, 8573, 8574, 8575, 8576, 8577, 8578] with [cw, Nat.zero_add]
  fx_close

theorem fx_cand0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20112 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20131 rlim rp (wp + acc qs (lm &&& word M (32 * 0 + rp)) * 32)
        (cw M wp (32 * 0 + rp) lm nm)) 52 := by
  glam87_rreach [8602, 8603, 8604, 8605, 8606, 8607, 8608, 8609, 8610, 8611, 8612, 8613, 8614, 8615, 8616, 8617, 8618, 8619] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20131 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20152 rlim rp (wp + acc qs (lm &&& word M (32 * 1 + rp)) * 32)
        (cw M wp (32 * 1 + rp) lm nm)) 57 := by
  glam87_rreach [8620, 8621, 8622, 8623, 8624, 8625, 8626, 8627, 8628, 8629, 8630, 8631, 8632, 8633, 8634, 8635, 8636, 8637, 8638] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20152 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20173 rlim rp (wp + acc qs (lm &&& word M (32 * 2 + rp)) * 32)
        (cw M wp (32 * 2 + rp) lm nm)) 57 := by
  glam87_rreach [8639, 8640, 8641, 8642, 8643, 8644, 8645, 8646, 8647, 8648, 8649, 8650, 8651, 8652, 8653, 8654, 8655, 8656, 8657] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20173 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20194 rlim rp (wp + acc qs (lm &&& word M (32 * 3 + rp)) * 32)
        (cw M wp (32 * 3 + rp) lm nm)) 57 := by
  glam87_rreach [8658, 8659, 8660, 8661, 8662, 8663, 8664, 8665, 8666, 8667, 8668, 8669, 8670, 8671, 8672, 8673, 8674, 8675, 8676] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20194 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20215 rlim rp (wp + acc qs (lm &&& word M (32 * 4 + rp)) * 32)
        (cw M wp (32 * 4 + rp) lm nm)) 57 := by
  glam87_rreach [8677, 8678, 8679, 8680, 8681, 8682, 8683, 8684, 8685, 8686, 8687, 8688, 8689, 8690, 8691, 8692, 8693, 8694, 8695] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20215 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20236 rlim rp (wp + acc qs (lm &&& word M (32 * 5 + rp)) * 32)
        (cw M wp (32 * 5 + rp) lm nm)) 57 := by
  glam87_rreach [8696, 8697, 8698, 8699, 8700, 8701, 8702, 8703, 8704, 8705, 8706, 8707, 8708, 8709, 8710, 8711, 8712, 8713, 8714] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20236 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20257 rlim rp (wp + acc qs (lm &&& word M (32 * 6 + rp)) * 32)
        (cw M wp (32 * 6 + rp) lm nm)) 57 := by
  glam87_rreach [8715, 8716, 8717, 8718, 8719, 8720, 8721, 8722, 8723, 8724, 8725, 8726, 8727, 8728, 8729, 8730, 8731, 8732, 8733] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_cand7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hqs : qs < 2 ^ 256) (hrp : rp + 256 ≤ 91680) (hwp : wp + 32 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20257 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20278 rlim rp (wp + acc qs (lm &&& word M (32 * 7 + rp)) * 32)
        (cw M wp (32 * 7 + rp) lm nm)) 57 := by
  glam87_rreach [8734, 8735, 8736, 8737, 8738, 8739, 8740, 8741, 8742, 8743, 8744, 8745, 8746, 8747, 8748, 8749, 8750, 8751, 8752] with [cw, acc, land_word_mod, Nat.zero_add]
  fx_close

theorem fx_ctail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hwp : wp + 256 ≤ 91680) :
    Reach (gst s ret tail sh lm nm qs fm 20075 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20079 rlim rp (256 + wp) M) 6 := by
  glam87_rreach [8579, 8580]
  fx_close

theorem fx_ftail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 20278 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20079 rlim rp wp M) 11 := by
  glam87_rreach [8753, 8754]
  fx_close

theorem fx_gn_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : 256 + rp < rlim) :
    Reach (gst s ret tail sh lm nm qs fm 20079 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19921 rlim (256 + rp) wp M) 47 := by
  glam87_rreach [8581, 8582, 8583, 8584, 8585, 8586, 8587, 8588, 8589, 8590, 8591, 8592, 8593, 8594]
  fx_close

theorem fx_gn_ext {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : wp < 28672) (hr : rlim ≤ 256 + rp) :
    Reach (gst s ret tail sh lm nm qs fm 20079 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20282 rlim (256 + rp) wp M) 80 := by
  glam87_rreach [8581, 8582, 8583, 8584, 8585, 8586, 8587, 8588, 8589, 8590, 8591, 8592, 8593, 8594, 8595, 8596, 8597, 8598, 8599, 8600, 8601]
  fx_close

theorem fx_gn_done {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hrp : rp < 65536) (hrl : rlim < 65536)
    (hwp : 28672 ≤ wp) (hwp' : wp < 65536)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 20079 rlim rp wp M)
      (callState s ret (wd 1 :: tail) M) 100 := by
  glam87_rreach [8581, 8582, 8583, 8584, 8585, 8586, 8587, 8588, 8589, 8590, 8591, 8592, 8593, 8594, 8595, 8596, 8597, 8598, 8599, 8793, 8794, 8795, 8796, 8797, 8798, 8799, 8800, 8801, 8802, 8803, 8804] with [hj, Nat.and_zero, Nat.zero_and]
  fx_close

theorem fx_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rp wp : Nat)
    (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (gst s ret tail sh lm nm qs fm 20282 31232 rp wp M)
      (callState s ret (wd 0 :: tail) M) 53 := by
  glam87_rreach [8755, 8756, 8757, 8758, 8759, 8760, 8805, 8806, 8807, 8808, 8809, 8810, 8811, 8812, 8813, 8814, 8815, 8816] with [hj]
  fx_close

theorem fx_ext_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 ≠ 0) :
    Reach (gst s ret tail sh lm nm qs fm 20282 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 20346 rlim rp wp M) 42 := by
  glam87_rreach [8755, 8756, 8757, 8758, 8759, 8760, 8761, 8762, 8763, 8764]
  fx_close

theorem fx_cont {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (gst s ret tail sh lm nm qs fm 20346 rlim rp wp M)
      (gst s ret tail sh lm nm qs fm 19921 31232 rp wp M) 23 := by
  glam87_rreach [8786, 8787, 8788, 8789, 8790, 8791, 8792]
  fx_close

theorem fx_sq_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) (hfl : rlim ≠ 31232) (hfl' : rlim < 65536)
    (h6 : word M 4064 = 0) :
    Reach (gst s ret tail sh lm nm qs fm 20282 rlim rp wp M)
      (callState s 20314 (wd 90880 :: wd 0 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064)) 59 := by
  glam87_rreach [8755, 8756, 8757, 8758, 8759, 8760, 8761, 8762, 8763, 8764, 8765, 8766, 8767, 8768, 8769, 8770]
  fx_close

theorem fx_sq_kf4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 20315 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 41770 (wd 20322 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm ::
        wd sh :: wd ret :: tail) M) 14 := by
  glam87_rreach [8772, 8773, 8774]
  fx_close

theorem fx_sq_blk {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 20322 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 10846 (wd 32352 :: wd 29440 :: wd 20336 :: wd wp :: wd rp :: wd rlim :: wd fm ::
        wd qs :: wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 21 := by
  glam87_rreach [8775, 8776, 8777, 8778, 8779, 8780]
  fx_close

theorem fx_sq_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (sh lm nm qs fm rlim rp wp : Nat) :
    Reach (callState s 20336 (wd wp :: wd rp :: wd rlim :: wd fm :: wd qs :: wd nm :: wd lm :: wd sh ::
        wd ret :: tail) M)
      (callState s 20345 (wd 0 :: wd 90880 :: wd 800 :: wd wp :: wd rp :: wd rlim :: wd fm :: wd qs ::
        wd nm :: wd lm :: wd sh :: wd ret :: tail) M) 9 := by
  glam87_rreach [8781, 8782, 8783, 8784]
  fx_close

end MlDsaOptGlam87.Proofs.Fix
