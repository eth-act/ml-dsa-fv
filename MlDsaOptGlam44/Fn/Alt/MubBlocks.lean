import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported by hand from `MlDsaOpt65/Fn/Sponge/MubBlocks.lean` (44 constants: calldata offset 3666, HDR 3732, MU 0xfe00; glam pcs and indices). -/
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `mub` (glam ML-DSA-44): straight-line blocks between the calls

Stack at entry `[K = 136 k, sh, ret]`; `P = |cd| − 0x0e52 = 66 + |M|`.

* `K ≤ P`, `K = 680`: nothing (`mub_z`);
* `K ≤ P`, `K ≠ 680`: `trabs [0, LM, 5, sh, K + 0x0e52]` (`mub_t`), then either
  `P ≥ K + 136` (full block, `mub_tf`) or the padding of the last block
  (`mub_tp`: `spr` of `0x1F << 8 (r % 8)`, `r = P − K`; `mub_tp2`: lane `r / 8`
  and the `0x80` of lane 16);
* `P < K ≤ P + 136`: `cext [8, sh, MU]` (`mub_cx`, `mub_cx2`);
* `P + 136 < K`: nothing (`mub_out`).
-/

namespace MlDsaOptGlam44.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

set_option hygiene false in
/-- Context facts for the `mub` blocks. -/
macro "mubkg_pre" : tactic => `(tactic| (
  have := hr.depth; simp only [Stack.mub, Stack.trabs, Stack.spr, Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits))

set_option maxRecDepth 100000 in
/-- `P < K ≤ P + 136`: call `cext [8, sh, MU]`. -/
theorem mub_cx {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 3732 ≤ s.executionEnv.calldata.size)
    (hlt : s.executionEnv.calldata.size - 3666 < K) (hle : K ≤ s.executionEnv.calldata.size - 3666 + 136) :
    Reach (callState s 20094 (wd K :: wd sh :: wd ret :: tail) M)
      (callState s 19241 (wd 8 :: wd sh :: wd 65024 :: wd 20131 :: wd (s.executionEnv.calldata.size - 3666) ::
        wd K :: wd sh :: wd ret :: tail) M) 85 := by
  mubkg_pre
  glam44_rreach [8455, 8456, 8457, 8458, 8459, 8460, 8461, 8462, 8463, 8464, 8465, 8466, 8467, 8468, 8469, 8470, 8471, 8472, 8473, 8474, 8475, 8476, 8477]

set_option maxRecDepth 100000 in
/-- After `cext`: return. -/
theorem mub_cx2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {p K sh : Nat} :
    Reach (callState s 20131 (wd p :: wd K :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 27 := by
  mubkg_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8478, 8479, 8480, 8546, 8547, 8548, 8549, 8550] with [hj]

set_option maxRecDepth 100000 in
/-- `P + 136 < K`: return. -/
theorem mub_out {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 3732 ≤ s.executionEnv.calldata.size)
    (hgt : s.executionEnv.calldata.size - 3666 + 136 < K) :
    Reach (callState s 20094 (wd K :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 77 := by
  mubkg_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8455, 8456, 8457, 8458, 8459, 8460, 8461, 8462, 8463, 8464, 8465, 8466, 8467, 8468, 8469, 8470, 8471, 8546, 8547, 8548, 8549, 8550] with [hj]

set_option maxRecDepth 100000 in
/-- `K = 680 ≤ P`: return. -/
theorem mub_z {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {sh : Nat}
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hle : 680 ≤ s.executionEnv.calldata.size - 3666) :
    Reach (callState s 20094 (wd 680 :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 72 := by
  mubkg_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8455, 8456, 8457, 8458, 8459, 8460, 8461, 8462, 8463, 8464, 8481, 8482, 8483, 8484, 8485, 8486, 8546, 8547, 8548, 8549, 8550] with [hj]

set_option maxRecDepth 100000 in
/-- `K ≤ P`, `K ≠ 680`: call `trabs [0, LM, 5, sh, K + 0x0e52]`. -/
theorem mub_t {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K < 680)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hle : K ≤ s.executionEnv.calldata.size - 3666) :
    Reach (callState s 20094 (wd K :: wd sh :: wd ret :: tail) M)
      (callState s 18792 (wd 0 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 ::
        wd 5 :: wd sh :: wd (3666 + K) :: wd 20195 :: wd (s.executionEnv.calldata.size - 3666) ::
        wd K :: wd sh :: wd ret :: tail) M) 91 := by
  mubkg_pre
  glam44_rreach [8455, 8456, 8457, 8458, 8459, 8460, 8461, 8462, 8463, 8464, 8481, 8482, 8483, 8484, 8485, 8486, 8487, 8488, 8489, 8490, 8491, 8492, 8493, 8494, 8495, 8496]

set_option maxRecDepth 100000 in
/-- After `trabs`, `K + 136 ≤ P` (a full block): return. -/
theorem mub_tf {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hle : K + 136 ≤ s.executionEnv.calldata.size - 3666) :
    Reach (callState s 20195 (wd (s.executionEnv.calldata.size - 3666) :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s ret tail M) 47 := by
  mubkg_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8497, 8498, 8499, 8500, 8501, 8502, 8503, 8504, 8505, 8546, 8547, 8548, 8549, 8550] with [hj]

set_option maxRecDepth 100000 in
/-- After `trabs`, `K ≤ P < K + 136` (the last block): call `spr` on the `0x1F` byte. -/
theorem mub_tp {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hle : K ≤ s.executionEnv.calldata.size - 3666)
    (hlt : s.executionEnv.calldata.size - 3666 < K + 136) :
    Reach (callState s 20195 (wd (s.executionEnv.calldata.size - 3666) :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s 19515 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 3666 - K) * 8)) :: wd 20229 ::
        wd (s.executionEnv.calldata.size - 3666 - K) :: wd (s.executionEnv.calldata.size - 3666) ::
        wd K :: wd sh :: wd ret :: tail) M) 82 := by
  mubkg_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 3666 - K) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 3666 - K) ≤ 7 := Nat.and_le_left
    omega
  glam44_rreach [8497, 8498, 8499, 8500, 8501, 8502, 8503, 8504, 8505, 8506, 8507, 8508, 8509, 8510, 8511, 8512, 8513, 8514, 8515, 8516, 8517, 8518, 8519, 8520]

set_option maxRecDepth 100000 in
/-- After `spr`: xor the padding into lane `q / 8` and the top bit into lane 16; return. -/
theorem mub_tp2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {r q p K sh : Nat} (hsh : sh < 4) (hq : q ≤ 135) :
    Reach (callState s 20229 (wd r :: wd q :: wd p :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
            ((r * 2 ^ sh ^^^ word M (0 + q / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + q / 8 * 32))
          (Data.Bytes.natToBytesPadded
            ((word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
                ((r * 2 ^ sh ^^^ word M (0 + q / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + q / 8 * 32)) 512 ^^^
              7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 87 := by
  mubkg_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8521, 8522, 8523, 8524, 8525, 8526, 8527, 8528, 8529, 8530, 8531, 8532, 8533, 8534, 8535, 8536, 8537, 8538, 8539, 8540, 8541, 8542, 8543, 8544, 8545, 8546, 8547, 8548, 8549, 8550] with [word_mstore_disjoint, hj]

end MlDsaOptGlam44.Proofs.WP4
