import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `mub` (ML-DSA-65): straight-line blocks between the calls

Stack at entry `[K = 136 k, sh, ret]`; `P = |cd| − 0x144b = 66 + |M|`.

* `K ≤ P`, `K = 680`: nothing (`mub_z`);
* `K ≤ P`, `K ≠ 680`: `trabs [0, LM, 5, sh, K + 0x144b]` (`mub_t`), then either
  `P ≥ K + 136` (full block, `mub_tf`) or the padding of the last block
  (`mub_tp`: `spr` of `0x1F << 8 (r % 8)`, `r = P − K`; `mub_tp2`: lane `r / 8`
  and the `0x80` of lane 16);
* `P < K ≤ P + 136`: `cext [8, sh, MU]` (`mub_cx`, `mub_cx2`);
* `P + 136 < K`: nothing (`mub_out`).
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

set_option hygiene false in
/-- Context facts for the `mub` blocks. -/
macro "mubk65_pre" : tactic => `(tactic| (
  have := hr.depth; simp only [Stack.mub, Stack.trabs, Stack.spr, Stack.cext, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits))

set_option maxRecDepth 100000 in
/-- `P < K ≤ P + 136`: call `cext [8, sh, MU]`. -/
theorem mub_cx {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 5261 ≤ s.executionEnv.calldata.size)
    (hlt : s.executionEnv.calldata.size - 5195 < K) (hle : K ≤ s.executionEnv.calldata.size - 5195 + 136) :
    Reach (callState s 13737 (wd K :: wd sh :: wd ret :: tail) M)
      (callState s 12876 (wd 8 :: wd sh :: wd 89600 :: wd 13775 :: wd (s.executionEnv.calldata.size - 5195) ::
        wd K :: wd sh :: wd ret :: tail) M) 85 := by
  mubk65_pre
  opt65_reach [6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029, 6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037]

set_option maxRecDepth 100000 in
/-- After `cext`: return. -/
theorem mub_cx2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {p K sh : Nat} :
    Reach (callState s 13775 (wd p :: wd K :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 27 := by
  mubk65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [6038, 6039, 6040, 6106, 6107, 6108, 6109, 6110] with [hj]

set_option maxRecDepth 100000 in
/-- `P + 136 < K`: return. -/
theorem mub_out {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 5261 ≤ s.executionEnv.calldata.size)
    (hgt : s.executionEnv.calldata.size - 5195 + 136 < K) :
    Reach (callState s 13737 (wd K :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 77 := by
  mubk65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029, 6030, 6031, 6106, 6107, 6108, 6109, 6110] with [hj]

set_option maxRecDepth 100000 in
/-- `K = 680 ≤ P`: return. -/
theorem mub_z {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {sh : Nat}
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hle : 680 ≤ s.executionEnv.calldata.size - 5195) :
    Reach (callState s 13737 (wd 680 :: wd sh :: wd ret :: tail) M) (callState s ret tail M) 72 := by
  mubk65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6041, 6042, 6043, 6044, 6045, 6046, 6106, 6107, 6108, 6109, 6110] with [hj]

set_option maxRecDepth 100000 in
/-- `K ≤ P`, `K ≠ 680`: call `trabs [0, LM, 5, sh, K + 0x144b]`. -/
theorem mub_t {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K < 680)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hle : K ≤ s.executionEnv.calldata.size - 5195) :
    Reach (callState s 13737 (wd K :: wd sh :: wd ret :: tail) M)
      (callState s 12427 (wd 0 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 ::
        wd 5 :: wd sh :: wd (5195 + K) :: wd 13839 :: wd (s.executionEnv.calldata.size - 5195) ::
        wd K :: wd sh :: wd ret :: tail) M) 91 := by
  mubk65_pre
  opt65_reach [6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6041, 6042, 6043, 6044, 6045, 6046, 6047, 6048, 6049, 6050, 6051, 6052, 6053, 6054, 6055, 6056]

set_option maxRecDepth 100000 in
/-- After `trabs`, `K + 136 ≤ P` (a full block): return. -/
theorem mub_tf {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hle : K + 136 ≤ s.executionEnv.calldata.size - 5195) :
    Reach (callState s 13839 (wd (s.executionEnv.calldata.size - 5195) :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s ret tail M) 47 := by
  mubk65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [6057, 6058, 6059, 6060, 6061, 6062, 6063, 6064, 6065, 6106, 6107, 6108, 6109, 6110] with [hj]

set_option maxRecDepth 100000 in
/-- After `trabs`, `K ≤ P < K + 136` (the last block): call `spr` on the `0x1F` byte. -/
theorem mub_tp {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {K sh : Nat} (hK : K ≤ 680)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hle : K ≤ s.executionEnv.calldata.size - 5195)
    (hlt : s.executionEnv.calldata.size - 5195 < K + 136) :
    Reach (callState s 13839 (wd (s.executionEnv.calldata.size - 5195) :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s 13150 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 5195 - K) * 8)) :: wd 13873 ::
        wd (s.executionEnv.calldata.size - 5195 - K) :: wd (s.executionEnv.calldata.size - 5195) ::
        wd K :: wd sh :: wd ret :: tail) M) 82 := by
  mubk65_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 5195 - K) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 5195 - K) ≤ 7 := Nat.and_le_left
    omega
  opt65_reach [6057, 6058, 6059, 6060, 6061, 6062, 6063, 6064, 6065, 6066, 6067, 6068, 6069, 6070, 6071, 6072, 6073, 6074, 6075, 6076, 6077, 6078, 6079, 6080]

set_option maxRecDepth 100000 in
/-- After `spr`: xor the padding into lane `q / 8` and the top bit into lane 16; return. -/
theorem mub_tp2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub ret tail) (M : ByteArray) {r q p K sh : Nat} (hsh : sh < 4) (hq : q ≤ 135) :
    Reach (callState s 13873 (wd r :: wd q :: wd p :: wd K :: wd sh :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
            ((r * 2 ^ sh ^^^ word M (0 + q / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + q / 8 * 32))
          (Data.Bytes.natToBytesPadded
            ((word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
                ((r * 2 ^ sh ^^^ word M (0 + q / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + q / 8 * 32)) 512 ^^^
              7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 87 := by
  mubk65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [6081, 6082, 6083, 6084, 6085, 6086, 6087, 6088, 6089, 6090, 6091, 6092, 6093, 6094, 6095, 6096, 6097, 6098, 6099, 6100, 6101, 6102, 6103, 6104, 6105, 6106, 6107, 6108, 6109, 6110] with [word_mstore_disjoint, hj]

end MlDsaOpt65.Proofs.WP4
