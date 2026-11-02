import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/Mub0Blocks.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `mub0`: straight-line blocks between the calls

`b0`–`b7` absorb the eight `TRL` lanes (one `spr` call each), `b8` calls
`trabs`, `b9` builds the two signature bytes, `b10` absorbs them into lane 8
and branches on `len = |M| + 66`, `b11` adds the padding.
-/

namespace MlDsaOptGlam44.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

set_option hygiene false in
/-- Context facts for the `mub0` blocks. -/
macro "mub_pre" : tactic => `(tactic| (
  have := hr.depth; simp only [Stack.mub0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits))

set_option maxRecDepth 100000 in
theorem mub0_b0 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 19730 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64768) :: wd 19743 :: wd sh :: wd rs :: wd rl :: tail) M) 24 := by
  mub_pre
  glam44_rreach [8258, 8259, 8260, 8261, 8262, 8263, 8264]

set_option maxRecDepth 100000 in
theorem mub0_b1 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19743 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64800) :: wd 19763 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  mub_pre
  glam44_rreach [8265, 8266, 8267, 8268, 8269, 8270, 8271, 8272, 8273, 8274, 8275, 8276, 8277, 8278] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b2 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19763 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64832) :: wd 19785 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  mub_pre
  glam44_rreach [8279, 8280, 8281, 8282, 8283, 8284, 8285, 8286, 8287, 8288, 8289, 8290, 8291, 8292] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b3 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19785 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64864) :: wd 19807 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  mub_pre
  glam44_rreach [8293, 8294, 8295, 8296, 8297, 8298, 8299, 8300, 8301, 8302, 8303, 8304, 8305, 8306] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b4 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19807 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64896) :: wd 19829 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  mub_pre
  glam44_rreach [8307, 8308, 8309, 8310, 8311, 8312, 8313, 8314, 8315, 8316, 8317, 8318, 8319, 8320] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b5 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19829 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64928) :: wd 19851 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  mub_pre
  glam44_rreach [8321, 8322, 8323, 8324, 8325, 8326, 8327, 8328, 8329, 8330, 8331, 8332, 8333, 8334] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b6 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19851 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64960) :: wd 19873 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  mub_pre
  glam44_rreach [8335, 8336, 8337, 8338, 8339, 8340, 8341, 8342, 8343, 8344, 8345, 8346, 8347, 8348] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b7 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19873 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (word M 64992) :: wd 19895 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  mub_pre
  glam44_rreach [8349, 8350, 8351, 8352, 8353, 8354, 8355, 8356, 8357, 8358, 8359, 8360, 8361, 8362] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b8 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19895 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 18792 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 3730 :: wd 19954 ::
        wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  mub_pre
  glam44_rreach [8363, 8364, 8365, 8366, 8367, 8368, 8369, 8370, 8371, 8372, 8373, 8374, 8375, 8376, 8377, 8378] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b9 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 19954 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (65280 &&& word s.executionEnv.calldata 3730 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 3730 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 19980 :: wd sh :: wd rs :: wd rl :: tail) M) 51 := by
  mub_pre
  glam44_rreach [8379, 8380, 8381, 8382, 8383, 8384, 8385, 8386, 8387, 8388, 8389, 8390, 8391, 8392, 8393, 8394]

set_option maxRecDepth 100000 in
theorem mub0_b10l {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : 135 < s.executionEnv.calldata.size - 3666) :
    Reach (callState s 19980 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rl tail
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 67 := by
  mub_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [8395, 8396, 8397, 8398, 8399, 8400, 8401, 8402, 8403, 8404, 8405, 8406, 8407, 8408, 8409, 8410, 8450, 8451, 8452, 8453, 8454] with [word_mstore_disjoint, hj]

set_option maxRecDepth 100000 in
theorem mub0_b10s {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 3666 ≤ 135) :
    Reach (callState s 19980 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19515 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 3666) * 8)) :: wd 20024 ::
        wd (s.executionEnv.calldata.size - 3666) :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 93 := by
  mub_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 3666) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 3666) ≤ 7 := Nat.and_le_left
    omega
  glam44_rreach [8395, 8396, 8397, 8398, 8399, 8400, 8401, 8402, 8403, 8404, 8405, 8406, 8407, 8408, 8409, 8410, 8411, 8412, 8413, 8414, 8415, 8416, 8417, 8418, 8419, 8420, 8421, 8422] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b11 {s : State} (hs : Ctx s) {rl rs : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (hrs : RetOK Stack.mub0 rs (wd rl :: tail)) (M : ByteArray)
    {r p sh : Nat} (hsh : sh < 4) (hp : p ≤ 135) :
    Reach (callState s 20024 (wd r :: wd p :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rs (wd rl :: tail)
        (MachineState.writeBytes
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
            ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32))
          (Data.Bytes.natToBytesPadded
            ((word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
                ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32)) 512 ^^^
              7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 82 := by
  mub_pre
  have hret := hrs.small
  have hj := hrs.jumpdest
  glam44_rreach [8423, 8424, 8425, 8426, 8427, 8428, 8429, 8430, 8431, 8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8441, 8442, 8443, 8444, 8445, 8446, 8447, 8448, 8449] with [word_mstore_disjoint, hj]

end MlDsaOptGlam44.Proofs.WP4
