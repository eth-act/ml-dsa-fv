import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Sponge/Mub0Blocks.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Sponge/Mub0Blocks.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568; hand adjustments are marked `-- port:`. -/
-- port: tactic macro renamed `mub_pre` → `mub65_pre` (no clash with the 44 macro); return pcs relocated by the script (`wd N`)
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `mub0`: straight-line blocks between the calls

`b0`–`b7` absorb the eight `TRL` lanes (one `spr` call each), `b8` calls
`trabs`, `b9` builds the two signature bytes, `b10` absorbs them into lane 8
and branches on `len = |M| + 66`, `b11` adds the padding.
-/

namespace MlDsaOptGlam65.Proofs.WP4

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs.WP4
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

set_option hygiene false in
/-- Context facts for the `mub0` blocks. -/
macro "mub65_pre" : tactic => `(tactic| (
  have := hr.depth; simp only [Stack.mub0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits))

set_option maxRecDepth 100000 in
theorem mub0_b0 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 19481 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89344) :: wd 19495 :: wd sh :: wd rs :: wd rl :: tail) M) 24 := by
  mub65_pre
  glam65_rreach [8251, 8252, 8253, 8254, 8255, 8256, 8257]

set_option maxRecDepth 100000 in
theorem mub0_b1 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19495 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89376) :: wd 19516 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  mub65_pre
  glam65_rreach [8258, 8259, 8260, 8261, 8262, 8263, 8264, 8265, 8266, 8267, 8268, 8269, 8270, 8271] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b2 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19516 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89408) :: wd 19539 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  mub65_pre
  glam65_rreach [8272, 8273, 8274, 8275, 8276, 8277, 8278, 8279, 8280, 8281, 8282, 8283, 8284, 8285] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b3 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19539 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89440) :: wd 19562 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  mub65_pre
  glam65_rreach [8286, 8287, 8288, 8289, 8290, 8291, 8292, 8293, 8294, 8295, 8296, 8297, 8298, 8299] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b4 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19562 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89472) :: wd 19585 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  mub65_pre
  glam65_rreach [8300, 8301, 8302, 8303, 8304, 8305, 8306, 8307, 8308, 8309, 8310, 8311, 8312, 8313] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b5 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19585 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89504) :: wd 19608 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  mub65_pre
  glam65_rreach [8314, 8315, 8316, 8317, 8318, 8319, 8320, 8321, 8322, 8323, 8324, 8325, 8326, 8327] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b6 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19608 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89536) :: wd 19631 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  mub65_pre
  glam65_rreach [8328, 8329, 8330, 8331, 8332, 8333, 8334, 8335, 8336, 8337, 8338, 8339, 8340, 8341] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b7 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19631 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (word M 89568) :: wd 19654 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  mub65_pre
  glam65_rreach [8342, 8343, 8344, 8345, 8346, 8347, 8348, 8349, 8350, 8351, 8352, 8353, 8354, 8355] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b8 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 19654 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 18543 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 5259 :: wd 19713 ::
        wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  mub65_pre
  glam65_rreach [8356, 8357, 8358, 8359, 8360, 8361, 8362, 8363, 8364, 8365, 8366, 8367, 8368, 8369, 8370, 8371] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b9 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 19713 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (65280 &&& word s.executionEnv.calldata 5259 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 5259 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 19739 :: wd sh :: wd rs :: wd rl :: tail) M) 51 := by
  mub65_pre
  glam65_rreach [8372, 8373, 8374, 8375, 8376, 8377, 8378, 8379, 8380, 8381, 8382, 8383, 8384, 8385, 8386, 8387]

set_option maxRecDepth 100000 in
theorem mub0_b10l {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : 135 < s.executionEnv.calldata.size - 5195) :
    Reach (callState s 19739 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rl tail
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 67 := by
  mub65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [8388, 8389, 8390, 8391, 8392, 8393, 8394, 8395, 8396, 8397, 8398, 8399, 8400, 8401, 8402, 8403, 8443, 8444, 8445, 8446, 8447] with [word_mstore_disjoint, hj]

set_option maxRecDepth 100000 in
theorem mub0_b10s {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 5195 ≤ 135) :
    Reach (callState s 19739 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 19266 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 5195) * 8)) :: wd 19783 ::
        wd (s.executionEnv.calldata.size - 5195) :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 93 := by
  mub65_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 5195) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 5195) ≤ 7 := Nat.and_le_left
    omega
  glam65_rreach [8388, 8389, 8390, 8391, 8392, 8393, 8394, 8395, 8396, 8397, 8398, 8399, 8400, 8401, 8402, 8403, 8404, 8405, 8406, 8407, 8408, 8409, 8410, 8411, 8412, 8413, 8414, 8415] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b11 {s : State} (hs : Ctx s) {rl rs : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (hrs : RetOK Stack.mub0 rs (wd rl :: tail)) (M : ByteArray)
    {r p sh : Nat} (hsh : sh < 4) (hp : p ≤ 135) :
    Reach (callState s 19783 (wd r :: wd p :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rs (wd rl :: tail)
        (MachineState.writeBytes
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
            ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32))
          (Data.Bytes.natToBytesPadded
            ((word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
                ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32)) 512 ^^^
              7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 82 := by
  mub65_pre
  have hret := hrs.small
  have hj := hrs.jumpdest
  glam65_rreach [8416, 8417, 8418, 8419, 8420, 8421, 8422, 8423, 8424, 8425, 8426, 8427, 8428, 8429, 8430, 8431, 8432, 8433, 8434, 8435, 8436, 8437, 8438, 8439, 8440, 8441, 8442] with [word_mstore_disjoint, hj]

end MlDsaOptGlam65.Proofs.WP4
