import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# `mub0`: straight-line blocks between the calls

`b0`–`b7` absorb the eight `TRL` lanes (one `spr` call each), `b8` calls
`trabs`, `b9` builds the two signature bytes, `b10` absorbs them into lane 8
and branches on `len = |M| + 66`, `b11` adds the padding.
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

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
    Reach (callState s 12640 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64768) :: wd 12653 :: wd sh :: wd rs :: wd rl :: tail) M) 24 := by
  mub_pre
  opt44_reach [5471, 5472, 5473, 5474, 5475, 5476, 5477]

set_option maxRecDepth 100000 in
theorem mub0_b1 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12653 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64800) :: wd 12673 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  mub_pre
  opt44_reach [5478, 5479, 5480, 5481, 5482, 5483, 5484, 5485, 5486, 5487, 5488, 5489, 5490, 5491] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b2 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12673 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64832) :: wd 12695 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  mub_pre
  opt44_reach [5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b3 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12695 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64864) :: wd 12717 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  mub_pre
  opt44_reach [5506, 5507, 5508, 5509, 5510, 5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b4 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12717 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64896) :: wd 12739 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  mub_pre
  opt44_reach [5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b5 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12739 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64928) :: wd 12761 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  mub_pre
  opt44_reach [5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b6 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12761 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64960) :: wd 12783 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  mub_pre
  opt44_reach [5548, 5549, 5550, 5551, 5552, 5553, 5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b7 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12783 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (word M 64992) :: wd 12805 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  mub_pre
  opt44_reach [5562, 5563, 5564, 5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b8 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 12805 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 11702 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 3730 :: wd 12864 ::
        wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  mub_pre
  opt44_reach [5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b9 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 12864 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (65280 &&& word s.executionEnv.calldata 3730 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 3730 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 12890 :: wd sh :: wd rs :: wd rl :: tail) M) 51 := by
  mub_pre
  opt44_reach [5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607]

set_option maxRecDepth 100000 in
theorem mub0_b10l {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : 135 < s.executionEnv.calldata.size - 3666) :
    Reach (callState s 12890 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rl tail
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 67 := by
  mub_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622, 5623, 5663, 5664, 5665, 5666, 5667] with [word_mstore_disjoint, hj]

set_option maxRecDepth 100000 in
theorem mub0_b10s {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 3666 ≤ 135) :
    Reach (callState s 12890 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12425 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 3666) * 8)) :: wd 12934 ::
        wd (s.executionEnv.calldata.size - 3666) :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 93 := by
  mub_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 3666) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 3666) ≤ 7 := Nat.and_le_left
    omega
  opt44_reach [5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622, 5623, 5624, 5625, 5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633, 5634, 5635] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b11 {s : State} (hs : Ctx s) {rl rs : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (hrs : RetOK Stack.mub0 rs (wd rl :: tail)) (M : ByteArray)
    {r p sh : Nat} (hsh : sh < 4) (hp : p ≤ 135) :
    Reach (callState s 12934 (wd r :: wd p :: wd sh :: wd rs :: wd rl :: tail) M)
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
  opt44_reach [5636, 5637, 5638, 5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647, 5648, 5649, 5650, 5651, 5652, 5653, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661, 5662] with [word_mstore_disjoint, hj]

end MlDsaOpt44.Proofs.WP4
