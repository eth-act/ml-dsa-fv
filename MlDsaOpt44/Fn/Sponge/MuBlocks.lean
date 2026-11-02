import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `mu0`: straight-line blocks between the calls
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

set_option maxRecDepth 100000 in
theorem mu0_b0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 3732 ≤ 69) :
    Reach (callState s 12640 (wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64768) :: wd 12633 :: wd (s.executionEnv.calldata.size - 3732) ::
        wd sh :: wd ret :: tail) M) 54 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  opt44_reach [5352, 5353, 5354, 5355, 5356, 5357, 5358, 5359, 5360, 5361, 5362, 5363, 5364, 5365, 5366]

set_option maxRecDepth 100000 in
theorem mu0_skip {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hml : 69 < s.executionEnv.calldata.size - 3732) :
    Reach (callState s 12640 (wd sh :: wd ret :: tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [5352, 5353, 5354, 5355, 5356, 5357, 5358, 5359, 5360, 5545, 5546, 5547, 5548] with [hj]

set_option maxRecDepth 100000 in
theorem mu0_b1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12633 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64800) :: wd 12653 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12653 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64832) :: wd 12675 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12675 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64864) :: wd 12697 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12697 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64896) :: wd 12719 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12719 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64928) :: wd 12741 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12741 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64960) :: wd 12763 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12763 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (word M 64992) :: wd 12785 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463, 5464] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12785 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 11702 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 3730 :: wd 12844 :: wd mlen ::
        wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5465, 5466, 5467, 5468, 5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479, 5480] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 12844 (wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (65280 &&& word s.executionEnv.calldata 3730 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 3730 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 12870 :: wd mlen :: wd sh :: wd ret :: tail) M) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [5481, 5482, 5483, 5484, 5485, 5486, 5487, 5488, 5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496]

set_option maxRecDepth 100000 in
theorem mu0_b10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4)
    (hml : mlen ≤ 69) :
    Reach (callState s 12870 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12425 (wd (31 * 2 ^ ((7 &&& 66 + mlen) * 8)) :: wd 12905 :: wd (66 + mlen) ::
        wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 72 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hpad : (7 &&& 66 + mlen) * 8 < 256 := by
    have : (7 &&& 66 + mlen) ≤ 7 := Nat.and_le_left
    omega
  opt44_reach [5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505, 5506, 5507, 5508, 5509, 5510, 5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r p mlen sh : Nat} (hsh : sh < 4)
    (hp : p ≤ 135) :
    Reach (callState s 12905 (wd r :: wd p :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s ret tail
        (MachineState.writeBytes
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
            ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32))
          (Data.Bytes.natToBytesPadded
            ((word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
                ((r * 2 ^ sh ^^^ word M (0 + p / 8 * 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (0 + p / 8 * 32)) 512 ^^^
              7237005577332262213973186563042994240829374041602535252466099000494570602496 * 2 ^ sh) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 85 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548] with [word_mstore_disjoint, hj]

end MlDsaOpt44.Proofs.WP4
