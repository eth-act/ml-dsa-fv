import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/MuBlocks.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568 --sub 12633=13221 --sub 12653=13242 --sub 12675=13265 --sub 12697=13288 --sub 12719=13311 --sub 12741=13334 --sub 12763=13357 --sub 12785=13380 --sub 12844=13439 --sub 12870=13465 --sub 12905=13500 --path Fn/Sponge/=Fn/Mu0/; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `mu0`: straight-line blocks between the calls
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

set_option maxRecDepth 100000 in
theorem mu0_b0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 5261 ≤ 69) :
    Reach (callState s 13194 (wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89344) :: wd 13221 :: wd (s.executionEnv.calldata.size - 5261) ::
        wd sh :: wd ret :: tail) M) 54 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  opt65_reach [5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591]

set_option maxRecDepth 100000 in
theorem mu0_skip {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : 69 < s.executionEnv.calldata.size - 5261) :
    Reach (callState s 13194 (wd sh :: wd ret :: tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5770, 5771, 5772, 5773] with [hj]

set_option maxRecDepth 100000 in
theorem mu0_b1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13221 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89376) :: wd 13242 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600, 5601, 5602, 5603, 5604, 5605] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13242 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89408) :: wd 13265 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5606, 5607, 5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13265 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89440) :: wd 13288 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5620, 5621, 5622, 5623, 5624, 5625, 5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13288 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89472) :: wd 13311 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5634, 5635, 5636, 5637, 5638, 5639, 5640, 5641, 5642, 5643, 5644, 5645, 5646, 5647] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13311 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89504) :: wd 13334 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5648, 5649, 5650, 5651, 5652, 5653, 5654, 5655, 5656, 5657, 5658, 5659, 5660, 5661] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13334 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89536) :: wd 13357 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5662, 5663, 5664, 5665, 5666, 5667, 5668, 5669, 5670, 5671, 5672, 5673, 5674, 5675] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13357 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (word M 89568) :: wd 13380 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5676, 5677, 5678, 5679, 5680, 5681, 5682, 5683, 5684, 5685, 5686, 5687, 5688, 5689] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13380 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12084 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 5259 :: wd 13439 :: wd mlen ::
        wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5690, 5691, 5692, 5693, 5694, 5695, 5696, 5697, 5698, 5699, 5700, 5701, 5702, 5703, 5704, 5705] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13439 (wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (65280 &&& word s.executionEnv.calldata 5259 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 5259 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 13465 :: wd mlen :: wd sh :: wd ret :: tail) M) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5706, 5707, 5708, 5709, 5710, 5711, 5712, 5713, 5714, 5715, 5716, 5717, 5718, 5719, 5720, 5721]

set_option maxRecDepth 100000 in
theorem mu0_b10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4)
    (hml : mlen ≤ 69) :
    Reach (callState s 13465 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12979 (wd (31 * 2 ^ ((7 &&& 66 + mlen) * 8)) :: wd 13500 :: wd (66 + mlen) ::
        wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 72 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hpad : (7 &&& 66 + mlen) * 8 < 256 := by
    have : (7 &&& 66 + mlen) ≤ 7 := Nat.and_le_left
    omega
  opt65_reach [5722, 5723, 5724, 5725, 5726, 5727, 5728, 5729, 5730, 5731, 5732, 5733, 5734, 5735, 5736, 5737, 5738, 5739, 5740, 5741, 5742, 5743, 5744] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r p mlen sh : Nat} (hsh : sh < 4)
    (hp : p ≤ 135) :
    Reach (callState s 13500 (wd r :: wd p :: wd mlen :: wd sh :: wd ret :: tail) M)
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
  opt65_reach [5745, 5746, 5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5756, 5757, 5758, 5759, 5760, 5761, 5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773] with [word_mstore_disjoint, hj]

end MlDsaOpt65.Proofs.WP4
