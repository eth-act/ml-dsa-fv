import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/MuBlocks.lean` by `scripts/proofgen_port.py 65` --sub 3732=5261 --sub 3730=5259 --sub 3731=5260 --sub 3666=5195 --sub 64768=89344 --sub 64800=89376 --sub 64832=89408 --sub 64864=89440 --sub 64896=89472 --sub 64928=89504 --sub 64960=89536 --sub 64992=89568 --sub 12633=13592 --sub 12653=13613 --sub 12675=13636 --sub 12697=13659 --sub 12719=13682 --sub 12741=13705 --sub 12763=13728 --sub 12785=13751 --sub 12844=13810 --sub 12870=13836 --sub 12905=13871 --path Fn/Sponge/=Fn/Mu0/; hand adjustments are marked `-- port:`. -/
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
    Reach (callState s 13565 (wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89344) :: wd 13592 :: wd (s.executionEnv.calldata.size - 5261) ::
        wd sh :: wd ret :: tail) M) 54 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  opt65_reach [5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5756, 5757, 5758, 5759, 5760, 5761]

set_option maxRecDepth 100000 in
theorem mu0_skip {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : 69 < s.executionEnv.calldata.size - 5261) :
    Reach (callState s 13565 (wd sh :: wd ret :: tail) M) (callState s ret tail M) 44 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hcs := hs.calldataFits
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [5747, 5748, 5749, 5750, 5751, 5752, 5753, 5754, 5755, 5940, 5941, 5942, 5943] with [hj]

set_option maxRecDepth 100000 in
theorem mu0_b1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13592 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89376) :: wd 13613 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5762, 5763, 5764, 5765, 5766, 5767, 5768, 5769, 5770, 5771, 5772, 5773, 5774, 5775] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13613 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89408) :: wd 13636 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5776, 5777, 5778, 5779, 5780, 5781, 5782, 5783, 5784, 5785, 5786, 5787, 5788, 5789] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13636 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89440) :: wd 13659 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5790, 5791, 5792, 5793, 5794, 5795, 5796, 5797, 5798, 5799, 5800, 5801, 5802, 5803] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13659 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89472) :: wd 13682 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13682 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89504) :: wd 13705 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5818, 5819, 5820, 5821, 5822, 5823, 5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13705 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89536) :: wd 13728 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 5844, 5845] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13728 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (word M 89568) :: wd 13751 :: wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5846, 5847, 5848, 5849, 5850, 5851, 5852, 5853, 5854, 5855, 5856, 5857, 5858, 5859] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13751 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 12455 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 5259 :: wd 13810 :: wd mlen ::
        wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5860, 5861, 5862, 5863, 5864, 5865, 5866, 5867, 5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b9 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {mlen sh : Nat} (hsh : sh < 4) :
    Reach (callState s 13810 (wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (65280 &&& word s.executionEnv.calldata 5259 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 5259 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 13836 :: wd mlen :: wd sh :: wd ret :: tail) M) 51 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5876, 5877, 5878, 5879, 5880, 5881, 5882, 5883, 5884, 5885, 5886, 5887, 5888, 5889, 5890, 5891]

set_option maxRecDepth 100000 in
theorem mu0_b10 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r mlen sh : Nat} (hsh : sh < 4)
    (hml : mlen ≤ 69) :
    Reach (callState s 13836 (wd r :: wd mlen :: wd sh :: wd ret :: tail) M)
      (callState s 13350 (wd (31 * 2 ^ ((7 &&& 66 + mlen) * 8)) :: wd 13871 :: wd (66 + mlen) ::
        wd mlen :: wd sh :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 72 := by
  have := hr.depth; simp only [Stack.mu0, Stack.trabs, Stack.spr, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hpad : (7 &&& 66 + mlen) * 8 < 256 := by
    have : (7 &&& 66 + mlen) ≤ 7 := Nat.and_le_left
    omega
  opt65_reach [5892, 5893, 5894, 5895, 5896, 5897, 5898, 5899, 5900, 5901, 5902, 5903, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5911, 5912, 5913, 5914] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mu0_b11 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (M : ByteArray) {r p mlen sh : Nat} (hsh : sh < 4)
    (hp : p ≤ 135) :
    Reach (callState s 13871 (wd r :: wd p :: wd mlen :: wd sh :: wd ret :: tail) M)
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
  opt65_reach [5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927, 5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938, 5939, 5940, 5941, 5942, 5943] with [word_mstore_disjoint, hj]

end MlDsaOpt65.Proofs.WP4
