import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
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

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

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
    Reach (callState s 13365 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89344) :: wd 13379 :: wd sh :: wd rs :: wd rl :: tail) M) 24 := by
  mub65_pre
  opt65_reach [5818, 5819, 5820, 5821, 5822, 5823, 5824]

set_option maxRecDepth 100000 in
theorem mub0_b1 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13379 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89376) :: wd 13400 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 0 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)) 43 := by
  mub65_pre
  opt65_reach [5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b2 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13400 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89408) :: wd 13423 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 32 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)) 45 := by
  mub65_pre
  opt65_reach [5839, 5840, 5841, 5842, 5843, 5844, 5845, 5846, 5847, 5848, 5849, 5850, 5851, 5852] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b3 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13423 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89440) :: wd 13446 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 64 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)) 45 := by
  mub65_pre
  opt65_reach [5853, 5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863, 5864, 5865, 5866] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b4 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13446 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89472) :: wd 13469 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 96 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 45 := by
  mub65_pre
  opt65_reach [5867, 5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875, 5876, 5877, 5878, 5879, 5880] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b5 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13469 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89504) :: wd 13492 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 128 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)) 45 := by
  mub65_pre
  opt65_reach [5881, 5882, 5883, 5884, 5885, 5886, 5887, 5888, 5889, 5890, 5891, 5892, 5893, 5894] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b6 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13492 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89536) :: wd 13515 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 160 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)) 45 := by
  mub65_pre
  opt65_reach [5895, 5896, 5897, 5898, 5899, 5900, 5901, 5902, 5903, 5904, 5905, 5906, 5907, 5908] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b7 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13515 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (word M 89568) :: wd 13538 :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 192 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)) 45 := by
  mub65_pre
  opt65_reach [5909, 5910, 5911, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b8 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4) :
    Reach (callState s 13538 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 12427 (wd 256 :: wd 115792089237316195417293883273301227089434195242432897623355228563449095127040 :: wd 3 :: wd sh :: wd 5259 :: wd 13597 ::
        wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 224 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 51 := by
  mub65_pre
  opt65_reach [5923, 5924, 5925, 5926, 5927, 5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b9 {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {sh rs : Nat} :
    Reach (callState s 13597 (wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (65280 &&& word s.executionEnv.calldata 5259 /
              6901746346790563787434755862277025452451108972170386555162524223799296 |||
            word s.executionEnv.calldata 5259 /
              452312848583266388373324160190187140051835877600158453279131187530910662656) ::
        wd 13623 :: wd sh :: wd rs :: wd rl :: tail) M) 51 := by
  mub65_pre
  opt65_reach [5939, 5940, 5941, 5942, 5943, 5944, 5945, 5946, 5947, 5948, 5949, 5950, 5951, 5952, 5953, 5954]

set_option maxRecDepth 100000 in
theorem mub0_b10l {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : 135 < s.executionEnv.calldata.size - 5195) :
    Reach (callState s 13623 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s rl tail
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 67 := by
  mub65_pre
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [5955, 5956, 5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 6010, 6011, 6012, 6013, 6014] with [word_mstore_disjoint, hj]

set_option maxRecDepth 100000 in
theorem mub0_b10s {s : State} (hs : Ctx s) {rl : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (M : ByteArray) {r sh rs : Nat} (hsh : sh < 4)
    (hcd : 5261 ≤ s.executionEnv.calldata.size) (hml : s.executionEnv.calldata.size - 5195 ≤ 135) :
    Reach (callState s 13623 (wd r :: wd sh :: wd rs :: wd rl :: tail) M)
      (callState s 13150 (wd (31 * 2 ^ ((7 &&& s.executionEnv.calldata.size - 5195) * 8)) :: wd 13667 ::
        wd (s.executionEnv.calldata.size - 5195) :: wd sh :: wd rs :: wd rl :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M 256 ^^^ r * 2 ^ sh) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)) 93 := by
  mub65_pre
  have hpad : (7 &&& s.executionEnv.calldata.size - 5195) * 8 < 256 := by
    have : (7 &&& s.executionEnv.calldata.size - 5195) ≤ 7 := Nat.and_le_left
    omega
  opt65_reach [5955, 5956, 5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981, 5982] with [word_mstore_disjoint]

set_option maxRecDepth 100000 in
theorem mub0_b11 {s : State} (hs : Ctx s) {rl rs : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mub0 rl tail) (hrs : RetOK Stack.mub0 rs (wd rl :: tail)) (M : ByteArray)
    {r p sh : Nat} (hsh : sh < 4) (hp : p ≤ 135) :
    Reach (callState s 13667 (wd r :: wd p :: wd sh :: wd rs :: wd rl :: tail) M)
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
  opt65_reach [5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991, 5992, 5993, 5994, 5995, 5996, 5997, 5998, 5999, 6000, 6001, 6002, 6003, 6004, 6005, 6006, 6007, 6008, 6009] with [word_mstore_disjoint, hj]

end MlDsaOpt65.Proofs.WP4
