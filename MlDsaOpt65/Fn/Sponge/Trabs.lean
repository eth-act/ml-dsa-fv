import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/Trabs.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `trabs`: entry, loop body (unmasked group), last (masked) group with exit
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

theorem trabs_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) (kp lm n4 sh off : Nat) :
    Reach (callState s 12455 (wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      19 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  opt65_reach [5341, 5342, 5343, 5344, 5345, 5346, 5347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_mid {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm n4 sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hn4 : 2 ≤ n4) (hn4' : n4 ≤ 25) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (128 + kp) :: wd lm :: wd (n4 - 1) :: wd sh :: wd (32 + off) ::
        wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((sprNet (bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off)) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 826 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt65_reach [5348, 5349, 5350, 5351, 5352, 5353, 5354, 5355, 5356, 5357, 5358, 5359, 5360, 5361, 5362, 5363, 5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463, 5464, 5465, 5466, 5467, 5468, 5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479, 5480, 5481, 5482, 5483, 5484, 5485, 5486, 5487, 5488, 5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505, 5506, 5507, 5508, 5509, 5510, 5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519, 5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550, 5551, 5552, 5553, 5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575, 5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591, 5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607, 5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
    sstage_fold24, sstage_fold12, sstage_fold6, sstage_fold3, sprNet_fold, bsw8_fold, bsw16_fold,
    bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hlm : lm < 2 ^ 256) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd 1 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s ret tail (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((sprNet ((lm &&& bswapNet (word s.executionEnv.calldata off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (lm &&& bswapNet (word s.executionEnv.calldata off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (lm &&& bswapNet (word s.executionEnv.calldata off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (lm &&& bswapNet (word s.executionEnv.calldata off))) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 862 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  opt65_reach [5348, 5349, 5350, 5351, 5352, 5353, 5354, 5355, 5356, 5357, 5358, 5359, 5360, 5361, 5362, 5363, 5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463, 5464, 5465, 5466, 5467, 5468, 5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479, 5480, 5481, 5482, 5483, 5484, 5485, 5486, 5487, 5488, 5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505, 5506, 5507, 5508, 5509, 5510, 5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519, 5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550, 5551, 5552, 5553, 5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575, 5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5591, 5592, 5593, 5594, 5595, 5596, 5597, 5598, 5599, 5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607, 5608, 5609, 5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5619, 5620, 5621, 5622, 5623, 5624, 5625, 5626, 5627, 5628, 5629, 5630, 5631, 5632, 5633, 5634] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
    sstage_fold24, sstage_fold12, sstage_fold6, sstage_fold3, sprNet_fold, bsw8_fold, bsw16_fold,
    bsw32_fold, bswapNet_fold, hj]

theorem trabs_T_lt (m cd : ByteArray) (kp off lm n4 sh : Nat) (hsh : sh < 4) (u : Nat) :
    word m (kp + 32 * u) ^^^ spread (trLane cd off lm n4 u) * 2 ^ sh < 2 ^ 256 :=
  Nat.xor_lt_two_pow (word_lt _ _) (spread_sh_lt hsh)

set_option maxHeartbeats 4000000 in
theorem trabs_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (m : ByteArray) {off sh n4 lm kp : Nat}
    (hoff : off < 2 ^ 64) (hsh : sh < 4) (hn4 : 1 ≤ n4) (hlm : lm < 2 ^ 256)
    (hkp : kp + 128 * n4 ≤ KS + 800) (hkp' : KS ≤ kp) (hkp32 : kp % 32 = 0) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if kp ≤ KS + 32 * x ∧ KS + 32 * x < kp + 128 * n4 then
          word m (KS + 32 * x) ^^^
            spread (trLane s.executionEnv.calldata off lm n4 ((KS + 32 * x - kp) / 32)) * 2 ^ sh
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(kp, kp + 128 * n4)] ∧
      Call s Entry.trabs [wd kp, wd lm, wd n4, wd sh, wd off] ret tail m [] m' (Gas.trabs n4) := by
  simp only [KS, Nat.zero_add] at hkp hkp' ⊢
  have hstep : ∀ i, i < n4 → (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i))
          (Data.Bytes.natToBytesPadded ((sprNet ((if i + 1 = n4 then (lm &&& bswapNet (word s.executionEnv.calldata (off + 32 * i))) else bswapNet (word s.executionEnv.calldata (off + 32 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (kp + 128 * i)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (kp + 128 * i))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (if i + 1 = n4 then (lm &&& bswapNet (word s.executionEnv.calldata (off + 32 * i))) else bswapNet (word s.executionEnv.calldata (off + 32 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (32 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + (kp + 128 * i)))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (if i + 1 = n4 then (lm &&& bswapNet (word s.executionEnv.calldata (off + 32 * i))) else bswapNet (word s.executionEnv.calldata (off + 32 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (64 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + (kp + 128 * i)))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& (if i + 1 = n4 then (lm &&& bswapNet (word s.executionEnv.calldata (off + 32 * i))) else bswapNet (word s.executionEnv.calldata (off + 32 * i)))) * 2 ^ sh ^^^ word (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (96 + (kp + 128 * i))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + (kp + 128 * i))) =
      storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (i + 1)) := by
    intro i hi
    conv_rhs => rw [show 4 * (i + 1) = 4 * i + 3 + 1 by ring, storeWords_succ, storeWords_succ,
      storeWords_succ, storeWords_succ]
    by_cases hlast : i + 1 = n4
    · refine wbc (wbc (wbc (wbc rfl ?v0 (by ring)) ?v1 (by ring)) ?v2 (by ring)) ?v3 (by ring)
      case v0 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 0 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_pos hlast]; exact ext0 (Nat.lt_of_le_of_lt Nat.and_le_left hlm)
      case v1 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 1 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_pos hlast]; exact ext1 (Nat.lt_of_le_of_lt Nat.and_le_left hlm)
      case v2 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 2 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_pos hlast]; exact ext2 (Nat.lt_of_le_of_lt Nat.and_le_left hlm)
      case v3 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 3 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_pos hlast]; exact ext3 _
    · refine wbc (wbc (wbc (wbc rfl ?v0 (by ring)) ?v1 (by ring)) ?v2 (by ring)) ?v3 (by ring)
      case v0 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 0 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_neg (by omega)]; exact ext0 (bswapNet_lt _)
      case v1 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 1 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_neg (by omega)]; exact ext1 (bswapNet_lt _)
      case v2 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 2 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_neg (by omega)]; exact ext2 (bswapNet_lt _)
      case v3 =>
        refine trabs_lane (m := m) (cd := s.executionEnv.calldata) (off := off) (lm := lm) (n4 := n4)
          (kp := kp) (i := i) 3 (by norm_num) hsh ?_ _ ?_
        · rw [word_storeWords_out (Or.inr (by omega))]; congr 1; omega
        · rw [if_neg (by omega)]; exact ext3 _
  let I : Nat → State := fun i => callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * i) :: wd lm ::
    wd (n4 - i) :: wd sh :: wd (off + 32 * i) :: wd ret :: tail) (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i))
  have hbody : ∀ i, i < n4 - 1 → Reach (I i) (I (i + 1)) 826 := by
    intro i hi
    have h := trabs_mid hs hr (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * i)) (kp := kp + 128 * i) (lm := lm) (n4 := n4 - i) (sh := sh)
      (off := off + 32 * i) (by omega) hsh (by omega) (by omega) (by omega)
    have h2 := hstep i (by omega)
    rw [if_neg (by omega)] at h2
    rw [h2, show 128 + (kp + 128 * i) = kp + 128 * (i + 1) by ring, show n4 - i - 1 = n4 - (i + 1) by omega,
      show 32 + (off + 32 * i) = off + 32 * (i + 1) by ring] at h
    exact h
  have hlast := trabs_last hs hr (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (n4 - 1))) (kp := kp + 128 * (n4 - 1))
    (lm := lm) (sh := sh) (off := off + 32 * (n4 - 1)) (by omega) hsh hlm (by omega)
  have h2 := hstep (n4 - 1) (by omega)
  rw [if_pos (by omega)] at h2
  rw [h2, show n4 - 1 + 1 = n4 by omega] at hlast
  have hloop := Reach.loop (I := I) (n4 - 1) hbody
  have hI : I (n4 - 1) = callState s 12632 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * (n4 - 1)) :: wd lm :: wd 1 ::
      wd sh :: wd (off + 32 * (n4 - 1)) :: wd ret :: tail) (storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * (n4 - 1))) := by
    simp only [I, show n4 - (n4 - 1) = 1 by omega]
  rw [hI] at hloop
  have hentry := trabs_entry hs hr m kp lm n4 sh off
  refine ⟨storeWords m kp (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh) (4 * n4), fun x hx => ?_,
    storeWords_mono_frame (le_refl _) (by omega), ?_⟩
  · split
    · rename_i hin
      have e : kp + 32 * ((32 * x - kp) / 32) = 32 * x := by omega
      have h := word_storeWords_get (m := m) (base := kp) (k := 4 * n4) (i := (32 * x - kp) / 32)
        (v := (fun u => word m (kp + 32 * u) ^^^ spread (trLane s.executionEnv.calldata off lm n4 u) * 2 ^ sh))
        (trabs_T_lt m s.executionEnv.calldata kp off lm n4 sh hsh ((32 * x - kp) / 32)) (by omega)
      beta_reduce at h
      rw [e] at h
      exact h
    · exact word_storeWords_out (by omega)
  · rw [call_iff, Entry.trabs, Gas.trabs]
    have htot := hentry.trans (hloop.trans hlast)
    refine (htot.mono ?_).of_eq rfl rfl
    have : (n4 - 1) * 826 + 826 = n4 * 826 := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn4]
    omega

end MlDsaOpt65.Proofs.WP4
