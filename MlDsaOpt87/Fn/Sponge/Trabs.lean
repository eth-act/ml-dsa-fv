import MlDsaOpt87.Infra.Reflect
import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge/Trabs.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `trabs`: entry, loop body (unmasked group), last (masked) group with exit
-/

namespace MlDsaOpt87.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

theorem trabs_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) (kp lm n4 sh off : Nat) :
    Reach (callState s 13731 (wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      19 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  opt87_reach [6099, 5792, 5793, 5794, 5795, 5796, 6107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_mid {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm n4 sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hn4 : 2 ≤ n4) (hn4' : n4 ≤ 25) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (128 + kp) :: wd lm :: wd (n4 - 1) :: wd sh :: wd (32 + off) ::
        wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((sprNet (bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off)) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 826 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt87_rreach [6108, 5799, 5800, 5801, 5802, 6110, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817, 5818, 5819, 5820, 5821, 5822, 5823, 5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 6112, 6113, 6114, 6115, 6116, 6119, 6120, 5853, 6122, 5855, 5856, 5857, 5858, 5859, 6126, 6127, 5862, 6129, 5864, 5865, 5866, 6132, 5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875, 5876, 5877, 6138, 6139, 6140, 6141, 5882, 5883, 6174, 6175, 6176, 6177, 5888, 6207, 6208, 5891, 6210, 5893, 6212, 6213, 6214, 6215, 6216, 6217, 6218, 6219, 5902, 6221, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5911, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927, 5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938, 5939, 6222, 6223, 5942, 6225, 5944, 6227, 6228, 6229, 6230, 6231, 6232, 6233, 6234, 6235, 6236, 5955, 6238, 5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981, 5982, 5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991, 5992, 6239, 6240, 5995, 6242, 5997, 6244, 6245, 6246, 6247, 6248, 6249, 6250, 6251, 6252, 6007, 6008, 6009, 6010, 6011, 6012, 6013, 6014, 6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029, 6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037, 6038, 6039, 6040, 6041, 6042, 6253, 6254, 6045, 6256, 6047, 6258, 6259, 6260, 6261, 6262, 6263, 6264, 6265, 6266, 6057, 6268, 6269, 6060, 6061, 6272, 6273, 6064, 6274, 6276, 6277, 6278, 6069, 6070, 6281, 6282] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
    sstage_fold24, sstage_fold12, sstage_fold6, sstage_fold3, sprNet_fold, bsw8_fold, bsw16_fold,
    bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hlm : lm < 2 ^ 256) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd 1 :: wd sh :: wd off :: wd ret :: tail) M)
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
  opt87_reach [6108, 5799, 5800, 5801, 5802, 6110, 5804, 5805, 5806, 5807, 5808, 5809, 5810, 5811, 5812, 5813, 5814, 5815, 5816, 5817, 5818, 5819, 5820, 5821, 5822, 5823, 5824, 5825, 5826, 5827, 5828, 5829, 5830, 5831, 5832, 5833, 5834, 5835, 5836, 5837, 5838, 5839, 5840, 5841, 5842, 5843, 6112, 6113, 6114, 6115, 6116, 5849, 6118, 6119, 6120, 5853, 6122, 5855, 5856, 5857, 5858, 5859, 6126, 6127, 5862, 6129, 5864, 5865, 5866, 6132, 5868, 5869, 5870, 5871, 5872, 5873, 5874, 5875, 5876, 5877, 6138, 6139, 6140, 6141, 5882, 5883, 6174, 6175, 6176, 6177, 5888, 6207, 6208, 5891, 6210, 5893, 6212, 6213, 6214, 6215, 6216, 6217, 6218, 6219, 5902, 6221, 5904, 5905, 5906, 5907, 5908, 5909, 5910, 5911, 5912, 5913, 5914, 5915, 5916, 5917, 5918, 5919, 5920, 5921, 5922, 5923, 5924, 5925, 5926, 5927, 5928, 5929, 5930, 5931, 5932, 5933, 5934, 5935, 5936, 5937, 5938, 5939, 6222, 6223, 5942, 6225, 5944, 6227, 6228, 6229, 6230, 6231, 6232, 6233, 6234, 6235, 6236, 5955, 6238, 5957, 5958, 5959, 5960, 5961, 5962, 5963, 5964, 5965, 5966, 5967, 5968, 5969, 5970, 5971, 5972, 5973, 5974, 5975, 5976, 5977, 5978, 5979, 5980, 5981, 5982, 5983, 5984, 5985, 5986, 5987, 5988, 5989, 5990, 5991, 5992, 6239, 6240, 5995, 6242, 5997, 6244, 6245, 6246, 6247, 6248, 6249, 6250, 6251, 6252, 6007, 6008, 6009, 6010, 6011, 6012, 6013, 6014, 6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6024, 6025, 6026, 6027, 6028, 6029, 6030, 6031, 6032, 6033, 6034, 6035, 6036, 6037, 6038, 6039, 6040, 6041, 6042, 6253, 6254, 6045, 6256, 6047, 6258, 6259, 6260, 6261, 6262, 6263, 6264, 6265, 6266, 6057, 6268, 6269, 6060, 6061, 6272, 6273, 6064, 6274, 6276, 6277, 6278, 6069, 6070, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288, 6289, 6290, 6291, 6292, 6293, 6296] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
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
  let I : Nat → State := fun i => callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * i) :: wd lm ::
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
  have hI : I (n4 - 1) = callState s 13963 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * (n4 - 1)) :: wd lm :: wd 1 ::
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

end MlDsaOpt87.Proofs.WP4
