import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `trabs`: entry, loop body (unmasked group), last (masked) group with exit
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

theorem trabs_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) (kp lm n4 sh off : Nat) :
    Reach (callState s 11497 (wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      19 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  opt44_reach [4948, 4949, 4950, 4951, 4952, 4953, 4954]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_mid {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm n4 sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hn4 : 2 ≤ n4) (hn4' : n4 ≤ 25) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd n4 :: wd sh :: wd off :: wd ret :: tail) M)
      (callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (128 + kp) :: wd lm :: wd (n4 - 1) :: wd sh :: wd (32 + off) ::
        wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((sprNet (bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896) * 2 ^ sh ^^^ word M kp) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) kp)
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456) * 2 ^ sh ^^^ word M (32 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (32 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616) * 2 ^ sh ^^^ word M (64 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (64 + kp))
          (Data.Bytes.natToBytesPadded ((sprNet (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off)) * 2 ^ sh ^^^ word M (96 + kp)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) (96 + kp))) 826 := by
  have := hr.depth; simp only [Stack.trabs, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5161, 5162, 5163, 5164, 5165, 5166, 5167, 5168, 5169, 5170, 5171, 5172, 5173, 5174, 5175, 5176, 5177, 5178, 5179, 5180, 5181, 5182, 5183, 5184, 5185, 5186, 5187, 5188, 5189, 5190, 5191, 5192, 5193, 5194, 5195, 5196, 5197, 5198, 5199, 5200, 5201, 5202, 5203, 5204, 5205, 5206, 5207, 5208, 5209, 5210, 5211, 5212, 5213, 5214, 5215, 5216, 5217, 5218, 5219, 5220, 5221, 5222, 5223, 5224, 5225, 5226, 5227, 5228, 5229] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
    sstage_fold24, sstage_fold12, sstage_fold6, sstage_fold3, sprNet_fold, bsw8_fold, bsw16_fold,
    bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem trabs_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (M : ByteArray) {kp lm sh off : Nat}
    (hoff : off < 2 ^ 65) (hsh : sh < 4) (hlm : lm < 2 ^ 256) (hkp : kp + 128 ≤ 800) :
    Reach (callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd kp :: wd lm :: wd 1 :: wd sh :: wd off :: wd ret :: tail) M)
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
  opt44_reach [4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5161, 5162, 5163, 5164, 5165, 5166, 5167, 5168, 5169, 5170, 5171, 5172, 5173, 5174, 5175, 5176, 5177, 5178, 5179, 5180, 5181, 5182, 5183, 5184, 5185, 5186, 5187, 5188, 5189, 5190, 5191, 5192, 5193, 5194, 5195, 5196, 5197, 5198, 5199, 5200, 5201, 5202, 5203, 5204, 5205, 5206, 5207, 5208, 5209, 5210, 5211, 5212, 5213, 5214, 5215, 5216, 5217, 5218, 5219, 5220, 5221, 5222, 5223, 5224, 5225, 5226, 5227, 5228, 5229, 5230, 5231, 5232, 5233, 5234, 5235, 5236, 5237, 5238, 5239, 5240, 5241] with [word_mstore_disjoint, sstage_fold96, sstage_fold48,
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
  let I : Nat → State := fun i => callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * i) :: wd lm ::
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
  have hI : I (n4 - 1) = callState s 11674 (wd 0x1111111111111111111111111111111111111111111111111111111111111111 :: wd 0x0303030303030303030303030303030303030303030303030303030303030303 :: wd 0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f :: wd 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff :: wd 0xffff000000000000ffff000000000000ffff000000000000ffff :: wd 0xffffffff000000000000000000000000ffffffff :: wd (kp + 128 * (n4 - 1)) :: wd lm :: wd 1 ::
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

end MlDsaOpt44.Proofs.WP4
