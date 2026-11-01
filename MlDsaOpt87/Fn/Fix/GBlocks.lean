import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/GBlocks.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `10952, 10981, 11013, 11045` and the exit `11077`, stack
`flags :: ok :: amask :: ret :: tail`.
-/

namespace MlDsaOpt87.Proofs.Fix

open MlDsaOpt44.Proofs  -- port: the 44 `Fix` namespace is not imported here

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- The OR of the first 32 flag words, masked to bit 23 of each lane (as `gfix` computes it). -/
def gflags (M : ByteArray) : Nat :=
  52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232))))))))))))))))))))))))))))))))

theorem gflags_def (M : ByteArray) : 52656145834278593351813509227247135921718862144084218434291761152 &&&
    (word M 32224 ||| (word M 32192 ||| (word M 32160 ||| (word M 32128 ||| (word M 32096 ||| (word M 32064 ||| (word M 32032 ||| (word M 32000 ||| (word M 31968 ||| (word M 31936 ||| (word M 31904 ||| (word M 31872 ||| (word M 31840 ||| (word M 31808 ||| (word M 31776 ||| (word M 31744 ||| (word M 31712 ||| (word M 31680 ||| (word M 31648 ||| (word M 31616 ||| (word M 31584 ||| (word M 31552 ||| (word M 31520 ||| (word M 31488 ||| (word M 31456 ||| (word M 31424 ||| (word M 31392 ||| (word M 31360 ||| (word M 31328 ||| (word M 31296 ||| (word M 31264 ||| (word M 31232)))))))))))))))))))))))))))))))) = gflags M := rfl

theorem gflags_lt (M : ByteArray) : gflags M < 2 ^ 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem gflags_mod (M : ByteArray) :
    gflags M % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = gflags M :=
  Nat.mod_eq_of_lt (gflags_lt M)

theorem gone_land (x : Nat) : 1 &&& x = x % 2 := by
  rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x 1

theorem gmod2_mod (x : Nat) :
    x % 2 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = x % 2 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

macro "gx_close" : tactic => `(tactic| (all_goals first | (congr 1; omega) | rfl | skip))


theorem gx_pre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 12615 (wd amask :: wd ret :: tail) M)
      (callState s 12813 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  opt87_reach [5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463, 5464, 5465, 5466, 5467] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 12615 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  opt87_reach [5364, 5365, 5366, 5367, 5368, 5369, 5370, 5371, 5372, 5373, 5374, 5375, 5376, 5377, 5378, 5379, 5380, 5381, 5382, 5383, 5384, 5385, 5386, 5387, 5388, 5389, 5390, 5391, 5392, 5393, 5394, 5395, 5396, 5397, 5398, 5399, 5400, 5401, 5402, 5403, 5404, 5405, 5406, 5407, 5408, 5409, 5410, 5411, 5412, 5413, 5414, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5431, 5432, 5433, 5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446, 5447, 5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461, 5462, 5463, 5464, 5465, 5466, 5467, 5556, 5557, 5558, 5559, 5560, 5561] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 12813 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12842 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  opt87_reach [5468, 5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_call0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1) :
    Reach (callState s 12813 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14410 (wd 0 :: wd 12837 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 58 := by
  opt87_reach [5468, 5469, 5470, 5471, 5472, 5473, 5474, 5475, 5476, 5477, 5478, 5479, 5480, 5481, 5482, 5483] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 12837 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12842 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5484, 5485, 5486, 5487, 5488]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 12842 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12874 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_call1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1) :
    Reach (callState s 12842 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14410 (wd 64 :: wd 12869 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 61 := by
  opt87_reach [5489, 5490, 5491, 5492, 5493, 5494, 5495, 5496, 5497, 5498, 5499, 5500, 5501, 5502, 5503, 5504, 5505] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 12869 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12874 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5506, 5507, 5508, 5509, 5510]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 12874 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12906 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519, 5520, 5521, 5522, 5523] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_call2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1) :
    Reach (callState s 12874 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14410 (wd 128 :: wd 12901 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 61 := by
  opt87_reach [5511, 5512, 5513, 5514, 5515, 5516, 5517, 5518, 5519, 5520, 5521, 5522, 5523, 5524, 5525, 5526, 5527] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 12901 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12906 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5528, 5529, 5530, 5531, 5532]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 12906 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12938 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt87_reach [5533, 5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_call3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1) :
    Reach (callState s 12906 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 14410 (wd 192 :: wd 12933 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 61 := by
  opt87_reach [5533, 5534, 5535, 5536, 5537, 5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548, 5549] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 12933 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 12938 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt87_reach [5550, 5551, 5552, 5553, 5554]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2897 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 12938 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  opt87_reach [5555, 5556, 5557, 5558, 5559, 5560, 5561] with [hj]
  gx_close

end MlDsaOpt87.Proofs.Fix
