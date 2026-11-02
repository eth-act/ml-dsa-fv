import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-!
# `gfix`: straight-line blocks

Slot-check heads at pcs `10699, 10748, 10800, 10852` and the exit `10904`, stack
`flags :: ok :: amask :: ret :: tail`. Bit 0 of `flags` records that `blkt`
has made the tail of block 4 (before the group's first `fix`).
-/

namespace MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

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
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M ≠ 0) :
    Reach (callState s 10501 (wd amask :: wd ret :: tail) M)
      (callState s 10699 (wd (gflags M) :: wd 1 :: wd amask :: wd ret :: tail) M) 317 := by
  opt44_reach [4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4344, 4345, 4346, 4347, 4348, 4349, 4350, 4351, 4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392, 4393, 4394, 4395, 4396, 4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4405, 4406, 4407, 4408, 4409, 4410, 4411, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419] with [gflags_def, gflags_mod, hf]
  gx_close

theorem gx_fast {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask : Nat) (hf : gflags M = 0) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 10501 (wd amask :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) M) 336 := by
  opt44_reach [4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4344, 4345, 4346, 4347, 4348, 4349, 4350, 4351, 4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392, 4393, 4394, 4395, 4396, 4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4405, 4406, 4407, 4408, 4409, 4410, 4411, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419, 4556, 4557, 4558, 4559, 4560, 4561] with [gflags_def, gflags_mod, hf, hj]
  gx_close

theorem gx_skip0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 0) :
    Reach (callState s 10699 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10748 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 42 := by
  opt44_reach [4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 10699 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10212 (wd 10730 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 78 := by
  opt44_reach [4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 10730 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 0 :: wd 10743 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 24 := by
  opt44_reach [4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447]
  gx_close

theorem gx_callF0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 1 &&& f / 8388608) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 10699 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 0 :: wd 10743 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 81 := by
  opt44_reach [4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4443, 4444, 4445, 4446, 4447] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 10743 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10748 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt44_reach [4448, 4449, 4450, 4451, 4452]
  gx_close

theorem gx_skip1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 0) :
    Reach (callState s 10748 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10800 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt44_reach [4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 10748 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10212 (wd 10781 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt44_reach [4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 10781 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 64 :: wd 10795 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt44_reach [4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481]
  gx_close

theorem gx_callF1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 2 &&& f / 154742504910672534362390528) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 10748 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 64 :: wd 10795 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt44_reach [4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4477, 4478, 4479, 4480, 4481] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 10795 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10800 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt44_reach [4482, 4483, 4484, 4485, 4486]
  gx_close

theorem gx_skip2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 0) :
    Reach (callState s 10800 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10852 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt44_reach [4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 10800 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10212 (wd 10833 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt44_reach [4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504, 4505, 4506, 4507] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 10833 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 128 :: wd 10847 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt44_reach [4508, 4509, 4510, 4511, 4512, 4513, 4514, 4515]
  gx_close

theorem gx_callF2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 4 &&& f / 2854495385411919762116571938898990272765493248) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 10800 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 128 :: wd 10847 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt44_reach [4487, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504, 4511, 4512, 4513, 4514, 4515] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 10847 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10852 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt44_reach [4516, 4517, 4518, 4519, 4520]
  gx_close

theorem gx_skip3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 0) :
    Reach (callState s 10852 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10904 (wd f :: wd ok :: wd amask :: wd ret :: tail) M) 44 := by
  opt44_reach [4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528, 4529, 4530, 4531, 4532, 4533] with [gone_land, gmod2_mod, hc]
  gx_close

theorem gx_callT3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 0) :
    Reach (callState s 10852 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10212 (wd 10885 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 80 := by
  opt44_reach [4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528, 4529, 4530, 4531, 4532, 4533, 4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_tret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hfl : f < 2 ^ 256) :
    Reach (callState s 10885 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 192 :: wd 10899 :: wd (1 ||| f) :: wd ok :: wd amask :: wd ret :: tail) M) 25 := by
  opt44_reach [4542, 4543, 4544, 4545, 4546, 4547, 4548, 4549]
  gx_close

theorem gx_callF3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (ha : amask < 16) (hfl : f < 2 ^ 256) (hc : (amask / 8 &&& f / 52656145834278593348959013841835216159447547700274555627155488768) % 2 = 1)
    (hb : f % 2 = 1) :
    Reach (callState s 10852 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 13206 (wd 192 :: wd 10899 :: wd f :: wd ok :: wd amask :: wd ret :: tail) M) 84 := by
  opt44_reach [4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528, 4529, 4530, 4531, 4532, 4533, 4534, 4535, 4536, 4537, 4538, 4545, 4546, 4547, 4548, 4549] with [gone_land, gmod2_mod, hc, hb]
  gx_close

theorem gx_ret3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok r : Nat) (hok : ok < 2) (hr : r < 2) :
    Reach (callState s 10899 (wd r :: wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s 10904 (wd f :: wd (ok &&& r) :: wd amask :: wd ret :: tail) M) 13 := by
  opt44_reach [4550, 4551, 4552, 4553, 4554]
  gx_close

theorem gx_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (amask f ok : Nat) (hj : EvmSemantics.EVM.Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 65536) :
    Reach (callState s 10904 (wd f :: wd ok :: wd amask :: wd ret :: tail) M)
      (callState s ret (wd ok :: tail) M) 20 := by
  opt44_reach [4555, 4556, 4557, 4558, 4559, 4560, 4561]  with [hj]
  gx_close

end MlDsaOpt44.Proofs.Fix
