import MlDsaOpt87.Fn.Decode.Lanes
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Decode/ZBlocks.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dz` (ML-DSA-87, WP G2)

20-bit twin of `MlDsaOpt44/Fn/Decode/ZBlocks.lean` (port plus the constants of
`gen_opt.py`'s `gen_decode` at 20 bits: windows at `off + 640 k`, shifts `20 kk`,
gather step `60`, chunk `30` bytes, clamp `−20`). Loop heads: `9929` (chunk loop,
stack `dp, off, acc, MB, end`), `10321` (gather loop). The entry is generic in the
base `[dp, off]` (two call sites).
-/

namespace MlDsaOpt87.Proofs.DecodeZ

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

-- port: generic base `[dp, off]` (two call sites)
theorem z_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off : Nat} :
    Reach (callState s 9890 (wd dp :: wd off :: wd ret :: tail) M)
      (callState s 9929 (wd dp :: wd off :: wd 0 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd (7808 + dp) :: wd ret :: tail) M) 27 := by
  opt87_reach [4102, 4103, 4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111]

theorem z_load0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9929 (wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10110 (wd (leNat s.executionEnv.calldata off 32) :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 172 := by
  opt87_reach [4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4155, 4156, 4157, 4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 10110 (wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10177 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 165 := by
  opt87_reach [4170, 4171, 4172, 4173, 4174, 4175, 4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223, 4224] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 10177 (wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10244 (wd (leNat s.executionEnv.calldata (1280 + off) 32) :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 :: wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 165 := by
  opt87_reach [4225, 4226, 4227, 4228, 4229, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263, 4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 10244 (wd V2 :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10321 (wd dp :: wd 0 :: wd (leNat s.executionEnv.calldata (1920 + off) 32) :: wd V2 ::
        wd V1 :: wd V0 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 190 := by
  opt87_reach [4280, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4290, 4291, 4292, 4293, 4294, 4295, 4296, 4297, 4298, 4299, 4300, 4301, 4302, 4303, 4304, 4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315, 4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4344] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_g1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {gp gs V0 V1 V2 V3 dp off acc e : Nat}
    (hgs : gs < 256) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 10321 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd dp :: wd off ::
        wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10386 (wd (gW gs V0 V1 V2 V3) :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 88 := by
  opt87_reach [4345, 4346, 4347, 4348, 4349, 4350, 4351, 4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373, 4374] with [gW_eq]

theorem z_g2 (hs : Ctx s) (M : ByteArray) {W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 32 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10386 (wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 :: wd x6 ::
        wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 10486 (wd (zf (zR W)) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)) 56 := by
  opt87_reach [4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392, 4393] with [zR_eq, zsub, zv_mod, zf_eq, Nat.or_zero]

theorem z_g3 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 64 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10486 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 10591 (wd (zf (zR (W / 1048576)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 ::
        wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 1048576))) 32) (32 + gp)))
        66 := by
  opt87_reach [4394, 4395, 4396, 4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4405, 4406, 4407, 4408, 4409, 4410, 4411, 4412, 4413, 4414, 4415] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g4 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 96 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10591 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 10696 (wd (zf (zR (W / 1099511627776)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 ::
        wd x3 :: wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 1099511627776))) 32) (64 + gp)))
        66 := by
  opt87_reach [4416, 4417, 4418, 4419, 4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g5 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {Lf W gp gs V0 V1 V2 V3 dp off acc e : Nat} :
    Reach (callState s 10696 (wd Lf :: wd W :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10709 (wd (96 + gp) :: wd (60 + gs) :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd (acc ||| Lf) :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 31 := by
  opt87_reach [4438, 4439, 4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447, 4448]

theorem z_gnext (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp gs V0 V1 V2 V3 dp off acc e : Nat} (hgs : gs < 240) :
    Reach (callState s 10709 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 10321 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 22 := by
  opt87_reach [4449, 4450, 4451, 4452, 4453]

theorem z_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hle : dp + 384 ≤ e) (he : e < 2 ^ 64) :
    Reach (callState s 10709 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9929 (wd (384 + dp) :: wd (30 + off) :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
        111 := by
  opt87_reach [4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4485, 4486, 4487]

theorem z_clamp (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hne : dp ≠ e) (hgt : e < dp + 384) (he : dp < 2 ^ 64)
    (hoff : off < 2 ^ 64) :
    Reach (callState s 10709 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9929 (wd (384 + dp - 256) :: wd (30 + off - 20) :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e ::
        wd ret :: tail) M) 135 := by
  opt87_reach [4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481, 4482, 4483, 4484, 4485, 4486, 4487]

theorem z_exit (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc : Nat} :
    Reach (callState s 10709 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd dp :: wd ret :: tail) M)
      (callState s ret (wd acc :: tail) M) 82 := by
  have := hr.small
  opt87_reach [4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4488, 4489, 4490, 4491, 4492, 4493, 4494, 4495, 4496] with [hr.jumpdest]

end

end MlDsaOpt87.Proofs.DecodeZ
