import MlDsaOpt65.Fn.Decode.Lanes
import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Decode/ZBlocks.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dz` (ML-DSA-65, WP G2)

20-bit twin of `MlDsaOpt44/Fn/Decode/ZBlocks.lean` (port plus the constants of
`gen_opt.py`'s `gen_decode` at 20 bits: windows at `off + 640 k`, shifts `20 kk`,
gather step `60`, chunk `30` bytes, clamp `−20`; v4 stores `zv` and flag words `zf` in
`z_g2` … `z_g4`). Loop heads: `9044` (chunk loop,
stack `dp, off, acc, MB, end`), `9436` (gather loop). The entry is generic in the
base `[dp, off]` (two call sites).
-/

namespace MlDsaOpt65.Proofs.DecodeZ

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

-- port: generic base `[dp, off]` (two call sites)
theorem z_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off : Nat} :
    Reach (callState s 9005 (wd dp :: wd off :: wd ret :: tail) M)
      (callState s 9044 (wd dp :: wd off :: wd 0 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd (7808 + dp) :: wd ret :: tail) M) 27 := by
  opt65_reach [3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794]

theorem z_load0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9044 (wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9225 (wd (leNat s.executionEnv.calldata off 32) :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 172 := by
  opt65_reach [3795, 3796, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9225 (wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9292 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 165 := by
  opt65_reach [3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9292 (wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9359 (wd (leNat s.executionEnv.calldata (1280 + off) 32) :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 :: wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 165 := by
  opt65_reach [3908, 3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943, 3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9359 (wd V2 :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9436 (wd dp :: wd 0 :: wd (leNat s.executionEnv.calldata (1920 + off) 32) :: wd V2 ::
        wd V1 :: wd V0 :: wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 190 := by
  opt65_reach [3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_g1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {gp gs V0 V1 V2 V3 dp off acc e : Nat}
    (hgs : gs < 256) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 9436 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd dp :: wd off ::
        wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9501 (wd (gW gs V0 V1 V2 V3) :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 88 := by
  opt65_reach [4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052, 4053, 4054, 4055, 4056, 4057] with [gW_eq]

theorem z_g2 (hs : Ctx s) (M : ByteArray) {W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 32 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9501 (wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 :: wd x6 ::
        wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 9577 (wd (zf (zR W)) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)) 46 := by
  opt65_reach [4058, 4059, 4060, 4061, 4062, 4063, 4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072] with [zR_eq, zsub, zv_mod, zf_eq, Nat.or_zero]

theorem z_g3 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 64 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9577 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 9658 (wd (zf (zR (W / 1048576)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 ::
        wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 1048576))) 32) (32 + gp)))
        56 := by
  opt65_reach [4073, 4074, 4075, 4076, 4077, 4078, 4079, 4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g4 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 96 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9658 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest) M)
      (callState s 9739 (wd (zf (zR (W / 1099511627776)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 ::
        wd x3 :: wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 1099511627776))) 32) (64 + gp)))
        56 := by
  opt65_reach [4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099, 4100, 4101, 4102, 4103, 4104, 4105, 4106, 4107, 4108] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g5 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {Lf W gp gs V0 V1 V2 V3 dp off acc e : Nat} :
    Reach (callState s 9739 (wd Lf :: wd W :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9752 (wd (96 + gp) :: wd (60 + gs) :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd (acc ||| Lf) :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 31 := by
  opt65_reach [4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119]

theorem z_gnext (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp gs V0 V1 V2 V3 dp off acc e : Nat} (hgs : gs < 240) :
    Reach (callState s 9752 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9436 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M) 22 := by
  opt65_reach [4120, 4121, 4122, 4123, 4124]

theorem z_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hle : dp + 384 ≤ e) (he : e < 2 ^ 64) :
    Reach (callState s 9752 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9044 (wd (384 + dp) :: wd (30 + off) :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
        111 := by
  opt65_reach [4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4156, 4157, 4158]

theorem z_clamp (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hne : dp ≠ e) (hgt : e < dp + 384) (he : dp < 2 ^ 64)
    (hoff : off < 2 ^ 64) :
    Reach (callState s 9752 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e :: wd ret :: tail) M)
      (callState s 9044 (wd (384 + dp - 256) :: wd (30 + off - 20) :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd e ::
        wd ret :: tail) M) 135 := by
  opt65_reach [4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4155, 4156, 4157, 4158]

theorem z_exit (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc : Nat} :
    Reach (callState s 9752 (wd gp :: wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 6582011952183088782295924477334101861609978183833731334774194175 :: wd dp :: wd ret :: tail) M)
      (callState s ret (wd acc :: tail) M) 82 := by
  have := hr.small
  opt65_reach [4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167] with [hr.jumpdest]

end

end MlDsaOpt65.Proofs.DecodeZ
