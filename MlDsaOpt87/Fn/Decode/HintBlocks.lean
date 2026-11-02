import MlDsaOpt87.Fn.Decode.Defs
import MlDsaOpt44.Fn.Decode.HintBlocks
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dhint` (ML-DSA-87, WP G2)

Generated from `MlDsaOpt44/Fn/Decode/HintBlocks.lean` (row 0 template instantiated for
the 8 unrolled rows, the trailing scan, entry and exit) with the ML-DSA-87
constants: hint bytes at `H0 = 7136`, counts at `H0 + ω + r` (`ω = 75`), row `r` ORs
`2^(64 (r % 4))` into `HP + 0x2000 (r / 4) + 32 y`. Row `r` (`r < 8`): head `pcH r`,
inner loop `pcI r`, next row `pcN r = pcH (r + 1)`; trailing scan at `10143`.
-/

namespace MlDsaOpt87.Proofs.DecodeH

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem h_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 9259 (wd ret :: tail) M) (callState s 9263 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  opt87_reach [3669, 3670, 3671]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7211 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9263 (wd a :: G :: wd ret :: tail) M) (callState s 9290 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3691, 3692] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7211 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9263 (wd a :: G :: wd ret :: tail) M) (callState s 9290 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692] with [word_shr248, hB]
  · opt87_reach [3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692] with [word_shr248, hB]
  · opt87_reach [3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9290 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9361 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [3693, 3694, 3695, 3696, 3697, 3698, 3699, 3740, 3741, 3742, 3743]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9290 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9290 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt87_reach [3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3711, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9290 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9290 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt87_reach [3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9290 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9290 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt87_reach [3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7212 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9361 (wd a :: G :: wd ret :: tail) M) (callState s 9388 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752, 3753, 3754, 3755, 3756, 3757, 3763, 3764] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7212 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9361 (wd a :: G :: wd ret :: tail) M) (callState s 9388 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752, 3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764] with [word_shr248, hB]
  · opt87_reach [3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752, 3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764] with [word_shr248, hB]
  · opt87_reach [3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752, 3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9388 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9467 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [3765, 3766, 3767, 3768, 3769, 3770, 3771, 3812, 3813, 3814, 3815]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9388 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9388 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt87_reach [3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9388 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9388 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt87_reach [3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3784, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9388 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9388 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt87_reach [3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3784, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794, 3795, 3796, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7213 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9467 (wd a :: G :: wd ret :: tail) M) (callState s 9494 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3835, 3836] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7213 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9467 (wd a :: G :: wd ret :: tail) M) (callState s 9494 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836] with [word_shr248, hB]
  · opt87_reach [3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836] with [word_shr248, hB]
  · opt87_reach [3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9494 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9581 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [3837, 3838, 3839, 3840, 3841, 3842, 3843, 3884, 3885, 3886, 3887]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9494 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9494 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt87_reach [3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9494 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9494 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt87_reach [3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9494 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9494 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt87_reach [3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7214 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9581 (wd a :: G :: wd ret :: tail) M) (callState s 9608 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3907, 3908] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7214 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9581 (wd a :: G :: wd ret :: tail) M) (callState s 9608 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908] with [word_shr248, hB]
  · opt87_reach [3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908] with [word_shr248, hB]
  · opt87_reach [3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9608 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9703 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [3909, 3910, 3911, 3912, 3913, 3914, 3915, 3956, 3957, 3958, 3959]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9608 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9608 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt87_reach [3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3941, 3942, 3943, 3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9608 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9608 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt87_reach [3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3941, 3942, 3943, 3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9608 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9608 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt87_reach [3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943, 3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955] with [word_shr248, hY, hP, or_word_mod]

theorem h4_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7215 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9703 (wd a :: G :: wd ret :: tail) M) (callState s 9730 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973, 3979, 3980] with [word_shr248, hB]

theorem h4_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7215 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9703 (wd a :: G :: wd ret :: tail) M) (callState s 9730 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980] with [word_shr248, hB]
  · opt87_reach [3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980] with [word_shr248, hB]
  · opt87_reach [3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980] with [word_shr248, hB]
  · omega

theorem h4_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9730 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9801 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [3981, 3982, 3983, 3984, 3985, 3986, 3987, 4028, 4029, 4030, 4031]

theorem h4_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9730 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9730 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt87_reach [3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027] with [word_shr248, hY, or_word_mod]

theorem h4_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9730 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9730 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt87_reach [3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027] with [word_shr248, hY, hP, or_word_mod]

theorem h4_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9730 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9730 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt87_reach [3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027] with [word_shr248, hY, hP, or_word_mod]

theorem h5_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7216 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9801 (wd a :: G :: wd ret :: tail) M) (callState s 9828 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4051, 4052] with [word_shr248, hB]

theorem h5_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7216 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9801 (wd a :: G :: wd ret :: tail) M) (callState s 9828 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052] with [word_shr248, hB]
  · opt87_reach [4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052] with [word_shr248, hB]
  · opt87_reach [4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052] with [word_shr248, hB]
  · omega

theorem h5_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9828 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9907 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [4053, 4054, 4055, 4056, 4057, 4058, 4059, 4100, 4101, 4102, 4103]

theorem h5_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9828 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9828 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt87_reach [4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063, 4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099] with [word_shr248, hY, or_word_mod]

theorem h5_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9828 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9828 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt87_reach [4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063, 4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079, 4080, 4081, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099] with [word_shr248, hY, hP, or_word_mod]

theorem h5_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9828 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9828 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt87_reach [4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063, 4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079, 4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099] with [word_shr248, hY, hP, or_word_mod]

theorem h6_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7217 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 9907 (wd a :: G :: wd ret :: tail) M) (callState s 9934 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4123, 4124] with [word_shr248, hB]

theorem h6_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7217 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 9907 (wd a :: G :: wd ret :: tail) M) (callState s 9934 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124] with [word_shr248, hB]
  · opt87_reach [4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124] with [word_shr248, hB]
  · opt87_reach [4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124] with [word_shr248, hB]
  · omega

theorem h6_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 9934 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 10021 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [4125, 4126, 4127, 4128, 4129, 4130, 4131, 4172, 4173, 4174, 4175]

theorem h6_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9934 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9934 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt87_reach [4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4157, 4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169, 4170, 4171] with [word_shr248, hY, or_word_mod]

theorem h6_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9934 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9934 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt87_reach [4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4157, 4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169, 4170, 4171] with [word_shr248, hY, hP, or_word_mod]

theorem h6_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 9934 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9934 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt87_reach [4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4155, 4156, 4157, 4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169, 4170, 4171] with [word_shr248, hY, hP, or_word_mod]

theorem h7_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7218 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 10021 (wd a :: G :: wd ret :: tail) M) (callState s 10048 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt87_reach [4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4195, 4196] with [word_shr248, hB]

theorem h7_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7218 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 10021 (wd a :: G :: wd ret :: tail) M) (callState s 10048 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · opt87_reach [4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196] with [word_shr248, hB]
  · opt87_reach [4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196] with [word_shr248, hB]
  · opt87_reach [4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196] with [word_shr248, hB]
  · omega

theorem h7_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 10048 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 10143 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt87_reach [4197, 4198, 4199, 4200, 4201, 4202, 4203, 4244, 4245, 4246, 4247]

theorem h7_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10048 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 10048 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt87_reach [4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4229, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243] with [word_shr248, hY, or_word_mod]

theorem h7_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10048 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 10048 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt87_reach [4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223, 4224, 4225, 4229, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243] with [word_shr248, hY, hP, or_word_mod]

theorem h7_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 10048 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 10048 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt87_reach [4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223, 4224, 4225, 4226, 4227, 4228, 4229, 4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 10143 (wd 75 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  opt87_reach [4248, 4249, 4250, 4251, 4252, 4253, 4254, 4272, 4273, 4274, 4275] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = 0) :
    Reach (callState s 10143 (wd idx :: G :: wd ret :: tail) M)
      (callState s 10143 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  opt87_reach [4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263, 4267, 4268, 4269, 4270, 4271] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 10143 (wd idx :: G :: wd ret :: tail) M)
      (callState s 10143 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  opt87_reach [4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263, 4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271] with [word_shr248, hY]

end

end MlDsaOpt87.Proofs.DecodeH
