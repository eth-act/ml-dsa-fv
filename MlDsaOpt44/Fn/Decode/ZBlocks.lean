import MlDsaOpt44.Fn.Decode.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dz` (WP8)

Loop heads: `8048` (chunk loop, stack `dp, off, acc, MB, end`), `8440`
(gather loop, `gp, gs, V3, V2, V1, V0, dp, off, acc, MB, end`). Every block is
stated for abstract stack values; the window values `V_k` enter as
`leNat cd a 32` (`bsw_word`), the gathered word `W` stays abstract inside one
gather step.
-/

namespace MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem z_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 8009 (wd ZH :: wd Z0 :: wd ret :: tail) M)
      (callState s 8048 (wd ZH :: wd Z0 :: wd 0 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd (ZH + 7808) :: wd ret :: tail) M) 27 := by
  simp only [ZH, Z0]
  opt44_reach [3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251]

theorem z_load0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 8048 (wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8229 (wd (leNat s.executionEnv.calldata off 32) :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 172 := by
  opt44_reach [3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3306, 3307, 3308, 3309] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 8229 (wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8296 (wd (leNat s.executionEnv.calldata (576 + off) 32) :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 165 := by
  opt44_reach [3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 8296 (wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8363 (wd (leNat s.executionEnv.calldata (1152 + off) 32) :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 :: wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 165 := by
  opt44_reach [3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_load3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {dp off acc e V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 8363 (wd V2 :: wd V1 :: wd V0 :: wd 6277101735386680763495507056286727952657427581105975853055 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8440 (wd dp :: wd 0 :: wd (leNat s.executionEnv.calldata (1728 + off) 32) :: wd V2 ::
        wd V1 :: wd V0 :: wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 190 := by
  opt44_reach [3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem z_g1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {gp gs V0 V1 V2 V3 dp off acc e : Nat}
    (hgs : gs < 256) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 8440 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd dp :: wd off ::
        wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8501 (wd (gW gs V0 V1 V2 V3) :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 88 := by
  opt44_reach [3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514] with [gW_eq]

theorem z_g2 (hs : Ctx s) (M : ByteArray) {W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 32 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8501 (wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 :: wd x6 ::
        wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest) M)
      (callState s 8601 (wd (zf (zR W)) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)) 56 := by
  opt44_reach [3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533] with [zR_eq, zsub, zv_mod, zf_eq, Nat.or_zero]

theorem z_g3 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 64 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8601 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest) M)
      (callState s 8706 (wd (zf (zR (W / 262144)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 ::
        wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 262144))) 32) (32 + gp)))
        66 := by
  opt44_reach [3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g4 (hs : Ctx s) (M : ByteArray) {Lf W gp x1 x2 x3 x4 x5 x6 x7 x8 : Nat}
    {rest : List UInt256} (hrest : rest.length ≤ 962) (hW : W < 2 ^ 256)
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : gp + 96 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8706 (wd Lf :: wd W :: wd gp :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd x5 ::
        wd x6 :: wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest) M)
      (callState s 8811 (wd (zf (zR (W / 68719476736)) ||| Lf) :: wd W :: wd gp :: wd x1 :: wd x2 ::
        wd x3 :: wd x4 :: wd x5 :: wd x6 :: wd x7 :: wd x8 :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR (W / 68719476736))) 32) (64 + gp)))
        66 := by
  opt44_reach [3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577] with [zR_eq, zsub, zv_mod, zf_eq]

theorem z_g5 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {Lf W gp gs V0 V1 V2 V3 dp off acc e : Nat} :
    Reach (callState s 8811 (wd Lf :: wd W :: wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8824 (wd (96 + gp) :: wd (54 + gs) :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd (acc ||| Lf) :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 31 := by
  opt44_reach [3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588]

theorem z_gnext (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp gs V0 V1 V2 V3 dp off acc e : Nat} (hgs : gs < 216) :
    Reach (callState s 8824 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8440 (wd gp :: wd gs :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M) 22 := by
  opt44_reach [3589, 3590, 3591, 3592, 3593]

theorem z_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hle : dp + 384 ≤ e) (he : e < 2 ^ 64) :
    Reach (callState s 8824 (wd gp :: wd 216 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8048 (wd (384 + dp) :: wd (27 + off) :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
        111 := by
  opt44_reach [3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3625, 3626, 3627]

theorem z_clamp (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc e : Nat} (hne : dp ≠ e) (hgt : e < dp + 384) (he : dp < 2 ^ 64)
    (hoff : off < 2 ^ 64) :
    Reach (callState s 8824 (wd gp :: wd 216 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e :: wd ret :: tail) M)
      (callState s 8048 (wd (384 + dp - 256) :: wd (27 + off - 18) :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd e ::
        wd ret :: tail) M) 135 := by
  opt44_reach [3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627]

theorem z_exit (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    {gp V0 V1 V2 V3 dp off acc : Nat} :
    Reach (callState s 8824 (wd gp :: wd 216 :: wd V3 :: wd V2 :: wd V1 :: wd V0 ::
        wd dp :: wd off :: wd acc :: wd 1645498280219470655563407987279682868948834857825835856559341567 :: wd dp :: wd ret :: tail) M)
      (callState s ret (wd acc :: tail) M) 82 := by
  have := hr.small
  opt44_reach [3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636] with [hr.jumpdest]

end

end MlDsaOpt44.Proofs.DecodeZ
