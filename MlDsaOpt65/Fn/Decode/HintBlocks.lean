import MlDsaOpt65.Fn.Decode.Defs
import MlDsaOpt44.Fn.Decode.HintBlocks
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dhint` (ML-DSA-65, WP G2)

Generated from `MlDsaOpt44/Fn/Decode/HintBlocks.lean` (row 0 template instantiated for
the 6 unrolled rows, the trailing scan, entry and exit) with the ML-DSA-65
constants: hint bytes at `H0 = 5200`, counts at `H0 + ω + r` (`ω = 55`), row `r` ORs
`2^(64 (r % 4))` into `HP + 0x2000 (r / 4) + 32 y`. Row `r` (`r < 6`): head `pcH r`,
inner loop `pcI r`, next row `pcN r = pcH (r + 1)`; trailing scan at `8890`.
-/

namespace MlDsaOpt65.Proofs.DecodeH

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem h_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 8242 (wd ret :: tail) M) (callState s 8246 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  opt65_reach [3209, 3210, 3211]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5255 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8246 (wd a :: G :: wd ret :: tail) M) (callState s 8273 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3231, 3232] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5255 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8246 (wd a :: G :: wd ret :: tail) M) (callState s 8273 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232] with [word_shr248, hB]
  · opt65_reach [3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232] with [word_shr248, hB]
  · opt65_reach [3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8273 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8344 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3233, 3234, 3235, 3236, 3237, 3238, 3239, 3280, 3281, 3282, 3283]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8273 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8273 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8273 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8273 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8273 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8273 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5256 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8344 (wd a :: G :: wd ret :: tail) M) (callState s 8371 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3303, 3304] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5256 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8344 (wd a :: G :: wd ret :: tail) M) (callState s 8371 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304] with [word_shr248, hB]
  · opt65_reach [3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304] with [word_shr248, hB]
  · opt65_reach [3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8371 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8450 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3305, 3306, 3307, 3308, 3309, 3310, 3311, 3352, 3353, 3354, 3355]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8371 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8371 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8371 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8371 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8371 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8371 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5257 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8450 (wd a :: G :: wd ret :: tail) M) (callState s 8477 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3375, 3376] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5257 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8450 (wd a :: G :: wd ret :: tail) M) (callState s 8477 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376] with [word_shr248, hB]
  · opt65_reach [3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376] with [word_shr248, hB]
  · opt65_reach [3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8477 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8564 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3377, 3378, 3379, 3380, 3381, 3382, 3383, 3424, 3425, 3426, 3427]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8477 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8477 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8477 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8477 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8477 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8477 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5258 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8564 (wd a :: G :: wd ret :: tail) M) (callState s 8591 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3447, 3448] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5258 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8564 (wd a :: G :: wd ret :: tail) M) (callState s 8591 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448] with [word_shr248, hB]
  · opt65_reach [3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448] with [word_shr248, hB]
  · opt65_reach [3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8591 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8686 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3449, 3450, 3451, 3452, 3453, 3454, 3455, 3496, 3497, 3498, 3499]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8591 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8591 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8591 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8591 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8591 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8591 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495] with [word_shr248, hY, hP, or_word_mod]

theorem h4_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5259 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8686 (wd a :: G :: wd ret :: tail) M) (callState s 8713 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3519, 3520] with [word_shr248, hB]

theorem h4_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5259 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8686 (wd a :: G :: wd ret :: tail) M) (callState s 8713 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520] with [word_shr248, hB]
  · opt65_reach [3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520] with [word_shr248, hB]
  · opt65_reach [3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520] with [word_shr248, hB]
  · omega

theorem h4_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8713 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8784 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3521, 3522, 3523, 3524, 3525, 3526, 3527, 3568, 3569, 3570, 3571]

theorem h4_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8713 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8713 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt65_reach [3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567] with [word_shr248, hY, or_word_mod]

theorem h4_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8713 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8713 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt65_reach [3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567] with [word_shr248, hY, hP, or_word_mod]

theorem h4_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8713 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8713 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt65_reach [3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567] with [word_shr248, hY, hP, or_word_mod]

theorem h5_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5260 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8784 (wd a :: G :: wd ret :: tail) M) (callState s 8811 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3591, 3592] with [word_shr248, hB]

theorem h5_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5260 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8784 (wd a :: G :: wd ret :: tail) M) (callState s 8811 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592] with [word_shr248, hB]
  · opt65_reach [3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592] with [word_shr248, hB]
  · opt65_reach [3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592] with [word_shr248, hB]
  · omega

theorem h5_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8811 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8890 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3593, 3594, 3595, 3596, 3597, 3598, 3599, 3640, 3641, 3642, 3643]

theorem h5_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8811 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8811 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt65_reach [3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639] with [word_shr248, hY, or_word_mod]

theorem h5_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8811 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8811 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt65_reach [3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639] with [word_shr248, hY, hP, or_word_mod]

theorem h5_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8811 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8811 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt65_reach [3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 8890 (wd 55 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  opt65_reach [3644, 3645, 3646, 3647, 3648, 3649, 3650, 3668, 3669, 3670, 3671] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = 0) :
    Reach (callState s 8890 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8890 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  opt65_reach [3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3663, 3664, 3665, 3666, 3667] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 8890 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8890 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  opt65_reach [3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667] with [word_shr248, hY]

end

end MlDsaOpt65.Proofs.DecodeH
