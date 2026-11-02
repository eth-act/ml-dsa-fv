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
inner loop `pcI r`, next row `pcN r = pcH (r + 1)`; trailing scan at `8966`.
-/

namespace MlDsaOpt65.Proofs.DecodeH

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeH

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem h_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 8318 (wd ret :: tail) M) (callState s 8322 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  opt65_reach [3322, 3323, 3324]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5255 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8322 (wd a :: G :: wd ret :: tail) M) (callState s 8349 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3344, 3345] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5255 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8322 (wd a :: G :: wd ret :: tail) M) (callState s 8349 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345] with [word_shr248, hB]
  · opt65_reach [3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345] with [word_shr248, hB]
  · opt65_reach [3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8349 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8420 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3346, 3347, 3348, 3349, 3350, 3351, 3352, 3393, 3394, 3395, 3396]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8349 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8349 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8349 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8349 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8349 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8349 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5256 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8420 (wd a :: G :: wd ret :: tail) M) (callState s 8447 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3416, 3417] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5256 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8420 (wd a :: G :: wd ret :: tail) M) (callState s 8447 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417] with [word_shr248, hB]
  · opt65_reach [3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417] with [word_shr248, hB]
  · opt65_reach [3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8447 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8526 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3418, 3419, 3420, 3421, 3422, 3423, 3424, 3465, 3466, 3467, 3468]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8447 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8447 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8447 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8447 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8447 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8447 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5257 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8526 (wd a :: G :: wd ret :: tail) M) (callState s 8553 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3488, 3489] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5257 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8526 (wd a :: G :: wd ret :: tail) M) (callState s 8553 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489] with [word_shr248, hB]
  · opt65_reach [3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489] with [word_shr248, hB]
  · opt65_reach [3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8553 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8640 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3490, 3491, 3492, 3493, 3494, 3495, 3496, 3537, 3538, 3539, 3540]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8553 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8553 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8553 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8553 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8553 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8553 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5258 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8640 (wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3560, 3561] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5258 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8640 (wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561] with [word_shr248, hB]
  · opt65_reach [3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561] with [word_shr248, hB]
  · opt65_reach [3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8667 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8762 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3562, 3563, 3564, 3565, 3566, 3567, 3568, 3609, 3610, 3611, 3612]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  opt65_reach [3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  opt65_reach [3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  opt65_reach [3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hY, hP, or_word_mod]

theorem h4_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5259 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8762 (wd a :: G :: wd ret :: tail) M) (callState s 8789 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3632, 3633] with [word_shr248, hB]

theorem h4_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5259 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8762 (wd a :: G :: wd ret :: tail) M) (callState s 8789 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633] with [word_shr248, hB]
  · opt65_reach [3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633] with [word_shr248, hB]
  · opt65_reach [3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633] with [word_shr248, hB]
  · omega

theorem h4_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8789 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8860 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3634, 3635, 3636, 3637, 3638, 3639, 3640, 3681, 3682, 3683, 3684]

theorem h4_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8789 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8789 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt65_reach [3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hY, or_word_mod]

theorem h4_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8789 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8789 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt65_reach [3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hY, hP, or_word_mod]

theorem h4_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8789 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8789 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt65_reach [3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hY, hP, or_word_mod]

theorem h5_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 5260 = B) (hab : a ≤ B) (hB80 : B ≤ 55) :
    Reach (callState s 8860 (wd a :: G :: wd ret :: tail) M) (callState s 8887 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt65_reach [3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3704, 3705] with [word_shr248, hB]

theorem h5_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 55)
    (hB : byteAt s.executionEnv.calldata 5260 = B) (hB256 : B < 256) (hbad : B < a ∨ 55 < B) :
    Reach (callState s 8860 (wd a :: G :: wd ret :: tail) M) (callState s 8887 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 55 < B
  · opt65_reach [3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705] with [word_shr248, hB]
  · opt65_reach [3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705] with [word_shr248, hB]
  · opt65_reach [3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705] with [word_shr248, hB]
  · omega

theorem h5_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 55) :
    Reach (callState s 8887 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8966 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt65_reach [3706, 3707, 3708, 3709, 3710, 3711, 3712, 3753, 3754, 3755, 3756]

theorem h5_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8887 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8887 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  opt65_reach [3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hY, or_word_mod]

theorem h5_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8887 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8887 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  opt65_reach [3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hY, hP, or_word_mod]

theorem h5_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (5199 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8887 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8887 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  opt65_reach [3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 8966 (wd 55 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  opt65_reach [3757, 3758, 3759, 3760, 3761, 3762, 3763, 3781, 3782, 3783, 3784] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = 0) :
    Reach (callState s 8966 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8966 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  opt65_reach [3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3776, 3777, 3778, 3779, 3780] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 55)
    (hY : byteAt s.executionEnv.calldata (5200 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 8966 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8966 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  opt65_reach [3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780] with [word_shr248, hY]

end

end MlDsaOpt65.Proofs.DecodeH
