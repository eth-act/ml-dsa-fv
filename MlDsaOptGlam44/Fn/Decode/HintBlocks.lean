import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Decode/HintBlocks.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# Straight-line blocks of `dhint` (WP8)

Row `r` (unrolled, `r < 4`): head at `pcH r` (stack `index, good`), inner loop
head at `pcI r` (stack `idx, bound, first, good`), next row at `pcN r`.
Trailing scan at `7970` (stack `idx, good`). Calldata bytes enter through
`byteAt cd …` equations (`word_shr248`); the bitmap update ORs `2^(64 r)` into
`HP + 32 y`.
-/

namespace MlDsaOptGlam44.Proofs.DecodeH

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

theorem beNat_succ' (m : ByteArray) : ∀ (a w : Nat),
    beNat m a (w + 1) = byteAt m a * 256 ^ w + beNat m (a + 1) w
  | a, 0 => by simp [beNat]
  | a, w + 1 => by
    rw [beNat, beNat_succ' m a w, beNat, show a + (w + 1) = a + 1 + w by omega, pow_succ]
    ring

theorem beNat_lt' (m : ByteArray) (a : Nat) : ∀ w, beNat m a w < 256 ^ w
  | 0 => by simp [beNat]
  | w + 1 => by
    have h1 := beNat_lt' m a w
    have h2 := byteAt_lt m (a + w)
    rw [beNat, pow_succ]
    have h3 : (beNat m a w + 1) * 256 ≤ 256 ^ w * 256 := Nat.mul_le_mul_right _ h1
    omega

/-- `CALLDATALOAD` then `SHR 248` reads one byte. -/
theorem word_shr248 (m : ByteArray) (a : Nat) :
    word m a / 452312848583266388373324160190187140051835877600158453279131187530910662656 =
      byteAt m a := by
  rw [word_eq_beNat, beNat_succ', show (452312848583266388373324160190187140051835877600158453279131187530910662656 : Nat) =
    256 ^ 31 by norm_num, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (beNat_lt' m (a + 1) 31), Nat.zero_add]

theorem or_word_mod {L : Nat} (m : ByteArray) (a : Nat) (hL : L < 2 ^ 256) :
    (L ||| word m a) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      L ||| word m a :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow hL (word_lt m a))

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem h_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 8291 (wd ret :: tail) M) (callState s 8295 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  glam44_rreach [3398, 3399, 3400]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3728 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 8295 (wd a :: G :: wd ret :: tail) M) (callState s 8322 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam44_rreach [3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3420, 3421] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3728 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 8295 (wd a :: G :: wd ret :: tail) M) (callState s 8322 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · glam44_rreach [3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421] with [word_shr248, hB]
  · glam44_rreach [3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421] with [word_shr248, hB]
  · glam44_rreach [3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 8322 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8392 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam44_rreach [3422, 3423, 3424, 3425, 3426, 3427, 3428, 3469, 3470, 3471, 3472]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8322 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8322 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  glam44_rreach [3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8322 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8322 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  glam44_rreach [3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8322 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8322 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  glam44_rreach [3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3729 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 8392 (wd a :: G :: wd ret :: tail) M) (callState s 8419 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam44_rreach [3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3492, 3493] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3729 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 8392 (wd a :: G :: wd ret :: tail) M) (callState s 8419 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · glam44_rreach [3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493] with [word_shr248, hB]
  · glam44_rreach [3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493] with [word_shr248, hB]
  · glam44_rreach [3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 8419 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8497 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam44_rreach [3494, 3495, 3496, 3497, 3498, 3499, 3500, 3541, 3542, 3543, 3544]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8419 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8419 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  glam44_rreach [3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8419 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8419 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  glam44_rreach [3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8419 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8419 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  glam44_rreach [3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3730 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 8497 (wd a :: G :: wd ret :: tail) M) (callState s 8524 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam44_rreach [3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3564, 3565] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3730 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 8497 (wd a :: G :: wd ret :: tail) M) (callState s 8524 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · glam44_rreach [3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565] with [word_shr248, hB]
  · glam44_rreach [3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565] with [word_shr248, hB]
  · glam44_rreach [3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 8524 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8610 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam44_rreach [3566, 3567, 3568, 3569, 3570, 3571, 3572, 3613, 3614, 3615, 3616]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8524 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8524 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  glam44_rreach [3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8524 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8524 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  glam44_rreach [3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592, 3593, 3594, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8524 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8524 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  glam44_rreach [3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608, 3609, 3610, 3611, 3612] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3731 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 8610 (wd a :: G :: wd ret :: tail) M) (callState s 8637 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam44_rreach [3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3636, 3637] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3731 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 8610 (wd a :: G :: wd ret :: tail) M) (callState s 8637 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · glam44_rreach [3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637] with [word_shr248, hB]
  · glam44_rreach [3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637] with [word_shr248, hB]
  · glam44_rreach [3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 8637 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8731 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam44_rreach [3638, 3639, 3640, 3641, 3642, 3643, 3644, 3685, 3686, 3687, 3688]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8637 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8637 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  glam44_rreach [3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8637 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8637 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  glam44_rreach [3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8637 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8637 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  glam44_rreach [3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680, 3681, 3682, 3683, 3684] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 8731 (wd 80 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  glam44_rreach [3689, 3690, 3691, 3692, 3693, 3694, 3695, 3713, 3714, 3715, 3716] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = 0) :
    Reach (callState s 8731 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8731 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  glam44_rreach [3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3708, 3709, 3710, 3711, 3712] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 8731 (wd idx :: G :: wd ret :: tail) M)
      (callState s 8731 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  glam44_rreach [3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3711, 3712] with [word_shr248, hY]

end

end MlDsaOptGlam44.Proofs.DecodeH

