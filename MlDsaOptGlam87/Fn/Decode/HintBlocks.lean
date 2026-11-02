import MlDsaOpt87.Fn.Decode.Defs
import MlDsaOpt44.Fn.Decode.HintBlocks
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Decode/HintBlocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
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
inner loop `pcI r`, next row `pcN r = pcH (r + 1)`; trailing scan at `9080`.
-/

namespace MlDsaOptGlam87.Proofs.DecodeH

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs.DecodeH
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem h_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s 8196 (wd ret :: tail) M) (callState s 8200 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  glam87_rreach [3441, 3442, 3443]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7211 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8200 (wd a :: G :: wd ret :: tail) M) (callState s 8227 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3463, 3464] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7211 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8200 (wd a :: G :: wd ret :: tail) M) (callState s 8227 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hB]
  · glam87_rreach [3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hB]
  · glam87_rreach [3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8227 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8298 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3465, 3466, 3467, 3468, 3469, 3470, 3471, 3512, 3513, 3514, 3515]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8227 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8227 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  glam87_rreach [3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8227 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8227 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  glam87_rreach [3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8227 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8227 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  glam87_rreach [3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7212 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8298 (wd a :: G :: wd ret :: tail) M) (callState s 8325 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3535, 3536] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7212 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8298 (wd a :: G :: wd ret :: tail) M) (callState s 8325 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hB]
  · glam87_rreach [3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hB]
  · glam87_rreach [3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8325 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8404 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3537, 3538, 3539, 3540, 3541, 3542, 3543, 3584, 3585, 3586, 3587]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8325 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8325 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  glam87_rreach [3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8325 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8325 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  glam87_rreach [3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8325 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8325 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  glam87_rreach [3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7213 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8404 (wd a :: G :: wd ret :: tail) M) (callState s 8431 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3607, 3608] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7213 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8404 (wd a :: G :: wd ret :: tail) M) (callState s 8431 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hB]
  · glam87_rreach [3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hB]
  · glam87_rreach [3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607, 3608] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8431 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8518 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3609, 3610, 3611, 3612, 3613, 3614, 3615, 3656, 3657, 3658, 3659]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8431 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8431 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  glam87_rreach [3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8431 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8431 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  glam87_rreach [3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8431 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8431 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  glam87_rreach [3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652, 3653, 3654, 3655] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7214 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8518 (wd a :: G :: wd ret :: tail) M) (callState s 8545 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3679, 3680] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7214 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8518 (wd a :: G :: wd ret :: tail) M) (callState s 8545 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hB]
  · glam87_rreach [3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hB]
  · glam87_rreach [3660, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668, 3669, 3670, 3671, 3672, 3673, 3674, 3675, 3676, 3677, 3678, 3679, 3680] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8545 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8640 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3681, 3682, 3683, 3684, 3685, 3686, 3687, 3728, 3729, 3730, 3731]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8545 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8545 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 117 := by
  glam87_rreach [3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8545 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8545 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 154 := by
  glam87_rreach [3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8545 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8545 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (67840 + Y * 32)) 32) (67840 + Y * 32))) 161 := by
  glam87_rreach [3681, 3682, 3683, 3684, 3685, 3686, 3687, 3688, 3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3697, 3698, 3699, 3700, 3701, 3702, 3703, 3704, 3705, 3706, 3707, 3708, 3709, 3710, 3711, 3712, 3713, 3714, 3715, 3716, 3717, 3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727] with [word_shr248, hY, hP, or_word_mod]

theorem h4_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7215 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8640 (wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3751, 3752] with [word_shr248, hB]

theorem h4_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7215 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8640 (wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hB]
  · glam87_rreach [3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hB]
  · glam87_rreach [3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752] with [word_shr248, hB]
  · omega

theorem h4_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8667 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8738 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3753, 3754, 3755, 3756, 3757, 3758, 3759, 3800, 3801, 3802, 3803]

theorem h4_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  glam87_rreach [3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794, 3795, 3796, 3797, 3798, 3799] with [word_shr248, hY, or_word_mod]

theorem h4_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  glam87_rreach [3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794, 3795, 3796, 3797, 3798, 3799] with [word_shr248, hY, hP, or_word_mod]

theorem h4_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8667 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8667 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  glam87_rreach [3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3784, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794, 3795, 3796, 3797, 3798, 3799] with [word_shr248, hY, hP, or_word_mod]

theorem h5_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7216 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8738 (wd a :: G :: wd ret :: tail) M) (callState s 8765 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3823, 3824] with [word_shr248, hB]

theorem h5_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7216 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8738 (wd a :: G :: wd ret :: tail) M) (callState s 8765 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824] with [word_shr248, hB]
  · glam87_rreach [3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824] with [word_shr248, hB]
  · glam87_rreach [3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824] with [word_shr248, hB]
  · omega

theorem h5_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8765 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8844 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3825, 3826, 3827, 3828, 3829, 3830, 3831, 3872, 3873, 3874, 3875]

theorem h5_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8765 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8765 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  glam87_rreach [3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871] with [word_shr248, hY, or_word_mod]

theorem h5_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8765 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8765 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  glam87_rreach [3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871] with [word_shr248, hY, hP, or_word_mod]

theorem h5_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8765 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8765 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  glam87_rreach [3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871] with [word_shr248, hY, hP, or_word_mod]

theorem h6_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7217 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8844 (wd a :: G :: wd ret :: tail) M) (callState s 8871 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3895, 3896] with [word_shr248, hB]

theorem h6_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7217 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8844 (wd a :: G :: wd ret :: tail) M) (callState s 8871 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896] with [word_shr248, hB]
  · glam87_rreach [3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896] with [word_shr248, hB]
  · glam87_rreach [3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896] with [word_shr248, hB]
  · omega

theorem h6_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8871 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8958 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3897, 3898, 3899, 3900, 3901, 3902, 3903, 3944, 3945, 3946, 3947]

theorem h6_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8871 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8871 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  glam87_rreach [3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911, 3912, 3913, 3914, 3915, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943] with [word_shr248, hY, or_word_mod]

theorem h6_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8871 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8871 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  glam87_rreach [3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943] with [word_shr248, hY, hP, or_word_mod]

theorem h6_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8871 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8871 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  glam87_rreach [3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943] with [word_shr248, hY, hP, or_word_mod]

theorem h7_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 7218 = B) (hab : a ≤ B) (hB80 : B ≤ 75) :
    Reach (callState s 8958 (wd a :: G :: wd ret :: tail) M) (callState s 8985 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  glam87_rreach [3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3967, 3968] with [word_shr248, hB]

theorem h7_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 75)
    (hB : byteAt s.executionEnv.calldata 7218 = B) (hB256 : B < 256) (hbad : B < a ∨ 75 < B) :
    Reach (callState s 8958 (wd a :: G :: wd ret :: tail) M) (callState s 8985 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 75 < B
  · glam87_rreach [3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968] with [word_shr248, hB]
  · glam87_rreach [3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968] with [word_shr248, hB]
  · glam87_rreach [3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968] with [word_shr248, hB]
  · omega

theorem h7_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 75) :
    Reach (callState s 8985 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 9080 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  glam87_rreach [3969, 3970, 3971, 3972, 3973, 3974, 3975, 4016, 4017, 4018, 4019]

theorem h7_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8985 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8985 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 117 := by
  glam87_rreach [3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015] with [word_shr248, hY, or_word_mod]

theorem h7_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8985 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8985 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 154 := by
  glam87_rreach [3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015] with [word_shr248, hY, hP, or_word_mod]

theorem h7_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (7135 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 84224 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 8985 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 8985 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (76032 + Y * 32)) 32) (76032 + Y * 32))) 161 := by
  glam87_rreach [3969, 3970, 3971, 3972, 3973, 3974, 3975, 3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 9080 (wd 75 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  glam87_rreach [4020, 4021, 4022, 4023, 4024, 4025, 4026, 4044, 4045, 4046, 4047] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = 0) :
    Reach (callState s 9080 (wd idx :: G :: wd ret :: tail) M)
      (callState s 9080 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  glam87_rreach [4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027, 4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4039, 4040, 4041, 4042, 4043] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 75)
    (hY : byteAt s.executionEnv.calldata (7136 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 9080 (wd idx :: G :: wd ret :: tail) M)
      (callState s 9080 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  glam87_rreach [4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027, 4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043] with [word_shr248, hY]

end

end MlDsaOptGlam87.Proofs.DecodeH
