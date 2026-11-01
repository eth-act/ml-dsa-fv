import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# `sib` (ML-DSA-87): straight-line blocks of the scan

Loop head `sibloop` at instruction 3285 (pc 8664), stack `p :: i :: signs :: ret :: tail`.
A visit with `p ∉ {136, 272}` jumps to `sibnok` (pc 8755, `sib_nok`); `p = 136` refills
the `KS` block first (`Fn/Ball/Refill.lean`); `p = 272` fails (`sib_fail`). From `sibnok`
the byte `p mod 136` of the block in `KS` is read; a rejected byte goes back to the head
(`sib_reject`), an accepted one runs `A` (to the `IDX[j]` test), `B` when `j` holds a
nonzero coefficient, then `C` (back to the head) or `D` (all `τ` placed: return `1`).
The `A`–`D` blocks are the ML-DSA-44 ones (`MlDsaOpt44/Fn/Ball/Blocks.lean`) with the
ML-DSA-87 `BASES`/`IDX` addresses.
-/

namespace MlDsaOpt87.Proofs.Ball

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

theorem land_seven (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

theorem seven_land (x : Nat) : 7 &&& x = x % 8 := by rw [Nat.and_comm]; exact land_seven x

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, beNat m a w < 256 ^ w
  | 0 => by simp [beNat]
  | w + 1 => by
    have := beNat_lt m a w; have := byteAt_lt m (a + w)
    simp only [beNat, Nat.pow_succ]; omega

theorem beNat_head (m : ByteArray) (a : Nat) : ∀ w,
    beNat m a (w + 1) = byteAt m a * 256 ^ w + beNat m (a + 1) w
  | 0 => by simp [beNat]
  | w + 1 => by
    rw [beNat, beNat_head m a w, beNat, Nat.pow_succ, show a + 1 + w = a + (w + 1) by omega]
    ring

theorem word_div_248 (m : ByteArray) (a : Nat) :
    word m a / 452312848583266388373324160190187140051835877600158453279131187530910662656 =
      byteAt m a := by
  rw [word_eq_beNat, beNat_head m a 31]
  have := beNat_lt m (a + 1) 31
  rw [show (452312848583266388373324160190187140051835877600158453279131187530910662656 : Nat) =
    256 ^ 31 by norm_num, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt this, Nat.zero_add]

theorem word_mstore8_disjoint (m : ByteArray) (b : UInt8) {a x : Nat} (h : a < x ∨ x + 32 ≤ a) :
    word (MachineState.writeBytes m (ByteArray.mk #[b]) a) x = word m x :=
  word_writeBytes_disjoint m _ (by
    have : (ByteArray.mk #[b]).size = 1 := rfl
    rw [this]; omega)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (p i sg : Nat) (M : ByteArray) :
    State :=
  callState s 8664 (wd p :: wd i :: wd sg :: wd ret :: tail) M

/-- `sibnok`: the byte read of a visit. -/
abbrev nokSt (s : State) (ret : Nat) (tail : List UInt256) (p i sg : Nat) (M : ByteArray) :
    State :=
  callState s 8755 (wd p :: wd i :: wd sg :: wd ret :: tail) M

theorem sib_nok {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray)
    (p i sg : Nat) (hp : p < 272) (hp' : p ≠ 136) :
    Reach (headSt s ret tail p i sg M) (nokSt s ret tail p i sg M) 48 := by
  opt87_reach [3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296]

theorem sib_reject {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i sg : Nat) (hp : p < 272)
    (j : Nat) (hj : 255 &&& word M (p % 136 / 8 * 32) / 2 ^ (p % 136 % 8 * 8) = j)
    (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail p i sg M) (headSt s ret tail (p + 1) i sg M) 110 := by
  have h1 : 1 + p = p + 1 := by omega
  have hpw : p < 2 ^ 256 := by omega
  have hrw : (136 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 136 := by norm_num
  opt87_reach [3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3477, 3478, 3479, 3480] with [ofNat_mod_ofNat, Nat.zero_add, land_seven, seven_land, hj, h1]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem sib_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (p % 136 / 8 * 32) / 2 ^ (p % 136 % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (51200 + j) = 0) :
    Reach (nokSt s ret tail p i signs M)
      (callState s 8879 (wd 0 :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 226 := by
  have h1 : 1 + p = p + 1 := by omega
  have hpw : p < 2 ^ 256 := by omega
  have hrw : (136 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 136 := by norm_num
  opt87_reach [3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411] with [ofNat_mod_ofNat, Nat.zero_add, land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

theorem sib_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (p % 136 / 8 * 32) / 2 ^ (p % 136 % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (nokSt s ret tail p i signs M)
      (callState s 8853 (wd k :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 226 := by
  have h1 : 1 + p = p + 1 := by omega
  have hpw : p < 2 ^ 256 := by omega
  have hrw : (136 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 136 := by norm_num
  opt87_reach [3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411] with [ofNat_mod_ofNat, Nat.zero_add, land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

/-- Memory after `BASES[k-1] += 8 (i - j); IDX[i] := k`. -/
abbrev memB (M : ByteArray) (i j k bv : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes M (Data.Bytes.natToBytesPadded ((i - j) * 8 + bv) 32) (49120 + k * 32))
    (ByteArray.mk #[UInt8.ofNat k]) (51200 + i)

/-- Memory after `IDX[j] := cnt + 1; CNT := cnt + 1; BASES[cnt] := 4064 + 8 j - 2048 sg`. -/
abbrev memC (M : ByteArray) (j sg cnt : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes (MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat (1 + cnt)]) (51200 + j))
      (Data.Bytes.natToBytesPadded (1 + cnt) 32) 4032)
    (Data.Bytes.natToBytesPadded (4064 + j * 8 - sg * 2048) 32) (49120 + (1 + cnt) * 32)

theorem sib_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (49120 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 8853 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 8879 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  opt87_reach [3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431] with [hbv]

theorem sib_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8879 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (headSt s ret tail p1 (i + 1) (signs / 2) (memC M j sg cnt)) 143 := by
  have h1 : 1 + i = i + 1 := by omega
  opt87_reach [3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476] with [hcnt, h1]

theorem sib_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (p1 i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8879 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 153 := by
  opt87_reach [3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3481, 3482, 3483, 3484, 3485, 3486, 3487] with [hcnt, hjd]

theorem sib_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i signs : Nat) :
    Reach (headSt s ret tail 272 i signs M) (callState s ret (wd 0 :: tail) M) 43 := by
  opt87_reach [3285, 3286, 3287, 3288, 3289, 3290, 3488, 3489, 3490, 3491, 3492, 3493, 3494] with [hjd]

end MlDsaOpt87.Proofs.Ball
