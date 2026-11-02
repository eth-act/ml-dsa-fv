import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# `sib` (v4, ML-DSA-87): straight-line blocks of the scan

Generated (`MlDsaOpt44/Fn/Ball/V4Blocks.lean` with the ML-DSA-87 pcs, indices,
`IDX`/`BASES` and the `kf1` head). Loop head `sibloop` (pc 8745), stack
`o :: i :: signs :: ret :: tail` (`o = 32 x` for stream lane `x`): `o = 1088` fails
(`b_fail`), `o = 544` squeezes the second block (`Fn/Ball/V4Prologue.lean`), otherwise
`b_nok` goes to `sibnok` (pc 8838), which loads the lane word `KS[o mod 544]` and tests
byte 0. Byte `r ≥ 1` of the lane is tested at `skipPc r` with `z :: w :: o :: …`
(`w` the lane word, `z` the previous byte or return label). An accepted byte calls the
shared accept step (`A`, `B` when `j` holds a nonzero coefficient, then `C` back to the
return label or `D` when all `τ` are placed).
-/

namespace MlDsaOpt87.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

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

/-- Pc of the test of byte `r` (`1 ≤ r ≤ 7`; `r = 8`: the lane epilogue). -/
def skipPc (r : Nat) : Nat := 8865 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 8745 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- `sibnok`: the lane load and the test of byte 0. -/
abbrev nokSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 8838 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 9043 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

theorem b_nok {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (o i sg : Nat) (ho : o < 1088) (ho' : o ≠ 544) :
    Reach (headSt s ret tail o i sg M) (nokSt s ret tail o i sg M) 48 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363]

theorem b_nok_rej {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) 49 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  opt87_reach [3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422] with [ofNat_mod_ofNat, hw, hj, skipPc]

theorem b_nok_acc {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (accSt s ret tail j 8865 w o i sg M) 66 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  opt87_reach [3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426] with [ofNat_mod_ofNat, hw, hj]

theorem b_skip_rej1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (skipSt s ret tail 2 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438] with [hj, skipPc]

theorem b_skip_acc1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (accSt s ret tail j 8889 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442] with [hj, skipPc]

theorem b_skip_rej2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (skipSt s ret tail 3 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454] with [hj, skipPc]

theorem b_skip_acc2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (accSt s ret tail j 8913 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458] with [hj, skipPc]

theorem b_skip_rej3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (skipSt s ret tail 4 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470] with [hj, skipPc]

theorem b_skip_acc3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (accSt s ret tail j 8937 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474] with [hj, skipPc]

theorem b_skip_rej4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (skipSt s ret tail 5 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486] with [hj, skipPc]

theorem b_skip_acc4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (accSt s ret tail j 8961 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490] with [hj, skipPc]

theorem b_skip_rej5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (skipSt s ret tail 6 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502] with [hj, skipPc]

theorem b_skip_acc5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (accSt s ret tail j 8985 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506] with [hj, skipPc]

theorem b_skip_rej6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (skipSt s ret tail 7 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518] with [hj, skipPc]

theorem b_skip_acc6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (accSt s ret tail j 9009 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522] with [hj, skipPc]

theorem b_skip_rej7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 62 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3539, 3540, 3541, 3542, 3543, 3544, 3545] with [hj, skipPc]

theorem b_skip_acc7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (accSt s ret tail j 9033 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538] with [hj, skipPc]

theorem b_tail8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg : Nat) :
    Reach (skipSt s ret tail 8 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3539, 3540, 3541, 3542, 3543, 3544, 3545] with [skipPc]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem b_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (51200 + j) = 0) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 9177 (wd 0 :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

theorem b_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 9151 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

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

theorem b_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (49120 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 9151 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 9177 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3588, 3589, 3590, 3591, 3592, 3593, 3594, 3595, 3596, 3597, 3598, 3599, 3600, 3601, 3602, 3603, 3604, 3605, 3606, 3607] with [hbv]

theorem b_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255)
    (hrl : Decode.isValidJumpDest MlDsaOpt87.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    Reach (callState s 9177 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (signs / 2) :: wd ret :: tail) (memC M j sg cnt)) 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have h1 : 1 + i = i + 1 := by omega
  opt87_reach [3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3651, 3652] with [hcnt, h1, hrl]

theorem b_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (rl w o i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 9177 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 157 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3608, 3609, 3610, 3611, 3612, 3613, 3614, 3615, 3616, 3617, 3618, 3619, 3620, 3621, 3622, 3623, 3624, 3625, 3626, 3627, 3628, 3629, 3630, 3631, 3632, 3633, 3634, 3635, 3636, 3637, 3638, 3639, 3640, 3641, 3642, 3643, 3644, 3645, 3646, 3647, 3648, 3649, 3650, 3653, 3654, 3655, 3656, 3657, 3658, 3659, 3660, 3661] with [hcnt, hjd]

/-- The fail exit (`o = 1088`): return `0`. -/
theorem b_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) 43 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt87_reach [3352, 3353, 3354, 3355, 3356, 3357, 3662, 3663, 3664, 3665, 3666, 3667, 3668] with [hjd]

end MlDsaOpt87.Proofs.Ball4
