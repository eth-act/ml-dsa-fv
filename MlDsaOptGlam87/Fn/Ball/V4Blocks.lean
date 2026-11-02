import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Ball/V4Blocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# `sib` (v4, ML-DSA-87): straight-line blocks of the scan

Generated (`MlDsaOpt44/Fn/Ball/V4Blocks.lean` with the ML-DSA-87 pcs, indices,
`IDX`/`BASES` and the `kf1` head). Loop head `sibloop` (pc 7682), stack
`o :: i :: signs :: ret :: tail` (`o = 32 x` for stream lane `x`): `o = 1088` fails
(`b_fail`), `o = 544` squeezes the second block (`Fn/Ball/V4Prologue.lean`), otherwise
`b_nok` goes to `sibnok` (pc 7775), which loads the lane word `KS[o mod 544]` and tests
byte 0. Byte `r ≥ 1` of the lane is tested at `skipPc r` with `z :: w :: o :: …`
(`w` the lane word, `z` the previous byte or return label). An accepted byte calls the
shared accept step (`A`, `B` when `j` holds a nonzero coefficient, then `C` back to the
return label or `D` when all `τ` are placed).
-/

namespace MlDsaOptGlam87.Proofs.Ball4

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

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
def skipPc (r : Nat) : Nat := 7802 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 7682 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- `sibnok`: the lane load and the test of byte 0. -/
abbrev nokSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 7775 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 7980 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

theorem b_nok {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (o i sg : Nat) (ho : o < 1088) (ho' : o ≠ 544) :
    Reach (headSt s ret tail o i sg M) (nokSt s ret tail o i sg M) 48 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]

theorem b_nok_rej {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) 49 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  glam87_rreach [3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194] with [ofNat_mod_ofNat, hw, hj, skipPc]

theorem b_nok_acc {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o < 1088) (hw : word M (o % 544) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (nokSt s ret tail o i sg M) (accSt s ret tail j 7802 w o i sg M) 66 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hpw : o < 2 ^ 256 := by omega
  have hrw : (544 : Nat) < 2 ^ 256 := by norm_num
  have h0 : (0 : Nat) < 544 := by norm_num
  glam87_rreach [3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198] with [ofNat_mod_ofNat, hw, hj]

theorem b_skip_rej1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (skipSt s ret tail 2 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210] with [hj, skipPc]

theorem b_skip_acc1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (accSt s ret tail j 7826 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214] with [hj, skipPc]

theorem b_skip_rej2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (skipSt s ret tail 3 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226] with [hj, skipPc]

theorem b_skip_acc2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (accSt s ret tail j 7850 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230] with [hj, skipPc]

theorem b_skip_rej3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (skipSt s ret tail 4 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242] with [hj, skipPc]

theorem b_skip_acc3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (accSt s ret tail j 7874 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246] with [hj, skipPc]

theorem b_skip_rej4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (skipSt s ret tail 5 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258] with [hj, skipPc]

theorem b_skip_acc4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (accSt s ret tail j 7898 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262] with [hj, skipPc]

theorem b_skip_rej5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (skipSt s ret tail 6 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274] with [hj, skipPc]

theorem b_skip_acc5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (accSt s ret tail j 7922 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278] with [hj, skipPc]

theorem b_skip_rej6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (skipSt s ret tail 7 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290] with [hj, skipPc]

theorem b_skip_acc6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (accSt s ret tail j 7946 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294] with [hj, skipPc]

theorem b_skip_rej7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 62 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3306, 3311, 3312, 3313, 3314, 3315, 3316, 3317] with [hj, skipPc]

theorem b_skip_acc7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (accSt s ret tail j 7970 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3306, 3307, 3308, 3309, 3310] with [hj, skipPc]

theorem b_tail8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg : Nat) :
    Reach (skipSt s ret tail 8 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3311, 3312, 3313, 3314, 3315, 3316, 3317] with [skipPc]

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
      (callState s 8114 (wd 0 :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

theorem b_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 8088 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

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
    Reach (callState s 8088 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 8114 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379] with [hbv]

theorem b_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255)
    (hrl : Decode.isValidJumpDest MlDsaOptGlam87.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    Reach (callState s 8114 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (signs / 2) :: wd ret :: tail) (memC M j sg cnt)) 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have h1 : 1 + i = i + 1 := by omega
  glam87_rreach [3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424] with [hcnt, h1, hrl]

theorem b_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (rl w o i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8114 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 157 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433] with [hcnt, hjd]

/-- The fail exit (`o = 1088`): return `0`. -/
theorem b_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) 43 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam87_rreach [3124, 3125, 3126, 3127, 3128, 3129, 3434, 3435, 3436, 3437, 3438, 3439, 3440] with [hjd]

end MlDsaOptGlam87.Proofs.Ball4
