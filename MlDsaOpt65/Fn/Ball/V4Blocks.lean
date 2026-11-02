import MlDsaOpt65.Layout
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
/-!
# `sib` (v4, ML-DSA-65): straight-line blocks

Generated from `MlDsaOpt44/Fn/Ball/V4Blocks.lean` (indices, pcs and costs from
`MlDsaOpt65/listing.tsv`). Loop head `sibloop` (pc 7888), stack
`o :: i :: signs :: ret :: tail` (`o = 32 x` for stream lane `x`). Byte `r` of
the lane is tested at `skipPc r` (`r ≥ 1`) with `z :: w :: o :: …` (`w` the
lane word, `z` the previous byte or return label). An accepted byte calls the
shared accept step (`A`, `B` when `j` holds a nonzero coefficient, then `C`
back to the return label or `D` when all `τ` are placed). Both stream blocks
are in `CB` (34 lanes); at `o = 0x440` the routine fails (returns `0`).
-/

namespace MlDsaOpt65.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

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
def skipPc (r : Nat) : Nat := 7924 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 7888 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 8102 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

theorem b_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 7878 (wd ret :: tail) M) (headSt s ret tail 32 207 (word M 88064) M) 13 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3053, 3054, 3055, 3056, 3057]

theorem b_head_rej {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o ≤ 1088) (hne : o ≠ 1088) (hw : word M (88064 + o) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) 66 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075] with [hw, hj, skipPc]

theorem b_head_acc {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o ≤ 1088) (hne : o ≠ 1088) (hw : word M (88064 + o) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (accSt s ret tail j 7924 w o i sg M) 83 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079] with [hw, hj]

theorem b_skip_rej1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (skipSt s ret tail 2 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091] with [hj, skipPc]

theorem b_skip_acc1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (accSt s ret tail j 7948 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095] with [hj, skipPc]

theorem b_skip_rej2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (skipSt s ret tail 3 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107] with [hj, skipPc]

theorem b_skip_acc2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (accSt s ret tail j 7972 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111] with [hj, skipPc]

theorem b_skip_rej3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (skipSt s ret tail 4 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123] with [hj, skipPc]

theorem b_skip_acc3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (accSt s ret tail j 7996 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127] with [hj, skipPc]

theorem b_skip_rej4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (skipSt s ret tail 5 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139] with [hj, skipPc]

theorem b_skip_acc4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (accSt s ret tail j 8020 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143] with [hj, skipPc]

theorem b_skip_rej5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (skipSt s ret tail 6 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155] with [hj, skipPc]

theorem b_skip_acc5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (accSt s ret tail j 8044 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159] with [hj, skipPc]

theorem b_skip_rej6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (skipSt s ret tail 7 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171] with [hj, skipPc]

theorem b_skip_acc6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (accSt s ret tail j 8068 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175] with [hj, skipPc]

theorem b_skip_rej7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 62 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3192, 3193, 3194, 3195, 3196, 3197, 3198] with [hj, skipPc]

theorem b_skip_acc7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (accSt s ret tail j 8092 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191] with [hj, skipPc]

theorem b_tail8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg : Nat) :
    Reach (skipSt s ret tail 8 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3192, 3193, 3194, 3195, 3196, 3197, 3198] with [skipPc]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem b_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (51200 + j) = 0) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 8236 (wd 0 :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

theorem b_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 8210 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

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

theorem b_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (49120 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 8210 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 8236 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260] with [hbv]

theorem b_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255)
    (hrl : Decode.isValidJumpDest MlDsaOpt65.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    Reach (callState s 8236 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (signs / 2) :: wd ret :: tail) (memC M j sg cnt)) 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have h1 : 1 + i = i + 1 := by omega
  opt65_reach [3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305] with [hcnt, h1, hrl]

theorem b_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (rl w o i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8236 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 157 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314] with [hcnt, hjd]

theorem b_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) 43 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt65_reach [3058, 3059, 3060, 3061, 3062, 3063, 3315, 3316, 3317, 3318, 3319, 3320, 3321] with [hjd]

end MlDsaOpt65.Proofs.Ball4
