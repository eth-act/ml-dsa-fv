import MlDsaOpt87.Fn.Ball.Blocks
import MlDsaOpt44.Main.Mu.Lemmas
import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
/-!
# `sib` (ML-DSA-87): the absorption prologue and the refill

`sib_zero` stores the empty state (lane-complemented, replicated) into `KS`;
`sib_absW0`/`sib_absW1` xor the eight byte-swapped `c̃` lanes of calldata `CTOFF` in
(the `absorb17` lane extraction); `sib_pad` xors the SHAKE256 padding into lanes 8 and 16
and calls `kf1`; `sib_post` un-complements the rate lanes 1, 2, 8, 12 and reads the sign
word `KS[0] mod 2^64`. At `p = 136`, `sib_rpre` re-complements those lanes and calls
`kf1`, `sib_rpost` un-complements them again.
-/

namespace MlDsaOpt87.Proofs.Ball

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

/-- Close the facts of a block whose memory is a chain of `MSTORE`s. -/
macro "sib87_chain" : tactic => `(tactic| (
  simp (disch := first | omega | exact word_lt _ _) only [word_mstore_disjoint, word_mstore]))

/-- The byte-swap masks and `REP` of the absorption. -/
def absK (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd 6277101735386680764176071790128604879584176795969512275969 :: wd 18446744073709551615 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 :: wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd ret :: tail

theorem sib_zero {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = rep (cpl x 0)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8084 (wd ret :: tail) M) (callState s 8207 (wd ret :: tail) M') 218 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt87_reach [2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> sib87_chain
    all_goals (try simp [cpl, complemented])
    all_goals (try norm_num [rep, REP, pack4])
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_absW0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if x < 4 then word M (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (CTOFF + 8 * x))
        else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8207 (wd ret :: tail) M) (callState s 8429 (absK ret tail) M') 255 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · unfold absK
    opt87_reach [3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159] with [MlDsaOpt44.Proofs.WP4.bsw8_fold, MlDsaOpt44.Proofs.WP4.bsw16_fold,
      MlDsaOpt44.Proofs.WP4.bsw32_fold, MlDsaOpt44.Proofs.WP4.bswapNet_fold]
    rfl
  · intro x hx
    by_cases hc : x < 4
    · rw [if_pos hc]
      obtain ⟨hc1, hc2⟩ : 0 ≤ x ∧ x < 4 := by omega
      interval_cases x
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 0) (off := 2592) (b := 2592) 0
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext0 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 1) (off := 2592) (b := 2592) 1
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext1 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 2) (off := 2592) (b := 2592) 2
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext2 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 3) (off := 2592) (b := 2592) 3
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext3 _)
    · rw [if_neg hc]
      interval_cases x <;> first | (exfalso; omega) | (simp only [KS, Nat.reduceMul, Nat.reduceAdd]; sib87_chain)
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_absW1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if 4 ≤ x ∧ x < 8 then
          word M (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (CTOFF + 8 * x))
        else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8429 (absK ret tail) M) (callState s 8531 (wd ret :: tail) M') 252 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · unfold absK
    opt87_reach [3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242] with [MlDsaOpt44.Proofs.WP4.bsw8_fold, MlDsaOpt44.Proofs.WP4.bsw16_fold,
      MlDsaOpt44.Proofs.WP4.bsw32_fold, MlDsaOpt44.Proofs.WP4.bswapNet_fold]
    rfl
  · intro x hx
    by_cases hc : 4 ≤ x ∧ x < 8
    · rw [if_pos hc]
      obtain ⟨hc1, hc2⟩ : 4 ≤ x ∧ x < 8 := by omega
      interval_cases x
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 4) (off := 2592) (b := 2624) 0
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext0 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 5) (off := 2592) (b := 2624) 1
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext1 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 6) (off := 2592) (b := 2624) 2
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext2 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 7) (off := 2592) (b := 2624) 3
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext3 _)
    · rw [if_neg hc]
      interval_cases x <;> first | (exfalso; omega) | (simp only [KS, Nat.reduceMul, Nat.reduceAdd]; sib87_chain)
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_pad {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if x = 8 then word M (KS + 32 * x) ^^^ rep 31
        else if x = 16 then word M (KS + 32 * x) ^^^ rep (2 ^ 63) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8531 (wd ret :: tail) M) (callState s 20467 (wd 8615 :: wd ret :: tail) M') 50 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt87_reach [3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> sib87_chain
    all_goals (try rfl)
    all_goals (simp only [↓reduceIte, if_false, if_true, Nat.reduceEqDiff]
               rw [MlDsaOpt44.Proofs.xor_mod_lit (MlDsaOpt44.Proofs.word_lt_lit _ _) (by norm_num)]
               norm_num only [rep, REP, pack4])
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

/-- Lanes `1, 2, 8, 12` (the complemented rate lanes) inverted. -/
def flip4 (M : ByteArray) (x : Nat) : Nat :=
  if x = 1 ∨ x = 2 ∨ x = 8 ∨ x = 12 then 115792089237316195423570985008687907853269984665640564039457584007913129639935 - word M (KS + 32 * x)
  else word M (KS + 32 * x)

theorem sib_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8615 (wd ret :: tail) M)
        (headSt s ret tail 8 196 (18446744073709551615 &&& word M 0) M') 78 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt87_reach [3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3267, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3276, 3277, 3278, 3279, 3280, 3281, 3282, 3283, 3284] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_rpre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (i sg : Nat) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (headSt s ret tail 136 i sg M)
        (callState s 20467 (wd 8722 :: wd 136 :: wd i :: wd sg :: wd ret :: tail) M') 122 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt87_reach [3285, 3286, 3287, 3288, 3289, 3290, 3291, 3292, 3293, 3294, 3295, 3296, 3297, 3298, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_rpost {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (i sg : Nat) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 8722 (wd 136 :: wd i :: wd sg :: wd ret :: tail) M)
        (nokSt s ret tail 136 i sg M') 61 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt87_reach [3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340]
    rfl
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt44.Proofs.frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

end MlDsaOpt87.Proofs.Ball
