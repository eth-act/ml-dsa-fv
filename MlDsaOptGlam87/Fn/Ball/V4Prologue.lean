import MlDsaOptGlam87.Fn.Ball.V4Blocks
import MlDsaOpt87.Fn.Ball.V4Rep
import MlDsaOpt44.Fn.Sponge.Lanes
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Ball/V4Prologue.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
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
word `KS[0] mod 2^64`. At `o = 544` (stream byte 136), `sib_rpre` re-complements those lanes and calls
`kf1`, `sib_rpost` un-complements them again.
-/

namespace MlDsaOptGlam87.Proofs.Ball4

open MlDsaOpt87.Proofs MlDsaOpt87.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam87.Proofs.Infra

/-- Close the facts of a block whose memory is a chain of `MSTORE`s. -/
macro "sib87v4_chain" : tactic => `(tactic| (
  simp (disch := first | omega | exact word_lt _ _) only [word_mstore_disjoint, word_mstore]))

/-- The byte-swap masks and `REP` of the absorption. -/
def absK (ret : Nat) (tail : List UInt256) : List UInt256 :=
  wd 6277101735386680764176071790128604879584176795969512275969 :: wd 18446744073709551615 :: wd 26959946660873538060741835960174461801791452538186943042387869433855 :: wd 1766820105243087041267848467410591083712559083657179364930612997358944255 :: wd 450552876409790643671482431940419874915447411150352389258589821042463539455 :: wd ret :: tail

theorem sib_zero {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = rep (cpl x 0)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7102 (wd ret :: tail) M) (callState s 7225 (wd ret :: tail) M') 218 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911, 2912, 2913, 2914, 2915]
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> sib87v4_chain
    all_goals (try simp [cpl, complemented])
    all_goals (try norm_num [rep, REP, pack4])
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_absW0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if x < 4 then word M (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (CTOFF + 8 * x))
        else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7225 (wd ret :: tail) M) (callState s 7447 (absK ret tail) M') 255 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · unfold absK
    glam87_rreach [2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998] with [MlDsaOpt44.Proofs.WP4.bsw8_fold, MlDsaOpt44.Proofs.WP4.bsw16_fold,
      MlDsaOpt44.Proofs.WP4.bsw32_fold, MlDsaOpt44.Proofs.WP4.bswapNet_fold]
  · intro x hx
    by_cases hc : x < 4
    · rw [if_pos hc]
      obtain ⟨hc1, hc2⟩ : 0 ≤ x ∧ x < 4 := by omega
      interval_cases x
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 0) (off := 2592) (b := 2592) 0
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext0 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 1) (off := 2592) (b := 2592) 1
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext1 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 2) (off := 2592) (b := 2592) 2
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext2 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 3) (off := 2592) (b := 2592) 3
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext3 _)
    · rw [if_neg hc]
      interval_cases x <;> first | (exfalso; omega) | (simp only [KS, Nat.reduceMul, Nat.reduceAdd]; sib87v4_chain)
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_absW1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if 4 ≤ x ∧ x < 8 then
          word M (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (CTOFF + 8 * x))
        else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7447 (absK ret tail) M) (callState s 7549 (wd ret :: tail) M') 252 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · unfold absK
    glam87_rreach [2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081] with [MlDsaOpt44.Proofs.WP4.bsw8_fold, MlDsaOpt44.Proofs.WP4.bsw16_fold,
      MlDsaOpt44.Proofs.WP4.bsw32_fold, MlDsaOpt44.Proofs.WP4.bswapNet_fold]
  · intro x hx
    by_cases hc : 4 ≤ x ∧ x < 8
    · rw [if_pos hc]
      obtain ⟨hc1, hc2⟩ : 4 ≤ x ∧ x < 8 := by omega
      interval_cases x
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 4) (off := 2592) (b := 2624) 0
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext0 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 5) (off := 2592) (b := 2624) 1
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext1 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 6) (off := 2592) (b := 2624) 2
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext2 (MlDsaOpt44.Proofs.bswapNet_lt _))
      · simp only [KS, CTOFF, Nat.reduceMul, Nat.reduceAdd]
        sib87v4_chain
        exact MlDsaOpt44.Proofs.WP4.absorb_lane (m := M) (x := 7) (off := 2592) (b := 2624) 3
          (by norm_num) rfl (by norm_num) _ (MlDsaOpt44.Proofs.WP4.ext3 _)
    · rw [if_neg hc]
      interval_cases x <;> first | (exfalso; omega) | (simp only [KS, Nat.reduceMul, Nat.reduceAdd]; sib87v4_chain)
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_pad {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        if x = 8 then word M (KS + 32 * x) ^^^ rep 31
        else if x = 16 then word M (KS + 32 * x) ^^^ rep (2 ^ 63) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7549 (wd ret :: tail) M) (callState s 29816 (wd 7633 :: wd ret :: tail) M') 50 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096]
  · intro x hx
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> sib87v4_chain
    all_goals (try rfl)
    all_goals (simp only [↓reduceIte, if_false, if_true, Nat.reduceEqDiff]
               rw [MlDsaOpt87.Proofs.Ball4.r4_xor_mod_lit (MlDsaOpt87.Proofs.Ball4.r4_word_lt_lit _ _) (by norm_num)]
               norm_num only [rep, REP, pack4])
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

/-- Lanes `1, 2, 8, 12` (the complemented rate lanes) inverted. -/
def flip4 (M : ByteArray) (x : Nat) : Nat :=
  if x = 1 ∨ x = 2 ∨ x = 8 ∨ x = 12 then 115792089237316195423570985008687907853269984665640564039457584007913129639935 - word M (KS + 32 * x)
  else word M (KS + 32 * x)

theorem sib_post {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7633 (wd ret :: tail) M)
        (headSt s ret tail 32 196 (18446744073709551615 &&& word M 0) M') 78 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87v4_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_rpre {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (i sg : Nat) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (headSt s ret tail 544 i sg M)
        (callState s 29816 (wd 7742 :: wd 544 :: wd i :: wd sg :: wd ret :: tail) M') 123 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159]
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87v4_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem sib_rpost {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) (i sg : Nat) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 7742 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M)
        (nokSt s ret tail 544 i sg M') 61 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180]
  · intro x hx
    interval_cases x <;> simp only [KS, flip4, Nat.reduceMul, Nat.reduceAdd] <;> sib87v4_chain
    all_goals (try rfl)
  · simp only [KS]
    repeat (refine MlDsaOpt87.Proofs.Ball4.r4_frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

end MlDsaOptGlam87.Proofs.Ball4
