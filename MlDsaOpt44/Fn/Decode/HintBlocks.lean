import MlDsaOpt44.Layout
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

namespace MlDsaOpt44.Proofs.DecodeH

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
    Reach (callState s 7530 (wd ret :: tail) M) (callState s 7534 (wd 0 :: wd 1 :: wd ret :: tail) M) 6 := by
  opt44_reach [2923, 2924, 2925]

theorem h0_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3728 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 7534 (wd a :: G :: wd ret :: tail) M) (callState s 7561 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt44_reach [2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2945, 2946] with [word_shr248, hB]

theorem h0_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3728 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 7534 (wd a :: G :: wd ret :: tail) M) (callState s 7561 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · opt44_reach [2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946] with [word_shr248, hB]
  · opt44_reach [2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946] with [word_shr248, hB]
  · opt44_reach [2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946] with [word_shr248, hB]
  · omega

theorem h0_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 7561 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7631 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt44_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 2994, 2995, 2996, 2997]

theorem h0_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7561 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7561 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  opt44_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993] with [word_shr248, hY, or_word_mod]

theorem h0_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7561 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7561 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  opt44_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993] with [word_shr248, hY, hP, or_word_mod]

theorem h0_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7561 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7561 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (1 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  opt44_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993] with [word_shr248, hY, hP, or_word_mod]

theorem h1_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3729 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 7631 (wd a :: G :: wd ret :: tail) M) (callState s 7658 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt44_reach [2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3017, 3018] with [word_shr248, hB]

theorem h1_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3729 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 7631 (wd a :: G :: wd ret :: tail) M) (callState s 7658 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · opt44_reach [2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018] with [word_shr248, hB]
  · opt44_reach [2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018] with [word_shr248, hB]
  · opt44_reach [2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018] with [word_shr248, hB]
  · omega

theorem h1_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 7658 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7736 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt44_reach [3019, 3020, 3021, 3022, 3023, 3024, 3025, 3066, 3067, 3068, 3069]

theorem h1_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7658 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7658 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  opt44_reach [3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065] with [word_shr248, hY, or_word_mod]

theorem h1_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7658 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7658 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  opt44_reach [3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065] with [word_shr248, hY, hP, or_word_mod]

theorem h1_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7658 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7658 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (18446744073709551616 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  opt44_reach [3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065] with [word_shr248, hY, hP, or_word_mod]

theorem h2_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3730 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 7736 (wd a :: G :: wd ret :: tail) M) (callState s 7763 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt44_reach [3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3089, 3090] with [word_shr248, hB]

theorem h2_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3730 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 7736 (wd a :: G :: wd ret :: tail) M) (callState s 7763 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · opt44_reach [3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090] with [word_shr248, hB]
  · opt44_reach [3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090] with [word_shr248, hB]
  · opt44_reach [3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090] with [word_shr248, hB]
  · omega

theorem h2_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 7763 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7849 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt44_reach [3091, 3092, 3093, 3094, 3095, 3096, 3097, 3138, 3139, 3140, 3141]

theorem h2_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7763 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7763 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  opt44_reach [3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137] with [word_shr248, hY, or_word_mod]

theorem h2_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7763 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7763 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  opt44_reach [3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137] with [word_shr248, hY, hP, or_word_mod]

theorem h2_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7763 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7763 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (340282366920938463463374607431768211456 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  opt44_reach [3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137] with [word_shr248, hY, hP, or_word_mod]

theorem h3_hok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat}
    (hB : byteAt s.executionEnv.calldata 3731 = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Reach (callState s 7849 (wd a :: G :: wd ret :: tail) M) (callState s 7876 (wd a :: wd B :: wd a :: G :: wd ret :: tail) M) 53 := by
  opt44_reach [3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3161, 3162] with [word_shr248, hB]

theorem h3_hbad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a B : Nat} (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata 3731 = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Reach (callState s 7849 (wd a :: G :: wd ret :: tail) M) (callState s 7876 (wd a :: wd a :: wd a :: wd 0 :: wd ret :: tail) M) 65 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · opt44_reach [3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162] with [word_shr248, hB]
  · opt44_reach [3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162] with [word_shr248, hB]
  · opt44_reach [3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162] with [word_shr248, hB]
  · omega

theorem h3_iexit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 : Nat} (hb : b0 ≤ 80) :
    Reach (callState s 7876 (wd b0 :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7970 (wd b0 :: G :: wd ret :: tail) M) 34 := by
  opt44_reach [3163, 3164, 3165, 3166, 3167, 3168, 3169, 3210, 3211, 3212, 3213]

theorem h3_ifirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 Y : Nat} (hab : a < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7876 (wd a :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7876 (wd (1 + a) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 117 := by
  opt44_reach [3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209] with [word_shr248, hY, or_word_mod]

theorem h3_iok (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7876 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7876 (wd (1 + idx) :: wd b0 :: wd a :: G :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 154 := by
  opt44_reach [3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209] with [word_shr248, hY, hP, or_word_mod]

theorem h3_ibad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a b0 idx P Y : Nat} (hai : a < idx) (hib : idx < b0) (hb : b0 ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 59648 ≤ 32 * s.activeWords.toNat) :
    Reach (callState s 7876 (wd idx :: wd b0 :: wd a :: G :: wd ret :: tail) M) (callState s 7876 (wd (1 + idx) :: wd b0 :: wd a :: wd 0 :: wd ret :: tail) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (6277101735386680763835789423207666416102355444464034512896 ||| word M (51456 + Y * 32)) 32) (51456 + Y * 32))) 161 := by
  opt44_reach [3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209] with [word_shr248, hY, hP, or_word_mod]

theorem h_texit (hs : Ctx s) (hr : RetOK Stack.dhint ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    (G : UInt256) :
    Reach (callState s 7970 (wd 80 :: G :: wd ret :: tail) M) (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  opt44_reach [3214, 3215, 3216, 3217, 3218, 3219, 3220, 3238, 3239, 3240, 3241] with [hr.jumpdest]

theorem h_tzero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = 0) :
    Reach (callState s 7970 (wd idx :: G :: wd ret :: tail) M)
      (callState s 7970 (wd (1 + idx) :: G :: wd ret :: tail) M) 78 := by
  opt44_reach [3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3233, 3234, 3235, 3236, 3237] with [word_shr248, hY]

theorem h_tnz (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {idx Y : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Reach (callState s 7970 (wd idx :: G :: wd ret :: tail) M)
      (callState s 7970 (wd (1 + idx) :: wd 0 :: wd ret :: tail) M) 85 := by
  opt44_reach [3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237] with [word_shr248, hY]

end

end MlDsaOpt44.Proofs.DecodeH

