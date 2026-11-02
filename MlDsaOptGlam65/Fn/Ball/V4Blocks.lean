import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Ball/V4Blocks.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
/-!
# `sib` (v4, ML-DSA-65): straight-line blocks

Generated from `MlDsaOpt44/Fn/Ball/V4Blocks.lean` (indices, pcs and costs from
`MlDsaOpt65/listing.tsv`). Loop head `sibloop` (pc 7343), stack
`o :: i :: signs :: ret :: tail` (`o = 32 x` for stream lane `x`). Byte `r` of
the lane is tested at `skipPc r` (`r ≥ 1`) with `z :: w :: o :: …` (`w` the
lane word, `z` the previous byte or return label). An accepted byte calls the
shared accept step (`A`, `B` when `j` holds a nonzero coefficient, then `C`
back to the return label or `D` when all `τ` are placed). Both stream blocks
are in `CB` (34 lanes); at `o = 0x440` the routine fails (returns `0`).
-/

namespace MlDsaOptGlam65.Proofs.Ball4

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

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
def skipPc (r : Nat) : Nat := 7379 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 7343 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 7557 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

theorem b_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 7333 (wd ret :: tail) M) (headSt s ret tail 32 207 (word M 88064) M) 13 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2922, 2923, 2924, 2925, 2926]

theorem b_head_rej {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o ≤ 1088) (hne : o ≠ 1088) (hw : word M (88064 + o) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) 66 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944] with [hw, hj, skipPc]

theorem b_head_acc {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j : Nat)
    (ho : o ≤ 1088) (hne : o ≠ 1088) (hw : word M (88064 + o) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (accSt s ret tail j 7379 w o i sg M) 83 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948] with [hw, hj]

theorem b_skip_rej1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (skipSt s ret tail 2 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960] with [hj, skipPc]

theorem b_skip_acc1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (accSt s ret tail j 7403 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964] with [hj, skipPc]

theorem b_skip_rej2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (skipSt s ret tail 3 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976] with [hj, skipPc]

theorem b_skip_acc2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (accSt s ret tail j 7427 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980] with [hj, skipPc]

theorem b_skip_rej3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (skipSt s ret tail 4 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992] with [hj, skipPc]

theorem b_skip_acc3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (accSt s ret tail j 7451 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991, 2992, 2993, 2994, 2995, 2996] with [hj, skipPc]

theorem b_skip_rej4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (skipSt s ret tail 5 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008] with [hj, skipPc]

theorem b_skip_acc4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (accSt s ret tail j 7475 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012] with [hj, skipPc]

theorem b_skip_rej5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (skipSt s ret tail 6 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024] with [hj, skipPc]

theorem b_skip_acc5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (accSt s ret tail j 7499 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026, 3027, 3028] with [hj, skipPc]

theorem b_skip_rej6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (skipSt s ret tail 7 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040] with [hj, skipPc]

theorem b_skip_acc6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (accSt s ret tail j 7523 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039, 3040, 3041, 3042, 3043, 3044] with [hj, skipPc]

theorem b_skip_rej7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 62 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3061, 3062, 3063, 3064, 3065, 3066, 3067] with [hj, skipPc]

theorem b_skip_acc7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (accSt s ret tail j 7547 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060] with [hj, skipPc]

theorem b_tail8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg : Nat) :
    Reach (skipSt s ret tail 8 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3061, 3062, 3063, 3064, 3065, 3066, 3067] with [skipPc]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem b_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (51200 + j) = 0) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 7691 (wd 0 :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

theorem b_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 7665 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

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

theorem b_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (49120 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 7665 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 7691 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129] with [hbv]

theorem b_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255)
    (hrl : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    Reach (callState s 7691 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (signs / 2) :: wd ret :: tail) (memC M j sg cnt)) 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have h1 : 1 + i = i + 1 := by omega
  glam65_rreach [3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174] with [hcnt, h1, hrl]

theorem b_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (rl w o i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 7691 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 157 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183] with [hcnt, hjd]

theorem b_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) 43 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  glam65_rreach [2927, 2928, 2929, 2930, 2931, 2932, 3184, 3185, 3186, 3187, 3188, 3189, 3190] with [hjd]

end MlDsaOptGlam65.Proofs.Ball4
