import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/- Ported from `MlDsaOpt44/Fn/Ball/Blocks.lean` by `scripts/proofgen_port.py 65` --sub 63488=88064 --sub 43008=51200 --sub 40928=49120 --sub 217=207; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option maxRecDepth 100000
/-!
# `sib`: straight-line blocks

Loop head `sibloop` at instruction 3072 (pc 8021), stack
`p :: i :: signs :: ret :: tail`. An accepted byte runs `A` (to the `IDX[j]`
test), `B` when `j` holds a nonzero coefficient (move its window base), then
`C` (back to the head) or `D` (all `τ` placed: return `1`).
-/

namespace MlDsaOpt65.Proofs.Ball

open MlDsaOpt44.Proofs  -- port: the 44 `Ball` blocks are not imported

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

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
  callState s 8021 (wd p :: wd i :: wd sg :: wd ret :: tail) M

theorem sib_reject {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i sg : Nat) (hp : p < 272)
    (j : Nat) (hj : 255 &&& word M (88064 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j)
    (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail p i sg M) (headSt s ret tail (p + 1) i sg M) 125 := by
  have h1 : 1 + p = p + 1 := by omega
  opt65_reach [3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3191, 3192, 3193, 3194] with [land_seven, seven_land, hj, h1]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem sib_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (88064 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (51200 + j) = 0) :
    Reach (headSt s ret tail p i signs M)
      (callState s 8154 (wd 0 :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 241 := by
  have h1 : 1 + p = p + 1 := by omega
  opt65_reach [3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125] with [land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

theorem sib_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (88064 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (51200 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (headSt s ret tail p i signs M)
      (callState s 8128 (wd k :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 241 := by
  have h1 : 1 + p = p + 1 := by omega
  opt65_reach [3052, 3053, 3054, 3055, 3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125] with [land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

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
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (49120 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 8128 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 8154 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  opt65_reach [3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145] with [hbv]

theorem sib_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8154 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (headSt s ret tail p1 (i + 1) (signs / 2) (memC M j sg cnt)) 143 := by
  have h1 : 1 + i = i + 1 := by omega
  opt65_reach [3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190] with [hcnt, h1]

theorem sib_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (p1 i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 8154 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 153 := by
  opt65_reach [3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3195, 3196, 3197, 3198, 3199, 3200, 3201] with [hcnt, hjd]

theorem sib_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i signs : Nat) :
    Reach (headSt s ret tail 272 i signs M) (callState s ret (wd 0 :: tail) M) 43 := by
  opt65_reach [3052, 3053, 3054, 3055, 3056, 3057, 3202, 3203, 3204, 3205, 3206, 3207, 3208] with [hjd]

theorem sib_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2865 ≤ s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 8011 (wd ret :: tail) M) (headSt s ret tail 8 207 (word M 88064) M) 13 := by
  opt65_reach [3047, 3048, 3049, 3050, 3051]

end MlDsaOpt65.Proofs.Ball
