import MlDsa44.Proofs.Infra
set_option warningAsError true
set_option linter.unusedSectionVars false
/-!
# Straight-line blocks of `computeRow`

Each lemma is one path of the compiled `computeRow` (instructions 2937–3133,
see `docs/reference.listing`), between `callState s …` states with the same
base `s`. Memory is left abstract.
-/

namespace MlDsa44.Proofs.Row

open EvmSemantics
open EvmSemantics.EVM

theorem addMod_mulMod_toNat (a b c : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hc : c < 2 ^ 256) :
    ((UInt256.ofNat a).addMod ((UInt256.ofNat b).mulMod (UInt256.ofNat c)
      (UInt256.ofNat 8380417)) (UInt256.ofNat 8380417)).toNat =
      (a + b * c % Fips204.q) % Fips204.q := by
  rw [Infra.ofNat_mulMod _ _ _ hb hc (by norm_num) (by norm_num),
    Infra.ofNat_addMod _ _ _ ha (by omega) (by norm_num) (by norm_num),
    Infra.toNat_ofNat_of_lt (by omega)]
  rfl

theorem addMod_subMulMod_toNat (a b c : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hc : c < 2 ^ 256) :
    ((UInt256.ofNat a).addMod (UInt256.ofNat 8380417 - (UInt256.ofNat b).mulMod (UInt256.ofNat c)
      (UInt256.ofNat 8380417)) (UInt256.ofNat 8380417)).toNat =
      (a + (Fips204.q - b * c % Fips204.q)) % Fips204.q := by
  have h1 : b * c % 8380417 < 8380417 := Nat.mod_lt _ (by norm_num)
  rw [Infra.ofNat_mulMod _ _ _ hb hc (by norm_num) (by norm_num),
    Infra.ofNat_sub (by omega) (by norm_num),
    Infra.ofNat_addMod _ _ _ ha (by omega) (by norm_num) (by norm_num),
    Infra.toNat_ofNat_of_lt (by omega)]
  rfl

/-- A loop whose per-iteration memory is only known to exist: from `P j M`
one iteration reaches some `M'` with `P (j + 1) M'`. -/
theorem reach_iter {S : Nat → ByteArray → State} {P : Nat → ByteArray → Prop} {c : Nat} :
    ∀ n, (∀ j, j < n → ∀ M, P j M → ∃ M', P (j + 1) M' ∧ Infra.Reach (S j M) (S (j + 1) M') c) →
      ∀ M0, P 0 M0 → ∃ M, P n M ∧ Infra.Reach (S 0 M0) (S n M) (n * c)
  | 0, _, M0, h0 => ⟨M0, h0, by simpa using Infra.Reach.refl (S 0 M0)⟩
  | n + 1, h, M0, h0 => by
    obtain ⟨M, hM, hr⟩ := reach_iter n (fun j hj => h j (by omega)) M0 h0
    obtain ⟨M', hM', hr'⟩ := h n (by omega) M hM
    exact ⟨M', hM', by simpa [Nat.succ_mul] using hr.trans hr'⟩

section
variable {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (haw : 2535 ≤ s.activeWords.toNat)
    (haw' : s.activeWords.toNat ≤ 18446744073709551616)
include hs htail haw haw'

theorem b_entry {i : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4415 (wd i :: wd 0 :: wd ret :: tail) M)
      (callState s 3067 (wd ACC :: wd 4430 :: wd i :: wd 1 :: wd ret :: tail) M) 26 := by
  evm_reach [2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_outerInit {i : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4430 (wd i :: wd 1 :: wd ret :: tail) M)
      (callState s 4432 (wd 0 :: wd i :: wd 1 :: wd ret :: tail) M) 3 := by
  evm_reach [2945, 2946] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_toShake {i j g : Nat} (hi : i < 4) (hj : j < 4) (M : ByteArray) :
    Infra.Reach (callState s 4432 (wd j :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 2680 (wd 168 :: wd SEEDA :: wd 34 :: wd XOF :: wd 6 :: wd 4481 ::
          wd j :: wd i :: wd g :: wd ret :: tail)
        (MachineState.writeBytes (MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat j])
          (SEEDA + 32)) (ByteArray.mk #[UInt8.ofNat i]) (SEEDA + 33))) 85 := by
  evm_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_toRej {i j g : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4481 (wd j :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 3523 (wd AP :: wd 0 :: wd 4493 :: wd j :: wd i :: wd g :: wd ret :: tail) M)
      20 := by
  evm_reach [2972, 2973, 2974, 2975, 2976, 2977] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_innerInit {i j g f : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4493 (wd f :: wd j :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4507 (wd 0 :: wd (ZH + POLY * j) :: wd j :: wd i :: wd (g &&& f) ::
        wd ret :: tail) M) 29 := by
  evm_reach [2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988] with [ZH, POLY, Nat.mul_comm 8192 j]

theorem b_inner {i j g t zj : Nat} (hj : j < 4) (ht : t < 256) (hzj : zj = ZH + POLY * j)
    (M : ByteArray) :
    Infra.Reach (callState s 4507 (wd t :: wd zj :: wd j :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4507 (wd (t + 1) :: wd zj :: wd j :: wd i :: wd g :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M (ACC + 32 * t) + word M (AP + 32 * t) * word M (zj + 32 * t) % Fips204.q)
            % Fips204.q) 32) (ACC + t * 32))) 131 := by
  simp only [ZH, POLY] at hzj
  subst hzj
  evm_reach [2989, 2990, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3000, 3001, 3002, 3003, 3004, 3005, 3006, 3007, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3025, 3026] with [ACC, AP, SEEDA, XOF, TP, CH]
  rw [addMod_mulMod_toNat _ _ _ (Infra.word_lt _ _) (Infra.word_lt _ _) (Infra.word_lt _ _)]
  simp only [Nat.mul_comm 32 t]

theorem b_innerExit {i j g zj : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4507 (wd 256 :: wd zj :: wd j :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4432 (wd (j + 1) :: wd i :: wd g :: wd ret :: tail) M) 56 := by
  evm_reach [2989, 2990, 2991, 2992, 2993, 2994, 2995, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_outerExit {i g : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4432 (wd 4 :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4579 (wd 0 :: wd i :: wd g :: wd ret :: tail) M) 31 := by
  evm_reach [2947, 2948, 2949, 2950, 2951, 2952, 2953, 3037, 3038, 3039] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_toUnpack {i g t : Nat} (ht : t < 256) (M : ByteArray) :
    Infra.Reach (callState s 4579 (wd t :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 3456 (wd (32 + 320 * i) :: wd t :: wd 10 :: wd 0 :: wd 4609 ::
        wd t :: wd i :: wd g :: wd ret :: tail) M) 65 := by
  evm_reach [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3056, 3057] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_fromUnpack {i g t v : Nat} (ht : t < 256) (hv : v < 2 ^ 10) (M : ByteArray) :
    Infra.Reach (callState s 4609 (wd v :: wd t :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4579 (wd (t + 1) :: wd i :: wd g :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v * 2 ^ 13) 32)
          (TP + t * 32))) 50 := by
  evm_reach [3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_toNtt {i g : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4579 (wd 256 :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 3107 (wd TP :: wd 4646 :: wd i :: wd g :: wd ret :: tail) M) 46 := by
  evm_reach [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3074, 3075, 3076, 3077, 3078, 3079] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_subInit {i g : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4646 (wd i :: wd g :: wd ret :: tail) M)
      (callState s 4648 (wd 0 :: wd i :: wd g :: wd ret :: tail) M) 3 := by
  evm_reach [3080, 3081] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_sub {i g t : Nat} (ht : t < 256) (M : ByteArray) :
    Infra.Reach (callState s 4648 (wd t :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 4648 (wd (t + 1) :: wd i :: wd g :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded
          ((word M (ACC + 32 * t) +
            (Fips204.q - word M (CH + 32 * t) * word M (TP + 32 * t) % Fips204.q)) % Fips204.q) 32)
          (ACC + t * 32))) 142 := by
  evm_reach [3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123]
  rw [addMod_subMulMod_toNat _ _ _ (Infra.word_lt _ _) (Infra.word_lt _ _) (Infra.word_lt _ _)]
  simp only [ACC, CH, TP, Nat.mul_comm 32 t]

theorem b_toNttInv {i g : Nat} (M : ByteArray) :
    Infra.Reach (callState s 4648 (wd 256 :: wd i :: wd g :: wd ret :: tail) M)
      (callState s 3255 (wd ACC :: wd 4726 :: wd i :: wd g :: wd ret :: tail) M) 46 := by
  evm_reach [3082, 3083, 3084, 3085, 3086, 3087, 3088, 3124, 3125, 3126, 3127, 3128, 3129] with [ACC, AP, SEEDA, XOF, TP, CH]

theorem b_final {i g : Nat} (hr : RetOK Stack.computeRow ret tail) (M : ByteArray) :
    Infra.Reach (callState s 4726 (wd i :: wd g :: wd ret :: tail) M)
      (callState s ret (wd g :: tail) M) 14 := by
  have := hr.small
  evm_reach [3130, 3131, 3132, 3133] with [hr.jumpdest]

end

end MlDsa44.Proofs.Row
