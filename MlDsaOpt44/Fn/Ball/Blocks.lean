import MlDsaOpt44.Layout
set_option warningAsError true
set_option maxRecDepth 100000
/-!
# `sib`: straight-line blocks

Loop head `sibloop` at instruction 2766 (pc 7310), stack
`p :: i :: signs :: ret :: tail`. An accepted byte runs `A` (to the `IDX[j]`
test), `B` when `j` holds a nonzero coefficient (move its window base), then
`C` (back to the head) or `D` (all `τ` placed: return `1`).
-/

namespace MlDsaOpt44.Proofs.Ball

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

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
  callState s 7310 (wd p :: wd i :: wd sg :: wd ret :: tail) M

theorem sib_reject {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i sg : Nat) (hp : p < 272)
    (j : Nat) (hj : 255 &&& word M (63488 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j)
    (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail p i sg M) (headSt s ret tail (p + 1) i sg M) 125 := by
  have h1 : 1 + p = p + 1 := by omega
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2905, 2906, 2907, 2908] with [land_seven, seven_land, hj, h1]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem sib_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (63488 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (43008 + j) = 0) :
    Reach (headSt s ret tail p i signs M)
      (callState s 7442 (wd 0 :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 241 := by
  have h1 : 1 + p = p + 1 := by omega
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839] with [land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

theorem sib_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (p i signs : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : 255 &&& word M (63488 + p / 8 * 32) / 2 ^ (p % 8 * 8) = j) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (43008 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (headSt s ret tail p i signs M)
      (callState s 7416 (wd k :: wd sg :: wd j :: wd (p + 1) :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 241 := by
  have h1 : 1 + p = p + 1 := by omega
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839] with [land_seven, seven_land, hj, h1, hsg, hnn, hcode, hk, word_div_248, word_mstore_disjoint]

/-- Memory after `BASES[k-1] += 8 (i - j); IDX[i] := k`. -/
abbrev memB (M : ByteArray) (i j k bv : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes M (Data.Bytes.natToBytesPadded ((i - j) * 8 + bv) 32) (40928 + k * 32))
    (ByteArray.mk #[UInt8.ofNat k]) (43008 + i)

/-- Memory after `IDX[j] := cnt + 1; CNT := cnt + 1; BASES[cnt] := 4064 + 8 j - 2048 sg`. -/
abbrev memC (M : ByteArray) (j sg cnt : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes (MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat (1 + cnt)]) (43008 + j))
      (Data.Bytes.natToBytesPadded (1 + cnt) 32) 4032)
    (Data.Bytes.natToBytesPadded (4064 + j * 8 - sg * 2048) 32) (40928 + (1 + cnt) * 32)

theorem sib_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (40928 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 7416 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 7442 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  opt44_reach [2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859] with [hbv]

theorem sib_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (p1 i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 7442 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (headSt s ret tail p1 (i + 1) (signs / 2) (memC M j sg cnt)) 143 := by
  have h1 : 1 + i = i + 1 := by omega
  opt44_reach [2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904] with [hcnt, h1]

theorem sib_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (p1 i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 7442 (wd k :: wd sg :: wd j :: wd p1 :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 153 := by
  opt44_reach [2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2909, 2910, 2911, 2912, 2913, 2914, 2915] with [hcnt, hjd]

theorem sib_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i signs : Nat) :
    Reach (headSt s ret tail 272 i signs M) (callState s ret (wd 0 :: tail) M) 43 := by
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2916, 2917, 2918, 2919, 2920, 2921, 2922] with [hjd]

theorem sib_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsized : 2065 ≤ s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 7301 (wd ret :: tail) M) (headSt s ret tail 8 217 (word M 63488) M) 13 := by
  opt44_reach [2761, 2762, 2763, 2764, 2765]

end MlDsaOpt44.Proofs.Ball
