import MlDsaOpt44.Layout
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 100000
/-!
# `sib` (v4, WP J): straight-line blocks

Loop head `sibloop` (pc 7256), stack `o :: i :: signs :: ret :: tail` (`o = 32 x`
for stream lane `x`). Byte `r` of the lane is tested at `skipPc r` (`r ≥ 1`) with
`z :: w :: o :: …` (`w` the lane word, `z` the previous byte or return label).
An accepted byte calls the shared accept step (`A`, `B` when `j` holds a
nonzero coefficient, then `C` back to the return label or `D` when all `τ`
are placed). At `o = LIM` the second block is squeezed (`ext*`, `LIM := 1088`)
or, if it already was, the routine fails.
-/

namespace MlDsaOpt44.Proofs.Ball4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

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
def skipPc (r : Nat) : Nat := 7292 + 24 * (r - 1)

/-- Loop-head state. -/
abbrev headSt (s : State) (ret : Nat) (tail : List UInt256) (o i sg : Nat) (M : ByteArray) : State :=
  callState s 7256 (wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- State before the test of byte `r ≥ 1` of a lane. -/
abbrev skipSt (s : State) (ret : Nat) (tail : List UInt256) (r z w o i sg : Nat) (M : ByteArray) : State :=
  callState s (skipPc r) (wd z :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

/-- The accept step's entry: byte `j`, return label `rl`. -/
abbrev accSt (s : State) (ret : Nat) (tail : List UInt256) (j rl w o i sg : Nat) (M : ByteArray) : State :=
  callState s 7470 (wd j :: wd rl :: wd w :: wd o :: wd i :: wd sg :: wd ret :: tail) M

theorem b_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) :
    Reach (callState s 7240 (wd ret :: tail) M)
      (headSt s ret tail 32 217 (word M 63488) (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 544 32) 3968)) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710]

theorem b_head_rej {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j lim : Nat)
    (ho : o ≤ 1088) (hlim : word M 3968 = lim) (hlim2 : lim ≤ 1088) (hne : o ≠ lim) (hw : word M (63488 + o) = w)
    (hj : 255 &&& w = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (skipSt s ret tail 1 j w o i sg M) 69 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729] with [hlim, hw, hj, skipPc]

theorem b_head_acc {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (o i sg w j lim : Nat)
    (ho : o ≤ 1088) (hlim : word M 3968 = lim) (hlim2 : lim ≤ 1088) (hne : o ≠ lim) (hw : word M (63488 + o) = w)
    (hj : 255 &&& w = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (headSt s ret tail o i sg M) (accSt s ret tail j 7292 w o i sg M) 86 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733] with [hlim, hw, hj]

theorem b_skip_rej1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (skipSt s ret tail 2 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745] with [hj, skipPc]

theorem b_skip_acc1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 256 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 1 z w o i sg M) (accSt s ret tail j 7316 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749] with [hj, skipPc]

theorem b_skip_rej2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (skipSt s ret tail 3 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761] with [hj, skipPc]

theorem b_skip_acc2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 65536 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 2 z w o i sg M) (accSt s ret tail j 7340 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765] with [hj, skipPc]

theorem b_skip_rej3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (skipSt s ret tail 4 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777] with [hj, skipPc]

theorem b_skip_acc3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 16777216 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 3 z w o i sg M) (accSt s ret tail j 7364 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781] with [hj, skipPc]

theorem b_skip_rej4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (skipSt s ret tail 5 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793] with [hj, skipPc]

theorem b_skip_acc4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 4294967296 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 4 z w o i sg M) (accSt s ret tail j 7388 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797] with [hj, skipPc]

theorem b_skip_rej5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (skipSt s ret tail 6 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809] with [hj, skipPc]

theorem b_skip_acc5 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 1099511627776 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 5 z w o i sg M) (accSt s ret tail j 7412 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813] with [hj, skipPc]

theorem b_skip_rej6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (skipSt s ret tail 7 j w o i sg M) 40 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825] with [hj, skipPc]

theorem b_skip_acc6 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 281474976710656 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 6 z w o i sg M) (accSt s ret tail j 7436 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829] with [hj, skipPc]

theorem b_skip_rej7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : i < j) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 62 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2846, 2847, 2848, 2849, 2850, 2851, 2852] with [hj, skipPc]

theorem b_skip_acc7 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg j : Nat) (hw : w < 2 ^ 256)
    (hj : 255 &&& w / 72057594037927936 = j) (hji : j ≤ i) (hj' : j < 256) (hi : i < 256) :
    Reach (skipSt s ret tail 7 z w o i sg M) (accSt s ret tail j 7460 w o i sg M) 57 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845] with [hj, skipPc]

theorem b_tail8 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (z w o i sg : Nat) :
    Reach (skipSt s ret tail 8 z w o i sg M) (headSt s ret tail (32 + o) i sg M) 22 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2846, 2847, 2848, 2849, 2850, 2851, 2852] with [skipPc]

/-- Memory after `CW[i] := CW[j]; NNEG += sg; CW[j] := code`. -/
abbrev memA (M : ByteArray) (i j nn sg code : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (12288 + j * 32)) 32)
        (12288 + i * 32))
      (Data.Bytes.natToBytesPadded (nn + sg) 32) 4000)
    (Data.Bytes.natToBytesPadded code 32) (12288 + j * 32)

theorem b_accA0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (hk : byteAt M (43008 + j) = 0) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 7604 (wd 0 :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

theorem b_accA1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (rl w o i signs : Nat) (hi : i < 256)
    (j : Nat) (hji : j ≤ i)
    (sg : Nat) (hsg : 1 &&& signs = sg) (hsg1 : sg ≤ 1)
    (nn : Nat) (hnn : word M 4000 = nn) (hnn' : nn ≤ 256)
    (code : Nat) (hcode : UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) - UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 = UInt256.ofNat code)
    (hcode' : code < 2 ^ 256)
    (k : Nat) (hk : byteAt M (43008 + j) = k) (hk0 : 0 < k) (hk1 : k < 256) :
    Reach (accSt s ret tail j rl w o i signs M)
      (callState s 7578 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memA M i j nn sg code)) 133 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894] with [hsg, hnn, hcode, word_mstore_disjoint, word_div_248, hk, Nat.mod_eq_of_lt hcode']

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

theorem b_accB {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i < 256) (hji : j ≤ i) (hk1 : k < 256)
    (bv : Nat) (hbv : word M (40928 + k * 32) = bv) (hbv' : bv < 2 ^ 200) :
    Reach (callState s 7578 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s 7604 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail)
        (memB M i j k bv)) 60 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911, 2912, 2913, 2914] with [hbv]

theorem b_accC {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray)
    (rl w o i signs j sg k : Nat) (hi : i + 1 < 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255)
    (hrl : Decode.isValidJumpDest MlDsaOpt44.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    Reach (callState s 7604 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (signs / 2) :: wd ret :: tail) (memC M j sg cnt)) 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have h1 : 1 + i = i + 1 := by omega
  opt44_reach [2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959] with [hcnt, h1, hrl]

theorem b_accD {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (rl w o i signs j sg k : Nat) (hi : i + 1 = 256) (hj : j < 256) (hsg1 : sg ≤ 1) (hsigns : signs < 2 ^ 256)
    (cnt : Nat) (hcnt : word M 4032 = cnt) (hcnt' : cnt < 255) :
    Reach (callState s 7604 (wd k :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i :: wd signs :: wd ret :: tail) M)
      (callState s ret (wd 1 :: tail) (memC M j sg cnt)) 157 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968] with [hcnt, hjd]

theorem b_ext1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (i sg : Nat) (hlim : word M 3968 = 544) :
    Reach (headSt s ret tail 544 i sg M)
      (callState s 7706 (wd 0 :: wd 61504 :: wd 800 :: wd 544 :: wd i :: wd sg :: wd ret :: tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1088 32) 3968)) 69 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2711, 2712, 2713, 2714, 2715, 2716, 2717, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2978, 2979, 2980, 2981] with [hlim]

theorem b_ext2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (i sg : Nat) :
    Reach (callState s 7707 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M)
      (callState s Entry.kf4 (wd 7714 :: wd 544 :: wd i :: wd sg :: wd ret :: tail) M) 14 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold Entry.kf4
  opt44_reach [2983, 2984, 2985]

theorem b_ext3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (i sg : Nat) :
    Reach (callState s 7714 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M)
      (callState s Entry.cext (wd 17 :: wd 0 :: wd 64032 :: wd 7728 :: wd 544 :: wd i :: wd sg :: wd ret :: tail) M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold Entry.cext
  opt44_reach [2986, 2987, 2988, 2989, 2990, 2991, 2992]

theorem b_ext4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray) (i sg : Nat) :
    Reach (callState s 7728 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M) (headSt s ret tail 544 i sg M) 12 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2993, 2994, 2995]

theorem b_fail {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (htail : tail.length ≤ 960) (hsized : 2616 ≤ s.activeWords.toNat) (M : ByteArray)
    (hjd : Decode.isValidJumpDest MlDsaOpt44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    (i sg : Nat) (hlim : word M 3968 = 1088) :
    Reach (headSt s ret tail 1088 i sg M) (callState s ret (wd 0 :: tail) M) 72 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  opt44_reach [2711, 2712, 2713, 2714, 2715, 2716, 2717, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2996, 2997, 2998, 2999, 3000, 3001, 3002] with [hlim, hjd]

end MlDsaOpt44.Proofs.Ball4
