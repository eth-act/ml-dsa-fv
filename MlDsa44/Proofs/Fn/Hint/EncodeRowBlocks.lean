import MlDsa44.Proofs.Fn.Hint.Mem
set_option warningAsError true
/-!
# Straight-line blocks of `encodeRow(i)`

Locals: `hrow = HB + 256 i` (as `76256 + i * 256`), `out = W1 + 64 + 192 i`
(as `78656 + (64 + 192 i)`). Loop heads: outer `g` at pc 4283, inner `e` at
pc 4295. Every block is stated for an abstract memory `M`.
-/

namespace MlDsa44.Proofs.Hint

open EvmSemantics EvmSemantics.EVM

variable {s : State} {ret : Nat} {tail : List UInt256}

/-- Outer loop head: `g, hrow, out, i, ret`. -/
abbrev erOuter (s : State) (g i ret : Nat) (tail : List UInt256) (M : ByteArray) : State :=
  callState s 4283
    (wd g :: wd (76256 + i * 256) :: wd (78656 + (64 + 192 * i)) :: wd i :: wd ret :: tail) M

/-- Inner loop head: `e, v, g, hrow, out, i, ret`. -/
abbrev erInner (s : State) (e v g i ret : Nat) (tail : List UInt256) (M : ByteArray) : State :=
  callState s 4295 (wd e :: wd v :: wd g :: wd (76256 + i * 256) :: wd (78656 + (64 + 192 * i)) ::
    wd i :: wd ret :: tail) M

theorem er_entry (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) (M : ByteArray) (i : Nat) :
    Infra.Reach (callState s 4260 (wd i :: wd ret :: tail) M) (erOuter s 0 i ret tail M) 41 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  evm_reach [2821, 2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2834]

theorem er_head (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) (M : ByteArray) {i g : Nat}
    (hg : g < 64) :
    Infra.Reach (erOuter s g i ret tail M) (erInner s 0 0 g i ret tail M) 30 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  evm_reach [2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843]

/-- Inner body up to the `useHint` call: `useHint(byte(0, mload(hrow + t)), mload(ACC + 32 t))`
with `t = 4 g + e`, returning to pc 4334. -/
theorem er_call (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) {M m : ByteArray}
    {i g e v : Nat} (hi : i < 4) (hg : g < 64) (he : e < 4)
    (hby : byteAt M (76256 + i * 256 + (g * 4 + e)) = byteAt m (HB + 256 * i + (g * 4 + e)))
    (hw : word M (59872 + (g * 4 + e) * 32) = word m (ACC + 32 * (g * 4 + e))) :
    Infra.Reach (erInner s e v g i ret tail M)
      (callState s 4139 (wd (byteAt m (HB + 256 * i + (g * 4 + e))) ::
        wd (word m (ACC + 32 * (g * 4 + e))) :: wd 0 :: wd 4334 :: wd (g * 4 + e) :: wd e :: wd v ::
        wd g :: wd (76256 + i * 256) :: wd (78656 + (64 + 192 * i)) :: wd i :: wd ret :: tail) M)
      92 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have haw2 : 2535 ≤ s.activeWords.toNat := hs.sized
  evm_reach [2844, 2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857,
    2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871]
    with [ofNat_byte, word_byte0, hby, hw]

/-- After the call: `v |= w << 6e`, `e += 1`. -/
theorem er_after (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) (M : ByteArray)
    {i g e v w t : Nat} (he : e < 4) :
    Infra.Reach
      (callState s 4334 (wd w :: wd t :: wd e :: wd v :: wd g :: wd (76256 + i * 256) ::
        wd (78656 + (64 + 192 * i)) :: wd i :: wd ret :: tail) M)
      (erInner s (e + 1) (v ||| w * 2 ^ (6 * e)) g i ret tail M) 58 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  evm_reach [2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885,
    2886, 2887, 2888, 2889, 2890]

/-- Inner exit, the three `MSTORE8`s of group `g`, `g += 1`. -/
theorem er_store (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) (M : ByteArray)
    {i g v : Nat} (hi : i < 4) (hg : g < 64) (hv : v < 2 ^ 24) :
    Infra.Reach (erInner s 4 v g i ret tail M)
      (erOuter s (g + 1) i ret tail
        (wb (wb (wb M (78656 + (64 + 192 * i) + 3 * g) (v % 256))
          (78656 + (64 + 192 * i) + 3 * g + 1) (v / 256 % 256))
          (78656 + (64 + 192 * i) + 3 * g + 2) (v / 65536 % 256))) 138 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have haw2 : 2535 ≤ s.activeWords.toNat := hs.sized
  evm_reach [2844, 2845, 2846, 2847, 2848, 2849, 2850, 2891, 2892, 2893, 2894, 2895, 2896, 2897,
    2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911, 2912,
    2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927]
    with [land_255, Nat.mod_mod, wb]

theorem er_exit (hs : Ctx s) (hr : RetOK Stack.encodeRow ret tail) (M : ByteArray) {i : Nat} :
    Infra.Reach (erOuter s 64 i ret tail M) (callState s ret tail M) 43 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.encodeRow, Stack.useHint, Stack.leaf] at this; omega
  have := hr.small
  evm_reach [2835, 2836, 2837, 2838, 2839, 2840, 2841, 2928, 2929, 2930, 2931, 2932, 2933]
    with [hr.jumpdest]

end MlDsa44.Proofs.Hint
