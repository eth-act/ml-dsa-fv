import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Math.Hint.UseHint
set_option warningAsError true
/-!
# Straight-line blocks of `useHint`

The body splits at the join point after the `switch eq(hi, q − 1)` (pc 4203):
* first half (entry, pc 4139 → 4203): `hi = q − 1` (119 gas) or not (114 gas),
  stated per case of `neg = r0u > γ₂` / `r0u = 0`;
* second half (pc 4203 → `ret`): `hb = 0` (44), `hb = 1 ∧ r0pos` (108),
  `hb = 1 ∧ ¬r0pos` (98).
-/

namespace MlDsa44.Proofs.Hint

open EvmSemantics EvmSemantics.EVM

variable {s : State} {ret : Nat} {tail : List UInt256}

/-- The join-point stack: `r0pos, hi, neg, r0u, hb, r, r1, ret`. -/
abbrev uhJoin (s : State) (p hi n r0u hb r r1 ret : Nat) (tail : List UInt256) (m : ByteArray) :
    State :=
  callState s 4203 (wd p :: wd hi :: wd n :: wd r0u :: wd hb :: wd r :: wd r1 :: wd ret :: tail) m

abbrev uhEntry (s : State) (hb r ret : Nat) (tail : List UInt256) (m : ByteArray) : State :=
  callState s 4139 (wd hb :: wd r :: wd 0 :: wd ret :: tail) m

/-- Takes `hr` rather than a bare jumpdest hypothesis: a local
`isValidJumpDest … = true` in context sends the `assumption` discharger into a
deep unfolding. -/
theorem uh_second (hs : Ctx s) (hr : RetOK Stack.useHint ret tail)
    (htl : tail.length ≤ 960) (m : ByteArray) {hb p r1 : Nat} (hi n r0u r : Nat)
    (hhb : hb ≤ 1) (hp : p ≤ 1) (hr1 : r1 < 44) :
    Infra.Reach (uhJoin s p hi n r0u hb r r1 ret tail m)
      (callState s ret (wd (adjust hb p r1) :: tail) m) (if p = 1 then 108 else 98) := by
  have := hr.small
  obtain rfl | rfl : hb = 0 ∨ hb = 1 := by omega
  · refine Infra.Reach.mono (a := 44) ?_ (by split <;> decide)
    evm_reach [2777, 2778, 2779, 2780, 2781, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816,
      2817] with [hr.jumpdest, adjust]
  · obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · show Infra.Reach _ _ 98
      evm_reach [2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2799,
        2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813,
        2814, 2815, 2816, 2817] with [hr.jumpdest, adjust, Infra.ofNat_mod_ofNat]
    · show Infra.Reach _ _ 108
      evm_reach [2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789,
        2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2808, 2809, 2810, 2811, 2812,
        2813, 2814, 2815, 2816, 2817] with [hr.jumpdest, adjust, Infra.ofNat_mod_ofNat]

theorem uh_first_neg_top (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) {r : Nat}
    (hb : Nat) (hq : r < 8380417) (hneg : r % 190464 > 95232)
    (hhi : r - r % 190464 + 190464 = 8380416) :
    Infra.Reach (uhEntry s hb r ret tail m)
      (uhJoin s 0 (r - r % 190464 + 190464) 1 (r % 190464) hb r 0 ret tail m) 119 := by
  evm_reach [2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745,
    2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760,
    2761, 2762, 2763, 2764, 2765, 2766, 2767, 2768, 2769] with [Infra.ofNat_mod_ofNat]

theorem uh_first_neg (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) {r : Nat}
    (hb : Nat) (hq : r < 8380417) (hneg : r % 190464 > 95232)
    (hhi : ¬ r - r % 190464 + 190464 = 8380416) :
    Infra.Reach (uhEntry s hb r ret tail m)
      (uhJoin s 0 (r - r % 190464 + 190464) 1 (r % 190464) hb r
        ((r - r % 190464 + 190464) / 190464) ret tail m) 114 := by
  evm_reach [2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745,
    2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760,
    2761, 2770, 2771, 2772, 2773, 2774, 2775, 2776]
    with [Infra.ofNat_mod_ofNat, Infra.ofNat_div_ofNat]

theorem uh_first_zero_top (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) {r : Nat}
    (hb : Nat) (hq : r < 8380417) (hz : r % 190464 = 0)
    (hhi : r - r % 190464 + 0 = 8380416) :
    Infra.Reach (uhEntry s hb r ret tail m)
      (uhJoin s 0 (r - r % 190464 + 0) 0 (r % 190464) hb r 0 ret tail m) 119 := by
  evm_reach [2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745,
    2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760,
    2761, 2762, 2763, 2764, 2765, 2766, 2767, 2768, 2769] with [Infra.ofNat_mod_ofNat]

theorem uh_first_pos (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) {r p : Nat}
    (hb : Nat) (hq : r < 8380417) (hneg : ¬ r % 190464 > 95232)
    (hp : p = if r % 190464 > 0 then 1 else 0)
    (hhi : ¬ r - r % 190464 + 0 = 8380416) :
    Infra.Reach (uhEntry s hb r ret tail m)
      (uhJoin s p (r - r % 190464 + 0) 0 (r % 190464) hb r
        ((r - r % 190464 + 0) / 190464) ret tail m) 114 := by
  by_cases hz : r % 190464 > 0
  · rw [if_pos hz] at hp; subst hp
    evm_reach [2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745,
      2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760,
      2761, 2770, 2771, 2772, 2773, 2774, 2775, 2776]
      with [Infra.ofNat_mod_ofNat, Infra.ofNat_div_ofNat]
  · rw [if_neg hz] at hp; subst hp
    evm_reach [2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745,
      2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760,
      2761, 2770, 2771, 2772, 2773, 2774, 2775, 2776]
      with [Infra.ofNat_mod_ofNat, Infra.ofNat_div_ofNat]

end MlDsa44.Proofs.Hint
