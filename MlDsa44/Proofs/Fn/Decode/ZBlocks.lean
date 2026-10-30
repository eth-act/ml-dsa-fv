import MlDsa44.Proofs.Fn.Decode.Bytes
set_option warningAsError true
/-!
# Straight-line blocks of `decodeZ`

Loop heads: `4005` (outer, stack `i, good`), `4024` (inner, `j, base, i, good`).
Calls: `unpack` (return `4055`) and `ntt` (return `4118`). `G` is the `good`
slot when a block only moves it.
-/

namespace MlDsa44.Proofs.Decode

open EvmSemantics
open EvmSemantics.EVM

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem z_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Infra.Reach (callState s 4000 (wd 0 :: wd ret :: tail) M)
      (callState s 4005 (wd 0 :: wd 1 :: wd ret :: tail) M) 8 := by
  evm_reach [2642, 2643, 2644, 2645]

theorem z_outer (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i : Nat} (hi : i < 4) :
    Infra.Reach (callState s 4005 (wd i :: G :: wd ret :: tail) M)
      (callState s 4024 (wd 0 :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail) M) 43 := by
  evm_reach [2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655, 2656, 2657, 2658]

theorem z_call (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i j : Nat} (hj : j < 256) :
    Infra.Reach (callState s 4024 (wd j :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail) M)
      (callState s 3456 (wd (1344 + 576 * i) :: wd j :: wd 18 :: wd 0 :: wd 4055 ::
        wd j :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail) M) 65 := by
  evm_reach [2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671, 2672, 2673, 2674, 2675, 2676]

theorem z_storeOK (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) (G : UInt256) (R : Nat → Nat) {i j : Nat} (hi : i < 4) (hj : j < 256)
    (hR : 78 < R j ∧ R j < 262066) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 43520 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 4055 (wd (R j) :: wd j :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail)
        (Infra.storeWords m (10720 + i * 8192) (fun j => (131072 + (8380417 - R j)) % 8380417) j))
      (callState s 4024 (wd (j + 1) :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail)
        (Infra.storeWords m (10720 + i * 8192) (fun j => (131072 + (8380417 - R j)) % 8380417) (j + 1))) 104 := by
  evm_reach [2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710] with [Infra.storeWords_succ, Infra.ofNat_addMod]

theorem z_storeBad (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) (G : UInt256) (R : Nat → Nat) {i j : Nat} (hi : i < 4) (hj : j < 256)
    (hR : ¬(78 < R j ∧ R j < 262066)) (hR' : R j < 262144) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 43520 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 4055 (wd (R j) :: wd j :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail)
        (Infra.storeWords m (10720 + i * 8192) (fun j => (131072 + (8380417 - R j)) % 8380417) j))
      (callState s 4024 (wd (j + 1) :: wd (10720 + i * 8192) :: wd i :: wd 0 :: wd ret :: tail)
        (Infra.storeWords m (10720 + i * 8192) (fun j => (131072 + (8380417 - R j)) % 8380417) (j + 1))) 111 := by
  by_cases h1 : 78 < R j <;> by_cases h2 : R j < 262066
  · exact absurd ⟨h1, h2⟩ hR
  · evm_reach [2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710] with [Infra.storeWords_succ, Infra.ofNat_addMod]
  · evm_reach [2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710] with [Infra.storeWords_succ, Infra.ofNat_addMod]
  · omega

theorem z_innerExit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i : Nat} :
    Infra.Reach (callState s 4024 (wd 256 :: wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail) M)
      (callState s 3107 (wd (10720 + i * 8192) :: wd 4118 :: wd (10720 + i * 8192) :: wd i :: G ::
        wd ret :: tail) M) 46 := by
  evm_reach [2659, 2660, 2661, 2662, 2663, 2664, 2665, 2711, 2712, 2713, 2714, 2715, 2716]

theorem z_afterNtt (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i : Nat} :
    Infra.Reach (callState s 4118 (wd (10720 + i * 8192) :: wd i :: G :: wd ret :: tail) M)
      (callState s 4005 (wd (i + 1) :: G :: wd ret :: tail) M) 28 := by
  evm_reach [2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725]

theorem z_exit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256)
    (hr : RetOK Stack.decodeZ ret tail) :
    Infra.Reach (callState s 4005 (wd 4 :: G :: wd ret :: tail) M)
      (callState s ret (G :: tail) M) 40 := by
  have := hr.small
  evm_reach [2646, 2647, 2648, 2649, 2650, 2651, 2652, 2726, 2727, 2728, 2729] with [hr.jumpdest]

end

end MlDsa44.Proofs.Decode
