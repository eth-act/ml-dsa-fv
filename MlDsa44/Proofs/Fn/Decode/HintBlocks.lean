import MlDsa44.Proofs.Fn.Decode.Bytes
set_option warningAsError true
/-!
# Straight-line blocks of `decodeHint`

Loop heads: `3791` (zeroing `HB`, stack `j, good`), `3826` (outer loop,
`i, index, good`), `3865` (inner loop, `idx, bound, i, index, good`), `3953`
(final scan, `idx, index, good`). `G` is the `good` slot when a block only
moves it. Calldata bytes enter through `byteAt cd …` equations.
-/

namespace MlDsa44.Proofs.Decode

open EvmSemantics
open EvmSemantics.EVM

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem hint_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Infra.Reach (callState s 3786 (wd 0 :: wd ret :: tail) M)
      (callState s 3791 (wd 0 :: wd 1 :: wd ret :: tail) M) 8 := by
  evm_reach [2480, 2481, 2482, 2483]

theorem hint_zero (hs : Ctx s) (htl : tail.length ≤ 960) (m : ByteArray) {j : Nat} (hj : j < 32) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 3791 (wd j :: wd 1 :: wd ret :: tail) (Infra.storeWords m 76256 (fun _ => 0) j))
      (callState s 3791 (wd (j + 1) :: wd 1 :: wd ret :: tail) (Infra.storeWords m 76256 (fun _ => 0) (j + 1))) 71 := by
  evm_reach [2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504] with [Infra.storeWords_succ]

theorem hint_zeroExit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Infra.Reach (callState s 3791 (wd 32 :: wd 1 :: wd ret :: tail) M)
      (callState s 3826 (wd 0 :: wd 0 :: wd 1 :: wd ret :: tail) M) 33 := by
  evm_reach [2484, 2485, 2486, 2487, 2488, 2489, 2490, 2505, 2506, 2507, 2508]

theorem hint_outerOK (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a B : Nat} (hi : i < 4)
    (hB : byteAt s.executionEnv.calldata (3728 + i) = B) (hab : a ≤ B) (hB80 : B ≤ 80) :
    Infra.Reach (callState s 3826 (wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3865 (wd a :: wd B :: wd i :: wd a :: G :: wd ret :: tail) M) 84 := by
  evm_reach [2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2538, 2539] with [byte0_word, hB]

theorem hint_outerBad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a B : Nat} (hi : i < 4) (ha : a ≤ 80)
    (hB : byteAt s.executionEnv.calldata (3728 + i) = B) (hB256 : B < 256) (hbad : B < a ∨ 80 < B) :
    Infra.Reach (callState s 3826 (wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3865 (wd a :: wd a :: wd i :: wd a :: wd 0 :: wd ret :: tail) M) 99 := by
  by_cases h1 : B < a <;> by_cases h2 : 80 < B
  · evm_reach [2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539] with [byte0_word, hB]
  · evm_reach [2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539] with [byte0_word, hB]
  · evm_reach [2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539] with [byte0_word, hB]
  · omega

theorem hint_innerFirst (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a b Y : Nat} (hi : i < 4) (hab : a < b) (hb : b ≤ 80)
    (hY : byteAt s.executionEnv.calldata (3648 + a) = Y) (hY256 : Y < 256) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 3865 (wd a :: wd b :: wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3865 (wd (a + 1) :: wd b :: wd i :: wd a :: G :: wd ret :: tail)
        (MachineState.writeBytes M { data := #[UInt8.ofNat 1] } (76256 + (i * 256 + Y)))) 123 := by
  evm_reach [2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590] with [byte0_word, hY]

theorem hint_innerOK (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a b idx P Y : Nat} (hi : i < 4) (hai : a < idx) (hib : idx < b)
    (hb : b ≤ 80) (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hPY : P < Y) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 3865 (wd idx :: wd b :: wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3865 (wd (idx + 1) :: wd b :: wd i :: wd a :: G :: wd ret :: tail)
        (MachineState.writeBytes M { data := #[UInt8.ofNat 1] } (76256 + (i * 256 + Y)))) 160 := by
  evm_reach [2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2572, 2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590] with [byte0_word, hY, hP]

theorem hint_innerBad (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a b idx P Y : Nat} (hi : i < 4) (hai : a < idx) (hib : idx < b)
    (hb : b ≤ 80) (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256)
    (hP : byteAt s.executionEnv.calldata (3647 + idx) = P) (hP256 : P < 256) (hPY : Y ≤ P) (haw : s.activeWords.toNat ≤ 18446744073709551616) (hmem : 77280 ≤ 32 * s.activeWords.toNat) :
    Infra.Reach (callState s 3865 (wd idx :: wd b :: wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3865 (wd (idx + 1) :: wd b :: wd i :: wd a :: wd 0 :: wd ret :: tail)
        (MachineState.writeBytes M { data := #[UInt8.ofNat 1] } (76256 + (i * 256 + Y)))) 167 := by
  evm_reach [2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590] with [byte0_word, hY, hP]

theorem hint_innerExit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {i a b : Nat} (hb : b ≤ 80) :
    Infra.Reach (callState s 3865 (wd b :: wd b :: wd i :: wd a :: G :: wd ret :: tail) M)
      (callState s 3826 (wd (i + 1) :: wd b :: G :: wd ret :: tail) M) 64 := by
  evm_reach [2540, 2541, 2542, 2543, 2544, 2545, 2546, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603]

theorem hint_outerExit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a : Nat} :
    Infra.Reach (callState s 3826 (wd 4 :: wd a :: G :: wd ret :: tail) M)
      (callState s 3953 (wd a :: wd a :: G :: wd ret :: tail) M) 32 := by
  evm_reach [2509, 2510, 2511, 2512, 2513, 2514, 2515, 2604, 2605, 2606]

theorem hint_finZero (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a idx : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = 0) :
    Infra.Reach (callState s 3953 (wd idx :: wd a :: G :: wd ret :: tail) M)
      (callState s 3953 (wd (idx + 1) :: wd a :: G :: wd ret :: tail) M) 85 := by
  evm_reach [2607, 2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633] with [byte0_word, hY]

theorem hint_finNZ (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a idx Y : Nat} (hidx : idx < 80)
    (hY : byteAt s.executionEnv.calldata (3648 + idx) = Y) (hY256 : Y < 256) (hY0 : Y ≠ 0) :
    Infra.Reach (callState s 3953 (wd idx :: wd a :: G :: wd ret :: tail) M)
      (callState s 3953 (wd (idx + 1) :: wd a :: wd 0 :: wd ret :: tail) M) 92 := by
  evm_reach [2607, 2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633] with [byte0_word, hY]

theorem hint_finExit (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) (G : UInt256) {a : Nat}
    (hr : RetOK Stack.decodeHint ret tail) :
    Infra.Reach (callState s 3953 (wd 80 :: wd a :: G :: wd ret :: tail) M)
      (callState s ret (G :: tail) M) 42 := by
  have := hr.small
  evm_reach [2607, 2608, 2609, 2610, 2611, 2612, 2613, 2634, 2635, 2636, 2637, 2638] with [hr.jumpdest]

end

end MlDsa44.Proofs.Decode
