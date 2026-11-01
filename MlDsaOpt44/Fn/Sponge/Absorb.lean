import MlDsaOpt44.Fn.Sponge.Lanes
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-!
# `absorb17`: five straight-line groups, one block lemma each
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem absorb_g0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (M : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    Reach (callState s 6705 (wd off :: wd ret :: tail) M)
      (callState s 6926 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((word M 0 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)
          (Data.Bytes.natToBytesPadded ((word M 32 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)
          (Data.Bytes.natToBytesPadded ((word M 64 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)
          (Data.Bytes.natToBytesPadded ((word M 96 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96)) 256 := by
  have := hr.depth; simp only [Stack.absorb17, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415, 2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431, 2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465, 2466, 2467] with [word_mstore_disjoint, bsw8_fold, bsw16_fold, bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem absorb_g1 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (M : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    Reach (callState s 6926 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) M)
      (callState s 7024 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((word M 128 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)
          (Data.Bytes.natToBytesPadded ((word M 160 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)
          (Data.Bytes.natToBytesPadded ((word M 192 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)
          (Data.Bytes.natToBytesPadded ((word M 224 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224)) 248 := by
  have := hr.depth; simp only [Stack.absorb17, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479, 2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547] with [word_mstore_disjoint, bsw8_fold, bsw16_fold, bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem absorb_g2 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (M : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    Reach (callState s 7024 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) M)
      (callState s 7130 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((word M 256 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)
          (Data.Bytes.natToBytesPadded ((word M 288 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 288)
          (Data.Bytes.natToBytesPadded ((word M 320 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 320)
          (Data.Bytes.natToBytesPadded ((word M 352 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 352)) 248 := by
  have := hr.depth; simp only [Stack.absorb17, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607, 2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627] with [word_mstore_disjoint, bsw8_fold, bsw16_fold, bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem absorb_g3 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (M : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    Reach (callState s 7130 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) M)
      (callState s 7236 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((word M 384 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 384)
          (Data.Bytes.natToBytesPadded ((word M 416 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 416)
          (Data.Bytes.natToBytesPadded ((word M 448 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 448)
          (Data.Bytes.natToBytesPadded ((word M 480 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 480)) 248 := by
  have := hr.depth; simp only [Stack.absorb17, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639, 2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655, 2656, 2657, 2658, 2659, 2660, 2661, 2662, 2663, 2664, 2665, 2666, 2667, 2668, 2669, 2670, 2671, 2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687, 2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707] with [word_mstore_disjoint, bsw8_fold, bsw16_fold, bsw32_fold, bswapNet_fold]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem absorb_g4 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (M : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    Reach (callState s 7236 (wd 0x01000000000000000100000000000000010000000000000001 :: wd 0xffffffffffffffff :: wd 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff :: wd 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff :: wd 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff :: wd off :: wd ret :: tail) M)
      (callState s ret tail (MachineState.writeBytes M
          (Data.Bytes.natToBytesPadded ((word M 512 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (128 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512)) 160 := by
  have := hr.depth; simp only [Stack.absorb17, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760] with [word_mstore_disjoint, bsw8_fold, bsw16_fold, bsw32_fold, bswapNet_fold, hj]

theorem absorb_A_lt (m cd : ByteArray) (off x : Nat) :
    word m (32 * x) ^^^ rep (le64 cd (off + 8 * x)) < 2 ^ 256 :=
  Nat.xor_lt_two_pow (word_lt _ _) (rep_lt (le64_lt' _ _))

set_option maxHeartbeats 4000000 in
theorem absorb17_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (m : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if x < 17 then word m (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(KS, KS + 544)] ∧
      Call s Entry.absorb17 [wd off] ret tail m [] m' Gas.absorb17 := by
  have h0 : (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0) 0 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 0)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0) 32 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 32)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0) 64 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 64)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0) 96 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata off))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 96) = storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4 := by
    conv_rhs => rw [storeWords_succ, storeWords_succ, storeWords_succ, storeWords_succ]
    refine wbc (wbc (wbc (wbc (rfl) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    · exact absorb_lane (x := 0) (b := off) 0 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext0 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 1) (b := off) 1 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext1 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 2) (b := off) 2 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext2 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 3) (b := off) 3 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext3 _)
    · norm_num
  have r0 := absorb_g0 hs hr (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 0) hoff
  rw [h0] at r0
  have h1 : (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4) 128 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 128)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4) 160 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 160)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4) 192 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 192)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4) 224 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (32 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 224) = storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8 := by
    conv_rhs => rw [storeWords_succ, storeWords_succ, storeWords_succ, storeWords_succ]
    refine wbc (wbc (wbc (wbc (rfl) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    · exact absorb_lane (x := 4) (b := 32 + off) 0 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext0 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 5) (b := 32 + off) 1 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext1 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 6) (b := 32 + off) 2 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext2 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 7) (b := 32 + off) 3 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext3 _)
    · norm_num
  have r1 := absorb_g1 hs hr (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 4) hoff
  rw [h1] at r1
  have h2 : (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8) 256 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 256)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8) 288 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 288)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8) 320 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 320)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8) 352 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (64 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 352) = storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12 := by
    conv_rhs => rw [storeWords_succ, storeWords_succ, storeWords_succ, storeWords_succ]
    refine wbc (wbc (wbc (wbc (rfl) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    · exact absorb_lane (x := 8) (b := 64 + off) 0 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext0 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 9) (b := 64 + off) 1 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext1 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 10) (b := 64 + off) 2 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext2 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 11) (b := 64 + off) 3 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext3 _)
    · norm_num
  have r2 := absorb_g2 hs hr (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 8) hoff
  rw [h2] at r2
  have h3 : (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12) 384 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 384)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12) 416 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 340282366920938463463374607431768211456)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 416)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12) 448 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 18446744073709551616)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 448)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12) 480 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (18446744073709551615 &&& bswapNet (word s.executionEnv.calldata (96 + off)))) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 480) = storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 16 := by
    conv_rhs => rw [storeWords_succ, storeWords_succ, storeWords_succ, storeWords_succ]
    refine wbc (wbc (wbc (wbc (rfl) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    · exact absorb_lane (x := 12) (b := 96 + off) 0 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext0 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 13) (b := 96 + off) 1 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext1 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 14) (b := 96 + off) 2 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext2 (bswapNet_lt _))
    · norm_num
    · exact absorb_lane (x := 15) (b := 96 + off) 3 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext3 _)
    · norm_num
  have r3 := absorb_g3 hs hr (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 12) hoff
  rw [h3] at r3
  have h4 : (MachineState.writeBytes (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 16)
          (Data.Bytes.natToBytesPadded ((word (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 16) 512 ^^^ 6277101735386680764176071790128604879584176795969512275969 * (bswapNet (word s.executionEnv.calldata (128 + off)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 / 6277101735386680763835789423207666416102355444464034512896)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936) 32) 512) = storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 17 := by
    conv_rhs => rw [storeWords_succ]
    refine wbc (rfl) ?_ ?_
    · exact absorb_lane (x := 16) (b := 128 + off) 0 (by norm_num) (word_storeWords_out (Or.inr (by norm_num))) (by omega) _ (ext0 (bswapNet_lt _))
    · norm_num
  have r4 := absorb_g4 hs hr (storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 16) hoff
  rw [h4] at r4
  refine ⟨storeWords m 0 (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))) 17, fun x hx => ?_,
    storeWords_mono_frame (by simp [KS]) (by simp [KS]), ?_⟩
  · simp only [KS, Nat.zero_add]
    split
    · have h := word_storeWords_get (m := m) (base := 0) (k := 17) (i := x)
        (v := (fun x => word m (32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x)))) (absorb_A_lt m s.executionEnv.calldata off x) (by omega)
      beta_reduce at h
      rw [Nat.zero_add] at h
      exact h
    · exact word_storeWords_out (Or.inr (by omega))
  · rw [call_iff, Entry.absorb17, Gas.absorb17]
    exact (((r0.trans r1).trans r2).trans r3).trans r4

end MlDsaOpt44.Proofs.WP4
