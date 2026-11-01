import MlDsa44.Proofs.Fn.UnpackZetas.Bytes
set_option warningAsError true
set_option linter.unusedVariables false
/-!
# `sampleInBall`: straight-line blocks

Loop head at instruction 2385 (pc 3653), stack `p :: i :: good :: ret :: tail`.
-/

namespace MlDsa44.Proofs.Sampling

open EvmSemantics
open EvmSemantics.EVM

theorem land_seven (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

/-- Loop-head state. -/
abbrev ballSt (s : State) (ret : Nat) (tail : List UInt256) (p i : Nat) (M : ByteArray) :
    State :=
  callState s 3653 (wd p :: wd i :: wd 0 :: wd ret :: tail) M

/-- Memory after `CH[i] := CH[j]`. -/
abbrev ballCopy (M : ByteArray) (i j : Nat) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (43488 + j * 32)) 32)
    (43488 + i * 32)

/-- Memory after `CH[i] := CH[j]; CH[j] := 1 + sg (q - 2)`. -/
abbrev ballWrite (M : ByteArray) (i j sg : Nat) : ByteArray :=
  MachineState.writeBytes (ballCopy M i j) (Data.Bytes.natToBytesPadded (1 + sg * 8380415) 32)
    (43488 + j * 32)

theorem ball_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Infra.Reach (callState s 3637 (wd 0 :: wd ret :: tail) M)
      (callState s 3067 (wd 43488 :: wd 3648 :: wd 0 :: wd ret :: tail) M) 18 := by
  evm_reach [2377, 2378, 2379, 2380, 2381]

theorem ball_start {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (M : ByteArray) :
    Infra.Reach (callState s 3648 (wd 0 :: wd ret :: tail) M) (ballSt s ret tail 8 217 M) 7 := by
  evm_reach [2382, 2383, 2384]

theorem ball_accept {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsized : 2535 ≤ s.activeWords.toNat)
    (M : ByteArray) (p i : Nat) (hp : p < 272) (hi : i < 256) (hi' : 217 ≤ i)
    (j : Nat) (hj : byteAt M (77280 + p + 0) = j) (hji : j ≤ i)
    (b : Nat) (hb : byteAt (ballCopy M i j) (77280 + (i - 217) / 8 + 0) = b) (hb' : b < 256)
    (sg : Nat) (hsg : b / 2 ^ ((i - 217) % 8) &&& 1 = sg) (hsg' : sg ≤ 1) :
    Infra.Reach (ballSt s ret tail p i M) (ballSt s ret tail (p + 1) (i + 1) (ballWrite M i j sg))
      256 := by
  simp only [ballCopy] at hb
  evm_reach [2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415, 2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431, 2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465] with [UnpackZetas.ofNat_byteAt_word, land_seven, hj, hb, hsg]

theorem ball_reject {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsized : 2535 ≤ s.activeWords.toNat)
    (M : ByteArray) (p i : Nat) (hp : p < 272) (hi : i < 256)
    (j : Nat) (hj : byteAt M (77280 + p + 0) = j) (hji : i < j) (hj' : j < 256) :
    Infra.Reach (ballSt s ret tail p i M) (ballSt s ret tail (p + 1) i M) 119 := by
  evm_reach [2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399, 2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465] with [UnpackZetas.ofNat_byteAt_word, hj]

theorem ball_skip {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960)
    (M : ByteArray) (p i : Nat) (hp : p < 272) (hi : 256 ≤ i) (hi' : i ≤ 256) :
    Infra.Reach (ballSt s ret tail p i M) (ballSt s ret tail (p + 1) i M) 77 := by
  evm_reach [2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465]

theorem ball_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) {B : Nat} (hr : RetOK B ret tail) (M : ByteArray) (i : Nat) (hi : i ≤ 256) :
    Infra.Reach (ballSt s ret tail 272 i M)
      (callState s ret (wd (if i < 256 then 0 else 1) :: tail) M) 59 := by
  have := hr.small
  evm_reach [2385, 2386, 2387, 2388, 2389, 2390, 2391, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476] with [hr.jumpdest]
  by_cases h : i < 256 <;>
    simp only [h, ↓reduceIte, Nat.reduceMod, Nat.one_ne_zero]

end MlDsa44.Proofs.Sampling
