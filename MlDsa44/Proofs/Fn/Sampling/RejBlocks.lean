import MlDsa44.Proofs.Fn.UnpackZetas.Bytes
set_option warningAsError true
set_option linter.unusedVariables false
/-!
# `rejSample`: straight-line blocks

Loop head at instruction 2297 (pc 3526), stack `t :: jj :: dst :: good :: ret :: tail`.
-/

namespace MlDsa44.Proofs.Sampling

open EvmSemantics
open EvmSemantics.EVM

/-- The candidate coefficient as the bytecode computes it from the word at `XOF + 3 t`. -/
abbrev rejZ (M : ByteArray) (t : Nat) : Nat :=
  byteAt M (77280 + 3 * t + 0) ||| byteAt M (77280 + 3 * t + 1) * 256 |||
    (byteAt M (77280 + 3 * t + 2) &&& 127) * 65536

/-- Loop-head state. -/
abbrev rejSt (s : State) (ret : Nat) (tail : List UInt256) (dst t jj : Nat) (M : ByteArray) :
    State :=
  callState s 3526 (wd t :: wd jj :: wd dst :: wd 0 :: wd ret :: tail) M

theorem rej_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (dst : Nat) (M : ByteArray) :
    Infra.Reach (callState s 3523 (wd dst :: wd 0 :: wd ret :: tail) M)
      (rejSt s ret tail dst 0 0 M) 5 := by
  evm_reach [2294, 2295, 2296]

theorem rej_accept {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsized : 2535 ≤ s.activeWords.toNat)
    {dst : Nat} (hdst : dst + 8192 + 32 ≤ 32 * s.activeWords.toNat)
    (M : ByteArray) (t jj z : Nat) (ht : t < 336) (hjj : jj < 256)
    (hz : rejZ M t = z) (hzq : z < 8380417) :
    Infra.Reach (rejSt s ret tail dst t jj M)
      (rejSt s ret tail dst (t + 1) (jj + 1)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded z 32) (dst + jj * 32))) 212 := by
  simp only [rejZ] at hz
  evm_reach [2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319, 2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2346, 2347, 2348, 2349, 2350, 2351, 2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361] with [UnpackZetas.ofNat_byteAt_word, hz]

theorem rej_reject {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsized : 2535 ≤ s.activeWords.toNat)
    {dst : Nat} (M : ByteArray) (t jj z : Nat) (ht : t < 336) (hjj : jj < 256)
    (hz : rejZ M t = z) (hzq : ¬ z < 8380417) (hz' : z < 2 ^ 24) :
    Infra.Reach (rejSt s ret tail dst t jj M) (rejSt s ret tail dst (t + 1) jj M) 177 := by
  simp only [rejZ] at hz
  evm_reach [2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319, 2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2351, 2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361] with [UnpackZetas.ofNat_byteAt_word, hz]

theorem rej_skip {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960)
    {dst : Nat} (M : ByteArray) (t jj : Nat) (ht : t < 336) (hjj : 256 ≤ jj) (hjj' : jj ≤ 256) :
    Infra.Reach (rejSt s ret tail dst t jj M) (rejSt s ret tail dst (t + 1) jj M) 77 := by
  evm_reach [2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361]

theorem rej_exit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) {B : Nat} (hr : RetOK B ret tail)
    {dst : Nat} (M : ByteArray) (jj : Nat) (hjj' : jj ≤ 256) :
    Infra.Reach (rejSt s ret tail dst 336 jj M)
      (callState s ret (wd (if jj < 256 then 0 else 1) :: tail) M) 61 := by
  have := hr.small
  evm_reach [2297, 2298, 2299, 2300, 2301, 2302, 2303, 2362, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2370, 2371, 2372, 2373] with [hr.jumpdest]
  by_cases h : jj < 256 <;>
    simp only [h, ↓reduceIte, Nat.reduceMod, Nat.one_ne_zero]

end MlDsa44.Proofs.Sampling
