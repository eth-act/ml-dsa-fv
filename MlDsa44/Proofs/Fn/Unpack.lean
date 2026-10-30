import MlDsa44.Proofs.Fn.UnpackZetas.UnpackMath
/-!
# `unpack`: one little-endian bit-packed coefficient from calldata

Yul: `unpack(off, i, c) -> v`; reads four bytes at `off + (i c) / 8`
little-endian, shifts by `(i c) mod 8` and masks `c` bits.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: the exact cost (one straight-line block).
namespace Gas

def unpack : Nat := 153

end Gas

/-- Coefficient `i` of the `c`-bit packing of the calldata field
`[off, off + n)`. -/
theorem unpack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.unpack ret tail) (m : ByteArray) {off n i c : Nat}
    (hc : 1 ≤ c ∧ c ≤ 18) (hfield : off + n ≤ s.executionEnv.calldata.size)
    (hi : (i + 1) * c ≤ 8 * n) :
    Call s Entry.unpack [wd off, wd i, wd c] ret tail m
      [wd (Fips204.bitsToInteger (s.executionEnv.calldata.extract off (off + n)) (i * c) c)]
      m Gas.unpack := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.unpack, Stack.leaf] at this; omega
  have := hs.calldataFits
  have := hr.small
  have hand : i * c &&& 7 < 8 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h2c : 2 ^ 1 ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc.1
  have h2c' : 2 ^ c ≤ 2 ^ 18 := Nat.pow_le_pow_right (by omega) hc.2
  have hic : i * c + c ≤ 8 * n := by rw [Nat.add_mul, Nat.one_mul] at hi; exact hi
  have h : Infra.Reach (callState s 3456 ([wd off, wd i, wd c, wd 0, wd ret] ++ tail) m)
      (callState s ret (wd (Fips204.bitsToInteger (s.executionEnv.calldata.extract off (off + n))
        (i * c) c) :: tail) m) 153 := by
    evm_reach [2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251,
      2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266,
      2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281,
      2282, 2283, 2284, 2285, 2286, 2287, 2288, 2289, 2290]
      with [hr.jumpdest, UnpackZetas.ofNat_byteAt_word,
        UnpackZetas.unpack_value s.executionEnv.calldata hc.2 hfield hic]
  rw [Infra.call_iff, Entry.unpack, Gas.unpack]
  exact h.of_eq (by simp) (by simp)

end MlDsa44.Proofs
