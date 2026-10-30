import MlDsa44.Proofs.Infra
/-!
# `brv8` and `initZetas`

Yul:
* `brv8(i) -> r`: eight-step bit reversal;
* `initZetas()`: `mstore(ZETA + 32 brv8(i), ζ^i mod q)` for `i < 256`,
  so every `zetas[k] = ζ^BitRev8(k) mod q` lands at `ZETA + 32 k`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def brv8 : Nat := 757

def initZetas : Nat := 256 * (brv8 + 150) + 100

end Gas

theorem brv8_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.brv8 ret tail) (m : ByteArray) {i : Nat} (hi : i < 256) :
    Call s Entry.brv8 [wd i] ret tail m [wd (Fips204.bitRev8 i)] m Gas.brv8 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.brv8, Stack.leaf] at this; omega
  have := hr.small
  -- the accumulator after `j` iterations of the bit loop
  have hacc : ∀ j, j ≤ 8 →
      (List.range j).foldl (fun a k => a ||| (i / 2 ^ k &&& 1) * 2 ^ (7 - k)) 0 < 256 := by
    have : ∀ i, i < 256 → ∀ j, j ≤ 8 →
        (List.range j).foldl (fun a k => a ||| (i / 2 ^ k &&& 1) * 2 ^ (7 - k)) 0 < 256 := by
      decide +kernel
    exact this i hi
  have hkey : (List.range 8).foldl (fun a k => a ||| (i / 2 ^ k &&& 1) * 2 ^ (7 - k)) 0 =
      Fips204.bitRev8 i := by
    have : ∀ i, i < 256 → (List.range 8).foldl (fun a k => a ||| (i / 2 ^ k &&& 1) * 2 ^ (7 - k)) 0 =
        Fips204.bitRev8 i := by
      decide +kernel
    exact this i hi
  let I : Nat → State := fun j => callState s 2958
    (wd j :: wd i ::
      wd ((List.range j).foldl (fun a k => a ||| (i / 2 ^ k &&& 1) * 2 ^ (7 - k)) 0) ::
      wd ret :: tail) m
  have hentry : Infra.Reach (callState s 2956 ([wd i, wd 0, wd ret] ++ tail) m) (I 0) 3 := by
    simp only [I, List.range_zero, List.foldl_nil]
    evm_reach [1878, 1879]
  have hbody : ∀ j, j < 8 → Infra.Reach (I j) (I (j + 1)) 89 := by
    intro j hj
    have := hacc j (by omega)
    simp only [I]
    evm_reach [1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906]
      with [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hexit : Infra.Reach (I 8) (callState s ret (wd (Fips204.bitRev8 i) :: tail) m) 42 := by
    have := hacc 8 le_rfl
    simp only [I]
    evm_reach [1880, 1881, 1882, 1883, 1884, 1885, 1886, 1907, 1908, 1909, 1910, 1911] with [hr.jumpdest, hkey]
  rw [Infra.call_iff, Entry.brv8, Gas.brv8]
  have h := (hentry.trans (Infra.Reach.loop 8 hbody)).trans hexit
  exact (h.mono (by norm_num)).of_eq (by simp) (by simp)

theorem initZetas_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.initZetas ret tail) (m : ByteArray) :
    ∃ m', ZetaTable m' ∧ FrameExcept m m' [(ZETA, ZETA + POLY)] ∧
      Call s Entry.initZetas [] ret tail m [] m' Gas.initZetas := by
  sorry

end MlDsa44.Proofs
