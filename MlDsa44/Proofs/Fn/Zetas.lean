import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Fn.UnpackZetas.ZetaMem
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

/-- Exact: entry 6, per iteration 48 + `brv8` + 63, exit 39. -/
def initZetas : Nat := 256 * (brv8 + 111) + 45

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
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.initZetas, Stack.brv8, Stack.leaf] at this; omega
  have := hr.small
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : 2535 ≤ s.activeWords.toNat := hs.sized
  let I : Nat → State := fun j => callState s 3007
    (wd j :: wd (1753 ^ j % 8380417) :: wd ret :: tail) (UnpackZetas.zmem m j)
  have hentry : Infra.Reach (callState s 3003 (wd ret :: tail) m) (I 0) 6 := by
    simp only [I, UnpackZetas.zmem]
    evm_reach [1915, 1916, 1917]
  have hbody : ∀ j, j < 256 → Infra.Reach (I j) (I (j + 1)) (48 + Gas.brv8 + 63) := by
    intro j hj
    have hr8 := UnpackZetas.bitRev8_lt j hj
    have hpw : 1753 ^ j % 8380417 < 8380417 := Nat.mod_lt _ (by decide)
    have hmul : 1753 ^ j % 8380417 * 1753 % 8380417 = 1753 ^ (j + 1) % 8380417 := by
      rw [Nat.pow_succ, Nat.mul_mod, Nat.mod_mod, Nat.mul_mod (1753 ^ j)]
    have hA : Infra.Reach (I j) (callState s 2956
        (wd j :: wd 0 :: wd 3028 :: wd (1753 ^ j % 8380417) :: wd j ::
          wd (1753 ^ j % 8380417) :: wd ret :: tail) (UnpackZetas.zmem m j)) 48 := by
      simp only [I]
      evm_reach [1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930]
    have hcall := Infra.call_iff.mp (brv8_call hs
      (hr.callee (B' := Stack.brv8) (ret' := 3028)
        (extra := [wd (1753 ^ j % 8380417), wd j, wd (1753 ^ j % 8380417), wd ret])
        (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
      (UnpackZetas.zmem m j) hj)
    have hB : Infra.Reach (callState s 3028
        (wd (Fips204.bitRev8 j) :: wd (1753 ^ j % 8380417) :: wd j ::
          wd (1753 ^ j % 8380417) :: wd ret :: tail) (UnpackZetas.zmem m j)) (I (j + 1)) 63 := by
      simp only [I, UnpackZetas.zmem]
      evm_reach [1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943,
        1944, 1945, 1946, 1947, 1948, 1949] with [Infra.ofNat_mulMod, hmul]
    exact (hA.trans (hcall.of_eq (by simp [Entry.brv8]) (by simp))).trans hB
  have hexit : ∀ (pw : Nat) (M : ByteArray), Infra.Reach
      (callState s 3007 (wd 256 :: wd pw :: wd ret :: tail) M) (callState s ret tail M) 39 := by
    intro pw M
    evm_reach [1918, 1919, 1920, 1921, 1922, 1923, 1924, 1950, 1951, 1952, 1953]
      with [hr.jumpdest]
  refine ⟨UnpackZetas.zmem m 256, UnpackZetas.zmem_table m,
    UnpackZetas.zmem_frame m 256 le_rfl, ?_⟩
  have h := (hentry.trans (Infra.Reach.loop 256 hbody)).trans
    (hexit (1753 ^ 256 % 8380417) (UnpackZetas.zmem m 256))
  have hgas : 6 + 256 * (48 + Gas.brv8 + 63) + 39 ≤ Gas.initZetas := by
    clear * -; unfold Gas.initZetas; omega
  exact Infra.call_iff.mpr ((h.mono hgas).of_eq (by simp [Entry.initZetas]) (by simp))

end MlDsa44.Proofs
