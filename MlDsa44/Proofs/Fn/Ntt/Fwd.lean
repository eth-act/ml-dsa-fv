import MlDsa44.Proofs.Fn.Ntt.Common
/-!
# `ntt(p)` (instructions 1987–2096)

Loop heads: outer `len` at pc 3111 (stack `len, m, p, ret`), middle `start` at
pc 3121 (`start, len, m, p, ret`), inner `j` at pc 3148
(`j, z, start, len, m, p, ret`). Layer `L` has `len = 128 / 2^L`, `2^L`
blocks, and `m = 2^L - 1` on entry; block `b` starts at `2 len b`.
-/

namespace MlDsa44.Proofs.NttProof

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.NttModel
open MlDsa44.Fips204 (Poly zetas)

set_option linter.unusedSectionVars false

theorem n_layer_facts : ∀ L < 8, 0 < 128 / 2 ^ L ∧ 128 / 2 ^ L ≤ 128 ∧
    2 * (128 / 2 ^ L) * 2 ^ L = 256 ∧ 2 ^ L - 1 + 2 ^ L < 256 ∧
    128 / 2 ^ L / 2 = 128 / 2 ^ (L + 1) ∧ 2 ^ L - 1 + 2 ^ L = 2 ^ (L + 1) - 1 := by
  decide

/-- Per-layer cost of `ntt`. -/
def nLayerCost (L : Nat) : Nat := 27 + 2 ^ L * (61 + (128 / 2 ^ L * 173 + 68)) + 54


section
variable {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (ht : tail.length ≤ 960)
  (haw : s.activeWords.toNat ≤ 18446744073709551616) {p : Nat}
  (hmem : p + 8192 + 32 ≤ 32 * s.activeWords.toNat) (hp : 10720 ≤ p)
include hs ht haw hmem hp

theorem n_entry (M : ByteArray) : Infra.Reach (callState s 3107 (wd p :: wd ret :: tail) M)
    (callState s 3111 (wd 128 :: wd 0 :: wd p :: wd ret :: tail) M) 6 := by
  evm_reach [1987, 1988, 1989]

theorem n_outer_in (M : ByteArray) {len m : Nat} (hlen : 0 < len) (hl : len ≤ 128) :
    Infra.Reach (callState s 3111 (wd len :: wd m :: wd p :: wd ret :: tail) M)
    (callState s 3121 (wd 0 :: wd len :: wd m :: wd p :: wd ret :: tail) M) 27 := by
  evm_reach [1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997]

theorem n_mid_in (M : ByteArray) {st len m : Nat} (hst : st < 256) (hm : m + 1 < 256) :
    Infra.Reach (callState s 3121 (wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
    (callState s 3148 (wd st :: wd (word M (2528 + (m + 1) * 32)) :: wd st :: wd len ::
      wd (m + 1) :: wd p :: wd ret :: tail) M) 61 := by
  evm_reach [1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011,
    2012, 2013, 2014, 2015, 2016]

theorem n_inner (M : ByteArray) {j z st len m : Nat} (hj : j < st + len) (hjl : j + len < 256)
    (hsl : st + len ≤ 256) (hz : z < 8380417) :
    Infra.Reach
      (callState s 3148 (wd j :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3148 (wd (j + 1) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail)
        (bflyMemN M p j len z)) 173 := by
  evm_reach [2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030,
    2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046,
    2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062,
    2063, 2064, 2065, 2066, 2067] with [addMod_q, mulMod_q, bflyMemN]

theorem n_inner_exit (M : ByteArray) {z st len m : Nat} (hsl : st + len ≤ 256) :
    Infra.Reach (callState s 3148
        (wd (st + len) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3121 (wd (st + len * 2) :: wd len :: wd m :: wd p :: wd ret :: tail) M) 68 := by
  evm_reach [2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2068, 2069, 2070, 2071, 2072,
    2073, 2074, 2075, 2076, 2077, 2078, 2079]

theorem n_mid_exit (M : ByteArray) {len m : Nat} (hl : len ≤ 128) :
    Infra.Reach (callState s 3121 (wd 256 :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3111 (wd (len / 2) :: wd m :: wd p :: wd ret :: tail) M) 54 := by
  evm_reach [1998, 1999, 2000, 2001, 2002, 2003, 2004, 2080, 2081, 2082, 2083, 2084, 2085, 2086,
    2087, 2088]

theorem n_outer_exit (M : ByteArray) {m : Nat} (hr : RetOK Stack.ntt ret tail) :
    Infra.Reach (callState s 3111 (wd 0 :: wd m :: wd p :: wd ret :: tail) M)
      (callState s ret tail M) 40 := by
  have := hr.small
  evm_reach [1990, 1991, 1992, 1993, 1994, 1995, 1996, 2089, 2090, 2091, 2092, 2093]
    with [hr.jumpdest]

/-- One block: `len` butterflies from `st` with twiddle `z`, then the inner-loop exit. -/
theorem n_block {m0 : ByteArray} {len st z m : Nat} (hlen : 0 < len) (hsl : st + 2 * len ≤ 256)
    (hz : z < 8380417) (M : ByteArray) (g : Poly) (hR : Rep m0 p M g) :
    ∃ M', Rep m0 p M' (blockN len (z : Int) g st len) ∧
      Infra.Reach
        (callState s 3148 (wd st :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
        (callState s 3121 (wd (st + len * 2) :: wd len :: wd m :: wd p :: wd ret :: tail) M')
        (len * 173 + 68) := by
  obtain ⟨M', hP, hReach⟩ := reach_iterU (c := 173)
    (S := fun k M => callState s 3148
      (wd (st + k) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
    (P := fun k M => Rep m0 p M (blockN len (z : Int) g st k)) len (fun k M hk hM => by
      refine ⟨bflyMemN M p (st + k) len z, ?_,
        (n_inner (ret := ret) hs ht haw hmem hp M (j := st + k) (by omega) (by omega) (by omega) hz).of_eq rfl
          (by rw [Nat.add_assoc])⟩
      simp only [blockN, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.one_mul] at hM ⊢
      exact rep_bflyN hM (by omega) hlen) M (by simpa [blockN] using hR)
  exact ⟨M', hP, ((hReach.of_eq (by simp) rfl).trans
    (n_inner_exit (ret := ret) hs ht haw hmem hp M' (z := z) (by omega))).mono (by omega)⟩

/-- One layer: `nb` blocks of length `len`, `m = m0` on entry. -/
theorem n_layer {m0 : ByteArray} (hz0 : ZetaTable m0) {len nb mb : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hnb : 2 * len * nb = 256) (hm : mb + nb < 256) (M : ByteArray) (g : Poly)
    (hR : Rep m0 p M g) :
    ∃ M', Rep m0 p M' (layerN len mb g nb) ∧
      Infra.Reach (callState s 3121 (wd 0 :: wd len :: wd mb :: wd p :: wd ret :: tail) M)
        (callState s 3121 (wd 256 :: wd len :: wd (mb + nb) :: wd p :: wd ret :: tail) M')
        (nb * (61 + (len * 173 + 68))) := by
  obtain ⟨M', hP, hReach⟩ := reach_iterU (c := 61 + (len * 173 + 68))
    (S := fun b M => callState s 3121
      (wd (2 * len * b) :: wd len :: wd (mb + b) :: wd p :: wd ret :: tail) M)
    (P := fun b M => Rep m0 p M (layerN len mb g b)) nb (fun b M hb hM => by
      have hle : 2 * len * (b + 1) ≤ 2 * len * nb := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at hle
      have hzt := zetaTable_of_rep hM hz0 (by simp only [ZETA, POLY]; omega) (mb + b + 1) (by omega)
      have hzl := zetas_lt (mb + b + 1)
      rw [← hzt] at hzl
      have hzq : word M (2528 + (mb + b + 1) * 32) < 8380417 := by
        rw [show 2528 + (mb + b + 1) * 32 = ZETA + 32 * (mb + b + 1) by simp only [ZETA]; omega]
        simp only [Fips204.q] at hzl; omega
      obtain ⟨M', hP', hR'⟩ := n_block (ret := ret) hs ht haw hmem hp (st := 2 * len * b) (m := mb + b + 1)
        hlen (by omega) hzq M _ hM
      refine ⟨M', ?_, ((n_mid_in (ret := ret) hs ht haw hmem hp M (st := 2 * len * b) (m := mb + b) (by omega)
        (by omega)).trans hR').of_eq rfl ?_⟩
      · rw [show 2528 + (mb + b + 1) * 32 = ZETA + 32 * (mb + b + 1) by simp only [ZETA]; omega,
          hzt] at hP'
        exact hP'
      · rw [show 2 * len * (b + 1) = 2 * len * b + len * 2 by rw [Nat.mul_succ]; omega,
          show mb + (b + 1) = mb + b + 1 by omega]) M hR
  refine ⟨M', hP, hReach.of_eq (by simp) ?_⟩
  rw [hnb]

theorem n_reach {m0 : ByteArray} (hz0 : ZetaTable m0) (hr : RetOK Stack.ntt ret tail) (g : Poly)
    (hR : Rep m0 p m0 g) :
    ∃ M', Rep m0 p M' (nttL g 8) ∧
      Infra.Reach (callState s 3107 (wd p :: wd ret :: tail) m0) (callState s ret tail M')
        210741 := by
  obtain ⟨M', hP, hReach⟩ := reach_iter (c := nLayerCost)
    (S := fun L M => callState s 3111
      (wd (128 / 2 ^ L) :: wd (2 ^ L - 1) :: wd p :: wd ret :: tail) M)
    (P := fun L M => Rep m0 p M (nttL g L)) 8 (fun L M hL hM => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := n_layer_facts L hL
      obtain ⟨M', hP', hR'⟩ := n_layer (ret := ret) hs ht haw hmem hp hz0 (mb := 2 ^ L - 1) h1 h2 h3 h4 M _ hM
      refine ⟨M', hP', ?_⟩
      have := ((n_outer_in (ret := ret) hs ht haw hmem hp M h1 h2).trans hR').trans
        (n_mid_exit (ret := ret) hs ht haw hmem hp M' h2)
      rw [h5, h6] at this
      exact this) m0 hR
  refine ⟨M', hP, ?_⟩
  have h0 := hReach.of_eq
    (s' := callState s 3111 (wd 128 :: wd 0 :: wd p :: wd ret :: tail) m0) (by simp) rfl
  have := ((n_entry (ret := ret) hs ht haw hmem hp m0).trans h0).trans
    (n_outer_exit (ret := ret) hs ht haw hmem hp M' hr)
  exact this.mono (by decide)

end

end MlDsa44.Proofs.NttProof
