import MlDsa44.Proofs.Fn.Ntt.Common
/-!
# `nttInv(p)` (instructions 2097–2238)

Loop heads: outer `len` at pc 3261 (stack `len, m, p, ret`), middle `start` at
pc 3273 (`start, len, m, p, ret`), inner `j` at pc 3305
(`j, z, start, len, m, p, ret`), scaling `j` at pc 3405 (`j, m, p, ret`).
Layer `L` has `len = 2^L`, `128 / 2^L` blocks and `m = 2^(8-L)` on entry;
block `b` starts at `2 len b` and uses `z = q - zetas[m - b - 1]`.
-/

namespace MlDsa44.Proofs.NttProof

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.NttModel
open MlDsa44.Fips204 (Poly zetas)

set_option linter.unusedSectionVars false

theorem i_layer_facts : ∀ L < 8, 0 < 2 ^ L ∧ 2 ^ L ≤ 128 ∧ 2 * 2 ^ L * (128 / 2 ^ L) = 256 ∧
    128 / 2 ^ L ≤ 2 ^ (8 - L) ∧ 2 ^ (8 - L) ≤ 256 ∧ 2 ^ L * 2 = 2 ^ (L + 1) ∧
    2 ^ (8 - L) - 128 / 2 ^ L = 2 ^ (8 - (L + 1)) := by
  decide

/-- Per-layer cost of `nttInv`. -/
def iLayerCost (L : Nat) : Nat := 28 + 128 / 2 ^ L * (67 + (2 ^ L * 173 + 68)) + 54

section
variable {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256} (ht : tail.length ≤ 960)
  (haw : s.activeWords.toNat ≤ 18446744073709551616) {p : Nat}
  (hmem : p + 8192 + 32 ≤ 32 * s.activeWords.toNat) (hp : 10720 ≤ p)
include hs ht haw hmem hp

theorem i_entry (M : ByteArray) : Infra.Reach (callState s 3255 (wd p :: wd ret :: tail) M)
    (callState s 3261 (wd 1 :: wd 256 :: wd p :: wd ret :: tail) M) 7 := by
  evm_reach [2097, 2098, 2099]

theorem i_outer_in (M : ByteArray) {len m : Nat} (hl : len < 256) :
    Infra.Reach (callState s 3261 (wd len :: wd m :: wd p :: wd ret :: tail) M)
    (callState s 3273 (wd 0 :: wd len :: wd m :: wd p :: wd ret :: tail) M) 28 := by
  evm_reach [2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107]

set_option opt.reflect.enabled false in
theorem i_mid_in (M : ByteArray) {st len k : Nat} (hst : st < 256) (hk : k < 256)
    (hzq : word M (2528 + k * 32) < 8380417) :
    Infra.Reach (callState s 3273 (wd st :: wd len :: wd (k + 1) :: wd p :: wd ret :: tail) M)
    (callState s 3305 (wd st :: wd (8380417 - word M (2528 + k * 32)) :: wd st :: wd len ::
      wd k :: wd p :: wd ret :: tail) M) 67 := by
  evm_reach [2108, 2109, 2110, 2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121,
    2122, 2123, 2124, 2125, 2126, 2127, 2128] with [Nat.add_sub_cancel]

theorem i_inner (M : ByteArray) {j z st len m : Nat} (hj : j < st + len) (hjl : j + len < 256)
    (hsl : st + len ≤ 256) (hz : z ≤ 8380417)
    (hu : word M (p + j * 32 + len * 32) < 8380417) :
    Infra.Reach
      (callState s 3305 (wd j :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3305 (wd (j + 1) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail)
        (bflyMemI M p j len z)) 173 := by
  evm_reach [2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142,
    2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158,
    2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174,
    2175, 2176, 2177, 2178, 2179] with [addMod_q, mulMod_q, bflyMemI]

theorem i_inner_exit (M : ByteArray) {z st len m : Nat} (hsl : st + len ≤ 256) :
    Infra.Reach (callState s 3305
        (wd (st + len) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3273 (wd (st + len * 2) :: wd len :: wd m :: wd p :: wd ret :: tail) M) 68 := by
  evm_reach [2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2180, 2181, 2182, 2183, 2184,
    2185, 2186, 2187, 2188, 2189, 2190, 2191]

theorem i_mid_exit (M : ByteArray) {len m : Nat} :
    Infra.Reach (callState s 3273 (wd 256 :: wd len :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3261 (wd (len * 2) :: wd m :: wd p :: wd ret :: tail) M) 54 := by
  evm_reach [2108, 2109, 2110, 2111, 2112, 2113, 2114, 2192, 2193, 2194, 2195, 2196, 2197, 2198,
    2199, 2200]

theorem i_outer_exit (M : ByteArray) {m : Nat} :
    Infra.Reach (callState s 3261 (wd 256 :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3405 (wd 0 :: wd m :: wd p :: wd ret :: tail) M) 31 := by
  evm_reach [2100, 2101, 2102, 2103, 2104, 2105, 2106, 2201, 2202, 2203]

theorem i_sc (M : ByteArray) {j m : Nat} (hj : j < 256) :
    Infra.Reach (callState s 3405 (wd j :: wd m :: wd p :: wd ret :: tail) M)
      (callState s 3405 (wd (j + 1) :: wd m :: wd p :: wd ret :: tail) (scMem M p j)) 94 := by
  evm_reach [2204, 2205, 2206, 2207, 2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217,
    2218, 2219, 2220, 2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230]
    with [mulMod_q, scMem]

theorem i_sc_exit (M : ByteArray) {m : Nat} (hr : RetOK Stack.nttInv ret tail) :
    Infra.Reach (callState s 3405 (wd 256 :: wd m :: wd p :: wd ret :: tail) M)
      (callState s ret tail M) 41 := by
  have := hr.small
  evm_reach [2204, 2205, 2206, 2207, 2208, 2209, 2210, 2231, 2232, 2233, 2234, 2235]
    with [hr.jumpdest]

/-- One block: `len` butterflies from `st` with twiddle `z`, then the inner-loop exit. -/
theorem i_block {m0 : ByteArray} {len st z m : Nat} {zI : Int} (hlen : 0 < len)
    (hsl : st + 2 * len ≤ 256) (hz : z ≤ 8380417) (hzI : (z : Int) % 8380417 = zI % 8380417)
    (M : ByteArray) (g : Poly) (hR : Rep m0 p M g) :
    ∃ M', Rep m0 p M' (blockI len zI g st len) ∧
      Infra.Reach
        (callState s 3305 (wd st :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
        (callState s 3273 (wd (st + len * 2) :: wd len :: wd m :: wd p :: wd ret :: tail) M')
        (len * 173 + 68) := by
  obtain ⟨M', hP, hReach⟩ := reach_iterU (c := 173)
    (S := fun k M => callState s 3305
      (wd (st + k) :: wd z :: wd st :: wd len :: wd m :: wd p :: wd ret :: tail) M)
    (P := fun k M => Rep m0 p M (blockI len zI g st k)) len (fun k M hk hM => by
      have hu := (rep_word hM (i := st + k + len) (by omega)).2
      rw [show p + (st + k + len) * 32 = p + (st + k) * 32 + len * 32 by omega] at hu
      refine ⟨bflyMemI M p (st + k) len z, ?_,
        (i_inner (ret := ret) hs ht haw hmem hp M (j := st + k) (by omega) (by omega) (by omega) hz
          hu).of_eq rfl (by rw [Nat.add_assoc])⟩
      simp only [blockI, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.one_mul] at hM ⊢
      exact rep_bflyI hM hzI (by omega) hlen) M (by simpa [blockI] using hR)
  exact ⟨M', hP, ((hReach.of_eq (by simp) rfl).trans
    (i_inner_exit (ret := ret) hs ht haw hmem hp M' (z := z) (by omega))).mono (by omega)⟩

/-- One layer: `nb` blocks of length `len`, `m = mb` on entry. -/
theorem i_layer {m0 : ByteArray} (hz0 : ZetaTable m0) {len nb mb : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hnb : 2 * len * nb = 256) (hm : nb ≤ mb) (hmb : mb ≤ 256) (M : ByteArray)
    (g : Poly) (hR : Rep m0 p M g) :
    ∃ M', Rep m0 p M' (layerI len mb g nb) ∧
      Infra.Reach (callState s 3273 (wd 0 :: wd len :: wd mb :: wd p :: wd ret :: tail) M)
        (callState s 3273 (wd 256 :: wd len :: wd (mb - nb) :: wd p :: wd ret :: tail) M')
        (nb * (67 + (len * 173 + 68))) := by
  obtain ⟨M', hP, hReach⟩ := reach_iterU (c := 67 + (len * 173 + 68))
    (S := fun b M => callState s 3273
      (wd (2 * len * b) :: wd len :: wd (mb - b) :: wd p :: wd ret :: tail) M)
    (P := fun b M => Rep m0 p M (layerI len mb g b)) nb (fun b M hb hM => by
      have hle : 2 * len * (b + 1) ≤ 2 * len * nb := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at hle
      have hzt := zetaTable_of_rep hM hz0 (by simp only [ZETA, POLY]; omega) (mb - b - 1)
        (by omega)
      have hzl := zetas_lt (mb - b - 1)
      rw [← hzt] at hzl
      have haddr : 2528 + (mb - b - 1) * 32 = ZETA + 32 * (mb - b - 1) := by
        simp only [ZETA]; omega
      have hzq : word M (2528 + (mb - b - 1) * 32) < 8380417 := by
        rw [haddr]; simp only [Fips204.q] at hzl; omega
      have hzI : ((8380417 - word M (2528 + (mb - b - 1) * 32) : Nat) : Int) % 8380417 =
          (-zetas (mb - b - 1)) % 8380417 := by
        rw [← hzt, ← haddr, Nat.cast_sub (by omega)]
        push_cast
        omega
      obtain ⟨M', hP', hR'⟩ := i_block (ret := ret) hs ht haw hmem hp (st := 2 * len * b)
        (m := mb - b - 1) hlen (by omega) (by omega) hzI M _ hM
      have hin := i_mid_in (ret := ret) hs ht haw hmem hp M (st := 2 * len * b) (len := len)
        (k := mb - b - 1) (by omega) (by omega) hzq
      rw [show mb - b - 1 + 1 = mb - b by omega] at hin
      refine ⟨M', hP', (hin.trans hR').of_eq rfl ?_⟩
      rw [show 2 * len * (b + 1) = 2 * len * b + len * 2 by rw [Nat.mul_succ]; omega,
        show mb - (b + 1) = mb - b - 1 by omega]) M hR
  refine ⟨M', hP, hReach.of_eq (by simp) ?_⟩
  rw [hnb]

set_option maxRecDepth 20000 in
theorem i_reach {m0 : ByteArray} (hz0 : ZetaTable m0) (hr : RetOK Stack.nttInv ret tail)
    (g : Poly) (hR : Rep m0 p m0 g) :
    ∃ M', Rep m0 p M' (scaleI (nttIL g 8) 256) ∧
      Infra.Reach (callState s 3255 (wd p :: wd ret :: tail) m0) (callState s ret tail M')
        236376 := by
  obtain ⟨M₁, hP₁, hReach₁⟩ := reach_iter (c := iLayerCost)
    (S := fun L M => callState s 3261
      (wd (2 ^ L) :: wd (2 ^ (8 - L)) :: wd p :: wd ret :: tail) M)
    (P := fun L M => Rep m0 p M (nttIL g L)) 8 (fun L M hL hM => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := i_layer_facts L hL
      obtain ⟨M', hP', hR'⟩ := i_layer (ret := ret) hs ht haw hmem hp hz0 (mb := 2 ^ (8 - L))
        h1 h2 h3 h4 h5 M _ hM
      refine ⟨M', hP', ?_⟩
      have := ((i_outer_in (ret := ret) hs ht haw hmem hp M (m := 2 ^ (8 - L)) (by omega)).trans
        hR').trans (i_mid_exit (ret := ret) hs ht haw hmem hp M')
      rw [h6, h7] at this
      exact this) m0 hR
  obtain ⟨M₂, hP₂, hReach₂⟩ := reach_iterU (c := 94)
    (S := fun j M => callState s 3405 (wd j :: wd 1 :: wd p :: wd ret :: tail) M)
    (P := fun j M => Rep m0 p M (scaleI (nttIL g 8) j)) 256 (fun j M hj hM => by
      refine ⟨scMem M p j, ?_, i_sc (ret := ret) hs ht haw hmem hp M hj⟩
      simp only [scaleI, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.one_mul, Nat.zero_add] at hM ⊢
      exact rep_sc hM hj) M₁ (by simpa [scaleI] using hP₁)
  refine ⟨M₂, hP₂, ?_⟩
  have h0 := hReach₁.of_eq
    (s' := callState s 3261 (wd 1 :: wd 256 :: wd p :: wd ret :: tail) m0) (by simp)
    (t' := callState s 3261 (wd 256 :: wd 1 :: wd p :: wd ret :: tail) M₁) (by simp)
  have := ((((i_entry (ret := ret) hs ht haw hmem hp m0).trans h0).trans
    (i_outer_exit (ret := ret) hs ht haw hmem hp M₁)).trans hReach₂).trans
    (i_sc_exit (ret := ret) hs ht haw hmem hp M₂ hr)
  exact this.mono (by decide)

end

end MlDsa44.Proofs.NttProof
