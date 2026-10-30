import MlDsa44.Proofs.Infra
/-!
# `zeroPoly`, `ntt`, `nttInv`

Yul:
* `zeroPoly(p)`: 256 zero words at `p`;
* `ntt(p)`: FIPS 204 Algorithm 41 in place, butterflies with
  `mulmod`/`addmod`, `zetas[m]` read from `ZETA`;
* `nttInv(p)`: Algorithm 42 in place with `z = q − zetas[m]`, then the
  scaling by `256⁻¹ = 8347681`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def zeroPoly : Nat := 18218

def ntt : Nat := 210741

def nttInv : Nat := 236376

end Gas

theorem zeroPoly_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.zeroPoly ret tail) (m : ByteArray) {p : Nat}
    (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p Fips204.zeroPoly ∧ FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.zeroPoly [wd p] ret tail m [] m' Gas.zeroPoly := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.zeroPoly, Stack.leaf] at this; omega
  have := hr.small
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [POLY] at hmem
  -- memory after `j` iterations: words `0 … j-1` of the polynomial zeroed
  let mem : Nat → ByteArray := Infra.storeWords m p (fun _ => 0)
  let I : Nat → State := fun j => callState s 3069 (wd j :: wd p :: wd ret :: tail) (mem j)
  have hentry : Infra.Reach (callState s 3067 (wd p :: wd ret :: tail) m) (I 0) 3 := by
    simp only [I, mem, Infra.storeWords_zero]
    evm_reach [1957, 1958]
  have hbody : ∀ j, j < 256 → Infra.Reach (I j) (I (j + 1)) 71 := by
    intro j hj
    simp only [I, mem]
    evm_reach [1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979] with [Infra.storeWords_succ]
  -- stated for an abstract memory: the kernel must never unfold `mem 256`
  have hexit : ∀ M, Infra.Reach (callState s 3069 (wd 256 :: wd p :: wd ret :: tail) M)
      (callState s ret tail M) 39 := by
    intro M
    evm_reach [1959, 1960, 1961, 1962, 1963, 1964, 1965, 1980, 1981, 1982, 1983] with [hr.jumpdest]
  refine ⟨mem 256, ⟨by simp [Fips204.zeroPoly], fun i hi => ?_⟩, ?_, ?_⟩
  · rw [Infra.word_storeWords (by norm_num) 256 hi]
    simp [Fips204.zeroPoly, hi]
  · simpa [POLY] using Infra.FrameExcept.storeWords m p (fun _ => 0) 256
  · rw [Infra.call_iff, Entry.zeroPoly, Gas.zeroPoly]
    have h := (hentry.trans (Infra.Reach.loop 256 hbody)).trans (hexit (mem 256))
    exact (h.mono (by norm_num)).of_eq (by simp) (by simp)

theorem ntt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) {m : ByteArray} {p : Nat} {f : Fips204.Poly}
    (hf : PolyAt m p f) (hred : Reduced f) (hz : ZetaTable m)
    (hp : ZETA + POLY ≤ p) (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p (Fips204.ntt f) ∧ Reduced (Fips204.ntt f) ∧
      FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.ntt [wd p] ret tail m [] m' Gas.ntt := by
  sorry

theorem nttInv_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.nttInv ret tail) {m : ByteArray} {p : Nat} {f : Fips204.Poly}
    (hf : PolyAt m p f) (hred : Reduced f) (hz : ZetaTable m)
    (hp : ZETA + POLY ≤ p) (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p (Fips204.nttInv f) ∧ Reduced (Fips204.nttInv f) ∧
      FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.nttInv [wd p] ret tail m [] m' Gas.nttInv := by
  sorry

end MlDsa44.Proofs
