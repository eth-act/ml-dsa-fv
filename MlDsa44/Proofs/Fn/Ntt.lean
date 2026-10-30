import MlDsa44.Proofs.Layout
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
    (hr : RetOK ret tail) (m : ByteArray) {p : Nat}
    (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p Fips204.zeroPoly ∧ FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.zeroPoly [wd p] ret tail m [] m' Gas.zeroPoly := by
  sorry

theorem ntt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) {m : ByteArray} {p : Nat} {f : Fips204.Poly}
    (hf : PolyAt m p f) (hred : Reduced f) (hz : ZetaTable m)
    (hp : ZETA + POLY ≤ p) (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p (Fips204.ntt f) ∧ Reduced (Fips204.ntt f) ∧
      FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.ntt [wd p] ret tail m [] m' Gas.ntt := by
  sorry

theorem nttInv_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) {m : ByteArray} {p : Nat} {f : Fips204.Poly}
    (hf : PolyAt m p f) (hred : Reduced f) (hz : ZetaTable m)
    (hp : ZETA + POLY ≤ p) (hmem : p + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', PolyAt m' p (Fips204.nttInv f) ∧ Reduced (Fips204.nttInv f) ∧
      FrameExcept m m' [(p, p + POLY)] ∧
      Call s Entry.nttInv [wd p] ret tail m [] m' Gas.nttInv := by
  sorry

end MlDsa44.Proofs
