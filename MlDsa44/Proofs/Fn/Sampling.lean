import MlDsa44.Proofs.Fn.Ntt
/-!
# `rejSample` and `sampleInBall`

Both read an XOF stream previously squeezed into `XOF`.

Yul:
* `rejSample(dst) -> good`: scan all 336 triples of the 1008-byte stream,
  storing accepted coefficients (`< q`) while fewer than 256 are stored;
  `good` iff 256 were found (FIPS 204 Algorithm 30 with the Appendix C limit);
* `sampleInBall() -> good`: zero `CH`, then scan bytes `8 … 271`, placing the
  `τ = 39` signed coefficients as `1` or `q − 1` (Algorithm 29 with the
  Appendix C limit); `good` iff all 39 were placed.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def rejSample : Nat := 336 * 250 + 100

def sampleInBall : Nat := zeroPoly + 264 * 250 + 100

end Gas

theorem rejSample_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.rejSample ret tail) {m : ByteArray} {dst : Nat} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.rejNTTPolyLimit)
    (hdst : ZETA + POLY ≤ dst ∧ (dst + POLY ≤ XOF ∨ XOF + 0x420 ≤ dst))
    (hmem : dst + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', (∀ a, Fips204.rejNTTPolyOf bs = some a → PolyAt m' dst a ∧ Reduced a) ∧
      FrameExcept m m' [(dst, dst + POLY)] ∧
      Call s Entry.rejSample [wd dst] ret tail m [flag (Fips204.rejNTTPolyOf bs).isSome] m'
        Gas.rejSample := by
  sorry

theorem sampleInBall_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sampleInBall ret tail) {m : ByteArray} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.sampleInBallLimit) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c →
        PolyAt m' CH (c.map (· % (Fips204.q : Int))) ∧ Reduced (c.map (· % (Fips204.q : Int)))) ∧
      FrameExcept m m' [(CH, CH + POLY)] ∧
      Call s Entry.sampleInBall [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m'
        Gas.sampleInBall := by
  sorry

end MlDsa44.Proofs
