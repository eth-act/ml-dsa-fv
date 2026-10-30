import MlDsa44.Proofs.Fn.Ntt
import MlDsa44.Proofs.Fn.Sampling.Rej
import MlDsa44.Proofs.Fn.Sampling.Ball
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

The loops are proved in `Fn/Sampling/Rej.lean` and `Fn/Sampling/Ball.lean`
(blocks in `Fn/Sampling/*Blocks.lean`, spec refolding in `Math/Sampling/`).
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budgets: exact worst cases over all branches.
namespace Gas

/-- `5 + 256·212 + 80·177 + 61`: 256 accepted triples (212 each), 80 rejected
(177 each); a skipped triple (count already 256) costs only 77. -/
def rejSample : Nat := 68498

/-- `18 + zeroPoly + 7 + 39·256 + 225·119 + 59`: 39 accepted positions (256
each), 225 rejected (119 each); a skipped position costs only 77. -/
def sampleInBall : Nat := zeroPoly + 36843

end Gas

theorem rejSample_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.rejSample ret tail) {m : ByteArray} {dst : Nat} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.rejNTTPolyLimit)
    (hdst : ZETA + POLY ≤ dst ∧ (dst + POLY ≤ XOF ∨ XOF + 0x420 ≤ dst))
    (hmem : dst + POLY + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', (∀ a, Fips204.rejNTTPolyOf bs = some a → PolyAt m' dst a ∧ Reduced a) ∧
      FrameExcept m m' [(dst, dst + POLY)] ∧
      Call s Entry.rejSample [wd dst] ret tail m [flag (Fips204.rejNTTPolyOf bs).isSome] m'
        Gas.rejSample :=
  Sampling.rejSample_main hs hr hbs hsize hdst hmem

theorem sampleInBall_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sampleInBall ret tail) {m : ByteArray} {bs : ByteArray}
    (hbs : BytesAt m XOF bs) (hsize : bs.size = Fips204.sampleInBallLimit) :
    ∃ m', (∃ c', PolyAt m' CH c' ∧ Reduced c') ∧
      (∀ c, Fips204.sampleInBallOf bs = some c →
        PolyAt m' CH (c.map (· % (Fips204.q : Int))) ∧ Reduced (c.map (· % (Fips204.q : Int)))) ∧
      FrameExcept m m' [(CH, CH + POLY)] ∧
      Call s Entry.sampleInBall [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m'
        Gas.sampleInBall := by
  have hmem : CH + POLY + 32 ≤ 32 * s.activeWords.toNat := by
    have h : 2535 ≤ s.activeWords.toNat := hs.sized
    simp only [CH, POLY]; omega
  obtain ⟨m0, hm0, hf0, hcall⟩ := zeroPoly_call hs
    (hr.callee (B' := Stack.zeroPoly) (ret' := 3648) (extra := [wd 0, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) m hmem
  have hz : Infra.Reach (callState s 3067 (wd 43488 :: wd 3648 :: wd 0 :: wd ret :: tail) m)
      (callState s 3648 (wd 0 :: wd ret :: tail) m0) Gas.zeroPoly :=
    (Infra.call_iff.mp hcall).of_eq (by simp [Entry.zeroPoly, CH]) (by simp)
  exact Sampling.sampleInBall_main hs hr hbs hsize hm0 hf0 hz

end MlDsa44.Proofs
