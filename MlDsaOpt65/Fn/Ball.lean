import MlDsaOpt65.Fn.Ball.Defs
/-! # `sib` contract (ML-DSA-65)

Open contract (statement only). The code is the ML-DSA-44 `sample_in_ball` with
`τ = 49` (loop start `i = 256 − τ = 207`) and the ML-DSA-65 `CB`/`BASES`/`IDX`
addresses: it scans bytes `8 … 271` of the 272-byte stream `H(c̃)` (34 lanes in `CB`,
squeezed from SIMD slot 2 of group 5 by `cext`) as FIPS 204 Algorithm 29 with the
Appendix C limit. Call site: `sib []` at the start of segment sib (pc 6545). The proof
mirrors `MlDsaOpt44/Fn/Ball/{Blocks,Proof}.lean` (`sib_call_proof`). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **sib**: `[ret] ↦ [ok]`, `ok = (SampleInBall bs).isSome`, for the stream `bs` whose
lanes are in `CB` and fresh scratch (`SibFresh`). On success `CW`, `NNEG`, `BASES`
represent `c` (`CRep`); the bases stay inside the window table (`≤ 6112`) in any case. -/
theorem sib_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x)) (hz : SibFresh m) :
    ∃ m', (∀ c, Fips204.sampleInBallOf P bs = some c → CRep m' c) ∧
      (∀ i, i < P.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(CW, CW + 8192), (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf P bs).isSome] m' Gas.sib := by
  sorry

end MlDsaOpt65.Proofs
