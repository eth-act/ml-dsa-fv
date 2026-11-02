import MlDsaOpt65.Fn.Ball.Defs
import MlDsaOptGlam65.Budget
import MlDsaOptGlam65.Fn.Ball.V4Loop
import MlDsaOptGlam65.Layout
/- Ported from `MlDsaOpt65/Fn/Ball.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # `sib` contract (v4: lane-unrolled byte loop, `±REP` codes)

 (ML-DSA-65)

The code is the ML-DSA-44 v4 `sample_in_ball` with `τ = 49` (loop start
`i = 256 − τ = 207`) and the ML-DSA-65 `CB`/`BASES`/`IDX` addresses: it scans
bytes `8 … 271` of the 272-byte stream `H(c̃)` (34 lanes in `CB`, squeezed from
SIMD slot 2 of group 5 by `cext`) as FIPS 204 Algorithm 29 with the Appendix C
limit, one 64-bit lane per iteration (8 unrolled byte tests, one shared accept
step); at `o = 0x440` it returns `0`. Call site: `sib []` at the start of
segment sib (pc 5843). The proof is `sib_main` (`Fn/Ball/V4*.lean`, generated
and ported from `MlDsaOpt44/Fn/Ball/V4*.lean`). `BASES` starts zeroed
(`SibFresh`), so on the failure path the unwritten slots stay in range. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

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
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf P bs).isSome] m' Gas.sib :=
  sib_main hs hr m bs hbs hcb hz

end MlDsaOptGlam65.Proofs
