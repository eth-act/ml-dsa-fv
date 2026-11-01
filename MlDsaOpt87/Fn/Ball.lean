import MlDsaOpt87.Fn.Ball.Proof
/-! # `sib` contract (ML-DSA-87)

Proved in `Fn/Ball/{Blocks,Prologue,Stream,Proof}.lean` (`sib_call_proof`). ML-DSA-87 has no free SIMD slot for `H(c̃)`, so
`sample_in_ball` squeezes the SampleInBall stream itself with `kf1`
(`Gen.gen_sample_in_ball` with `simd_c() = False`): it zeroes `KS`, absorbs the 64-byte
`c̃` from calldata `CTOFF` (8 lanes, replicated), XORs the SHAKE256 padding (`0x1F` into
lane 8, `0x80` into the top byte of lane 16), runs `kf1`, un-complements the rate lanes
and reads the sign word from `KS[0]`; then scans bytes `8 … 271` as FIPS 204
Algorithm 29 (`τ = 60`, loop start `i = 196`), reading byte `p mod 136` of the current
block from `KS`; at `p = 136` it re-complements, runs `kf1` again (second block) and
un-complements. The `CW`/`BASES`/`IDX`/`NNEG`/`CNT` bookkeeping is the ML-DSA-44 one.

Call site: `sib []` right after `dhint` in segment zh/sib (pc 1129). The proof follows
`MlDsaOpt44/Fn/Ball/{Blocks,Proof}.lean` for the scan (over the parametric
`MlDsaOptCommon.BallScan`), with the absorption prologue (`Prologue`: `KS1` of the padded
`c̃` seed state), the two `kf1_call`s, and `Stream.le64_cStream`: the two `kf1` blocks are
the lanes of `cStream = H(c̃)`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **sib**: `[ret] ↦ [okC]`. With the iota table (for `kf1`) and fresh scratch
(`SibFresh`): on success `CW`, `NNEG`, `BASES` represent `c = SampleInBall(c̃)` (`CRep`);
the bases stay inside the window table (`≤ 6112`) in any case. `KS`, `KB` are clobbered. -/
theorem sib_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (hrc : RC1Table m)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hz : SibFresh m) :
    ∃ m', (∀ c, cOf s.executionEnv.calldata = some c → CRep m' c) ∧
      (∀ i, i < P.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (CW, CW + 8192), (BASES, BASES + 2048),
        (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (okC s.executionEnv.calldata)] m' Gas.sib :=
  sib_call_proof hs hr m hrc hcd hz

end MlDsaOpt87.Proofs
