import MlDsaOpt87.Fn.Ball.Defs
import MlDsaOpt87.Budget
import MlDsaOpt87.Fn.Ball.V4Loop
/-! # `sib` contract (v4: lane-unrolled byte loop, `±REP` codes) (ML-DSA-87)

Proved as `sib_main` in `Fn/Ball/V4{Blocks,Prologue,Proof,Scan,Loop}.lean`. ML-DSA-87 has no
free SIMD slot for `H(c̃)`, so `sample_in_ball` squeezes the SampleInBall stream itself with
`kf1` (`Gen.gen_sample_in_ball` with `simd_c() = False`): it zeroes `KS`, absorbs the 64-byte
`c̃` from calldata `CTOFF` (8 lanes, replicated), XORs the SHAKE256 padding (`0x1F` into
lane 8, `0x80` into the top byte of lane 16), runs `kf1`, un-complements the rate lanes
and reads the sign word from `KS[0]`; then scans bytes `8 … 271` as FIPS 204
Algorithm 29 (`τ = 60`, loop start `i = 196`), one 64-bit lane per iteration (8 unrolled
byte tests of the lane word `KS[32 x mod 544]`); at lane `x = 17` it re-complements, runs
`kf1` again (second block) and un-complements. The `CW` (`±REP` codes) / `BASES` / `IDX` /
`NNEG` / `CNT` bookkeeping is the ML-DSA-44 one. `BASES` starts zeroed (`SibFresh`), so the
slots the failure path leaves unwritten stay in range.

Call site: `sib []` in segment sib (`Main/SegSib.lean`). `Stream.le64_cStream`: the two
`kf1` blocks are the lanes of `cStream = H(c̃)`.
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
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (CW, CW + 8192), (BASES, BASES + 2048),
        (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (okC s.executionEnv.calldata)] m' Gas.sib :=
  sib_main hs hr m hrc hcd hz

end MlDsaOpt87.Proofs
