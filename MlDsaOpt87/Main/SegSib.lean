import MlDsaOpt87.Main.Base
/-! # Segment `1126 … 1135`: `sib` (SampleInBall with its own `kf1` sponge), `AND` -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `1126 … 1135`, open: `sib_call` (needs `RC1Table`, `SibFresh` from the
zeroed `MISC … ZH` and `BASES … HP` of `Inv1`), then `AND` of its flag `okC`
with the stack flag (`and_flags_block` of `MlDsaOpt44/Main/SegSib.lean`).
`sib`'s frame (`KS`, `KB`, `CW`, `BASES`, `IDX`, `NNEG`) avoids `ZH`, `HP`,
`ACC`, the tables. -/
theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv1 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv2 s.executionEnv.calldata m' ∧
      Reach (callState s 1126 [flag b] m)
        (callState s 1135 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  sorry

end MlDsaOpt87.Proofs
