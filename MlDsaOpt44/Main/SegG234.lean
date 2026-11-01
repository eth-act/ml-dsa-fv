import MlDsaOpt44.Main.SegG234.Proof
set_option warningAsError true
/-! # Segment `3466 … 4648`: the three mixed SIMD groups (tr, c̃, μ riders; `pass3m`, `pass3k4`).

Proof in `Main/SegG234/`: `G2`, `G3`, `G4` (one group each, on top of `Round`)
and their composition `Proof`; sponge facts in `Math/Sponge*.lean`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_g234 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', Inv5 s.executionEnv.calldata m' ∧
      Reach (callState s 3466 [flag b] m)
        (callState s 4648
          [flag (b && (okCol s.executionEnv.calldata 2 && okCol s.executionEnv.calldata 3))] m')
        Gas.pG234 :=
  seg_g234_proof hs hcd hI b


end MlDsaOpt44.Proofs
