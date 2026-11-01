import MlDsaOpt44.Main.Base
/-! # Segment `4648 … 5926`: μ from the SIMD slot (`|M| ≤ 69`) or `hash_mu` (`kf1`). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 4648 [flag b] m) (callState s 5926 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry


end MlDsaOpt44.Proofs
