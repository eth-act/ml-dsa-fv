import MlDsaOpt65.Main.Base
/-! # Segment `3093 … 3115`: `ntt(ZH)`, `ntt(ZH2)`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegNtt.lean`; two `ntt_call`s, `p = ZH` and
`p = ZH2`; every lane of both tables is a `zLane < 2^25`, lanes of polynomials `0 … 4`
give `ẑ` via `ntt_zLane`). -/
theorem seg_ntt {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv2 cd m) (b : Bool)
    (hcd : HDR ≤ cd.size) :
    ∃ m', Inv3 cd m' ∧
      Reach (callState s 3093 [flag b] m) (callState s 3115 [flag b] m') Gas.pNtt := by
  sorry

end MlDsaOpt65.Proofs
