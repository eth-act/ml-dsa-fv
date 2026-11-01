import MlDsaOpt87.Main.Base
/-! # Segment `3118 … 3140`: `ntt(ZH)`, `ntt(ZH2)` -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `3118 … 3140`, open: two `ntt` calls on the two `ẑ` tables (lanes of `ZAt`
are `< 2^25`; polynomials `0 … 6` give `ZHatAt` via `ntt_zLane`; lane 3 of
`ZH2` is transformed garbage, unconstrained). Mirror
`MlDsaOpt44/Main/SegNtt.lean`. -/
theorem seg_ntt {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv3 cd m) (b : Bool)
    (hcd : HDR ≤ cd.size) :
    ∃ m', Inv4 cd m' ∧
      Reach (callState s 3118 [flag b] m) (callState s 3140 [flag b] m') Gas.pNtt := by
  sorry

end MlDsaOpt87.Proofs
