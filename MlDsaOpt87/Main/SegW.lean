import MlDsaOpt87.Main.Base
/-! # Segment `6646 … 6724`: `intt`, `usehint`, `pack` per row group -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `6646 … 6724`, open: for `g < 2`, `intt [ACC + 0x2000 g]`, `usehint [ACC + 0x2000 g]`
(reads `HP`/`SP` at fixed offsets from the accumulator table), `pack [ACC + 0x2000 g,
FIN + 32 (8 + 64 g), 4]`. Under `ok3`: `AccAt` (lanes `< 2^58`), `SpAt`, the hint
give `w1Of` row by row, and `FIN` holds `μ ‖ w1Encode(w1)` (`FinAt`, 136
lanes). Mirror `MlDsaOpt44/Main/SegW.lean`. -/
theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 6646 [flag b] m) (callState s 6724 [flag b] m') Gas.pW := by
  sorry

end MlDsaOpt87.Proofs
