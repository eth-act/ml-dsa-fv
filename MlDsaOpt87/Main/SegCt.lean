import MlDsaOpt87.Main.Base
/-! # Segment `6591 … 6646`: `tbuild`, `csum` per row group -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `6591 … 6646`, open: for `g < 2`, `tbuild [32 + 1280 g, TT + 0x1800 g]`
(`TTable`) and `csum [TT + 0x1800 g, SP + 0x2000 g]` (`SpAt` under `okC`, from
`CAt`). Frames: `TT`/`SP` overlay `ABUF`/`FL`/`ZH` (dead after ExpandA); `ACC`,
`HP`, `FIN`, `CW`, `BASES` untouched. Mirror `MlDsaOpt44/Main/SegCt.lean`. -/
theorem seg_ct {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv7 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv8 s.executionEnv.calldata m' ∧
      Reach (callState s 6591 [flag b] m) (callState s 6646 [flag b] m') Gas.pCt := by
  sorry

end MlDsaOpt87.Proofs
