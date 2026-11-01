import MlDsaOpt65.Main.Base
import MlDsaOpt65.Main.S4.G8
/-! # Segment `5029 … 5221`: mixed ExpandA group 8 (rows 4, 5 of column 3 with riders). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Group 8 (proof: `Main/S4/G8.lean`): `ginit [0x777770000070200000077, 0, 7, 0]`, `mu0 [3]` (slot 3: `H(tr ‖ 0 ‖
0 ‖ M)` for `|M| ≤ 69`, from `TRL`), five `kf4` + `blk`, `cext [8, 3, MU]` (μ), `gfix [3]`, `AND`,
`pass3 [192, ZH, ACC + 0x2000]`. Mirror `MlDsaOpt44/Main/SegG234/G4.lean` (μ rider).
Rows 4, 5 of column 3 accumulate into lanes 0, 1 of `ACC + 0x2000` (`AccCols1`); lanes 2, 3
stay `≤ 4 · 2^51` (candidates `< 2^23` times `ẑ` lanes `< 2^28`). -/
theorem seg_g8 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvMu s.executionEnv.calldata m' ∧
      Reach (callState s 5029 [flag b] m)
        (callState s 5221 [flag (b && okCol1 s.executionEnv.calldata 3)] m') Gas.pG8 :=
  S4.seg_g8_proof hs hcd hI b

end MlDsaOpt65.Proofs
