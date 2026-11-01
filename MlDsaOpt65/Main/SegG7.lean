import MlDsaOpt65.Main.Base
import MlDsaOpt65.Main.S4.G7
/-! # Segment `4517 … 5029`: mixed ExpandA group 7 (rows 4, 5 of column 2 with riders). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Group 7 (proof: `Main/S4/G7.lean`): `ginit` keeping slot 3, `trabs 5` ×4 + `trabs 2` (pk blocks 10–14, last one
with the `0x1F … 0x80` padding) + `kf4` + `blk`, `cext [8, 3, TRL]` (`tr`), `gfix [3]`, `AND`,
`pass3 [128, ZH, ACC + 0x2000]`. Mirror `MlDsaOpt44/Main/SegG234/G3.lean`.
Rows 4, 5 of column 2 accumulate into lanes 0, 1 of `ACC + 0x2000` (`AccCols1`); lanes 2, 3
stay `≤ 3 · 2^51` (candidates `< 2^23` times `ẑ` lanes `< 2^28`). -/
theorem seg_g7 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvTr s.executionEnv.calldata m' ∧
      Reach (callState s 4517 [flag b] m)
        (callState s 5029 [flag (b && okCol1 s.executionEnv.calldata 2)] m') Gas.pG7 :=
  S4.seg_g7_proof hs hcd hI b

end MlDsaOpt65.Proofs
