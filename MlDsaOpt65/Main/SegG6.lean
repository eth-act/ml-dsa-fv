import MlDsaOpt65.Main.Base
import MlDsaOpt65.Main.S4.G6
/-! # Segment `4074 … 4517`: mixed ExpandA group 6 (rows 4, 5 of column 1 with riders). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Group 6 (proof: `Main/S4/G6.lean`): `ginit` with `keep = 0x88…8` (slot 3 carried: `tr` sponge after 5 blocks),
five rounds `trabs 5` (pk blocks 5–9) + `kf4` + `blk`, `gfix [3]`, `AND`, `pass3 [64, ZH, ACC +
0x2000]`. Mirror `MlDsaOpt44/Main/SegG234/G3.lean`.
Rows 4, 5 of column 1 accumulate into lanes 0, 1 of `ACC + 0x2000` (`AccCols1`); lanes 2, 3
stay `≤ 2 · 2^51` (candidates `< 2^23` times `ẑ` lanes `< 2^28`). -/
theorem seg_g6 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvT s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 2 ∧
      Reach (callState s 4074 [flag b] m)
        (callState s 4517 [flag (b && okCol1 s.executionEnv.calldata 1)] m') Gas.pG6 :=
  S4.seg_g6_proof hs hcd hI b

end MlDsaOpt65.Proofs
