import MlDsaOpt65.Main.Base
import MlDsaOpt65.Main.S4.G5
/-! # Segment `3634 … 4074`: mixed ExpandA group 5 (rows 4, 5 of column 0 with riders). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Group 5 (proof: `Main/S4/G5.lean`): `ginit [0x333330000030200000000, 4, 3, 0]` (slots 0, 1: `A[4][0]`,
`A[5][0]` (`amult 3`); slot 2: c̃ (`cmult 4`); slot 3: `tr` sponge, fresh), five rounds `trabs 5`
(pk blocks 0–4 into slot 3) + `kf4` + `blk`, `cext 17` twice after rounds 0 and 1 (the c̃ stream
`H(c̃)` into `CB`, `CB + 0x220`), `gfix [3]`, `AND`, `pass3 [0, ZH, ACC + 0x2000]`. Mirror
`MlDsaOpt44/Main/SegG234/G2.lean` (tr rider) and `G4.lean` (c̃ stream).
Rows 4, 5 of column 0 accumulate into lanes 0, 1 of `ACC + 0x2000` (`AccCols1`); lanes 2, 3
stay `≤ 1 · 2^51` (candidates `< 2^23` times `ẑ` lanes `< 2^28`). -/
theorem seg_g5 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvG s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3634 [flag b] m)
        (callState s 4074 [flag (b && okCol1 s.executionEnv.calldata 0)] m') Gas.pG5 :=
  S4.seg_g5_proof hs hcd hI b

end MlDsaOpt65.Proofs
