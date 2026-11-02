import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Group
import MlDsaOpt87.Fn.Sponge
import MlDsaOpt87.Main.Exp.Compose
import MlDsaOpt87.Main.Exp.G1013
/-! # Segment `3371 … 5551`: ExpandA (v4)

All fifteen groups: the ten pure groups `group [15, s, rb]` (rows 0–3 of
columns 0–6, rows 4–7 of columns 0–2), the mixed groups 10–13 (rows 4–6 of
columns 3–6, the `tr` rider in slot 3, `TRL` after group 13) and the
Kronecker group 14 (row 7, columns 3–6); the copies of `ABUF` to the side
buffers `CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`, and the fused passes
`pass3f4`, `pass3f6`, `pass3f10`, `pass3f14` into `ACC`. Composed in
`Main/Exp/Compose.lean` from `Exp.exp_pure` (groups 0–9, `Main/Exp/Pure.lean`),
`Exp.exp_g1013` (groups 10–13, `Main/Exp/G1013.lean`) and `Exp.exp_g14`
(group 14, `Main/Exp/G14.lean`); the three costs sum to exactly `Gas.pExp`. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

theorem seg_exp {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3371 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 5551 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp :=
  Exp.seg_exp_of hs hcd hI (fun m b h => Exp.exp_g1013 hs hcd h b) (by
    unfold Exp.pureCost Exp.gG1013 Exp.gG14; decide)

end MlDsaOpt87.Proofs
