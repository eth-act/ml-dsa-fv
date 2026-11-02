import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Group
import MlDsaOpt65.Fn.Sponge
import MlDsaOpt65.Main.Exp.Compose
import MlDsaOpt65.Main.Exp.G57
import MlDsaOpt65.Main.Exp.G8
/-! # Segment `3556 … 5242`: ExpandA (v4)

Groups 0 … 4 (`group [15, s, 0]`, copies of `ABUF` to `CW`, `HP`,
`HP + 0x2000`, `ACC + 0x2000`, then `pass3f4` into `ACC`); the mixed groups
5 … 7 (row-group-1 instances in slots 0 … 2, `tr` in slot 3, `TRL` after group
7; copies to `CW`, `HP`, `HP + 0x2000`); group 8 (`A[5][4]` in slot 0, the
c̃ stream in slot 1 (`CB`), μ's blocks 0 … 4 in slot 2 by `mub0` / `mub`,
with the out-of-line `mulong` region rejoining at `gfix`'s return); `pass3f8`
into `ACC + 0x2000`. Composed in `Main/Exp/Compose.lean` from `Exp.exp_pure`
(groups 0–4, `Main/Exp/Pure.lean`), `Exp.exp_g57` (groups 5–7,
`Main/Exp/G57.lean`) and `Exp.exp_g8` (group 8, `pass3f8`, `Main/Exp/G8.lean`;
budget: the `mulong` path). The three costs sum to exactly `Gas.pExp`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

theorem seg_exp {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3556 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 5242 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp :=
  Exp.seg_exp_of hs hcd hI (fun m b h => Exp.exp_g57 hs hcd h b) (fun m b h => Exp.exp_g8 hs hcd h b)
    (by rw [Exp.gG8_eq]; unfold Exp.gPure Exp.gG57; decide)

end MlDsaOpt65.Proofs
