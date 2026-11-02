import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Group
import MlDsaOptGlam65.Fn.Sponge
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
import MlDsaOptGlam65.Fn.Blk
import MlDsaOptGlam65.Fn.Fix
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Main.Mu.Spec
/- Ported from `MlDsaOpt65/Main/SegExp.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `3556 … 4903`: ExpandA (v4)

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

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

theorem seg_exp {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 2515 [flag (okZ s.executionEnv.calldata)] m)
        (callState s 4903 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pExp := by
  sorry  -- glam: open item (package 4: the 42-call schedule)

end MlDsaOptGlam65.Proofs
