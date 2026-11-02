import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Group
import MlDsaOpt65.Fn.Sponge
/-! # Segment `3556 … 5242`: ExpandA (v4, open)

Groups 0 … 4 (`group [15, s, 0]`, copies of `ABUF` to `CW`, `HP`,
`HP + 0x2000`, `ACC + 0x2000`, then `pass3f4` into `ACC`); the mixed groups
5 … 7 (row-group-1 instances in slots 0 … 2, `tr` in slot 3, `TRL` after group
7; copies to `CW`, `HP`, `HP + 0x2000`); group 8 (`A[5][4]` in slot 0, the
c̃ stream in slot 1 (`CB`), μ's blocks 0 … 4 in slot 2 by `mub0` / `mub`,
with the out-of-line `mulong` region rejoining at `gfix`'s return); `pass3f8`
into `ACC + 0x2000`. One segment for now; the v3 group proofs
(`Main/SegG{5,6,7,8}.lean`, `Main/S{3,4}`, removed in the v4 retarget) show the
shape of its parts. -/

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
        Gas.pExp := by
  sorry

end MlDsaOpt65.Proofs
