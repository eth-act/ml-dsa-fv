import MlDsaOptGlam44.Main.SegZd
import MlDsaOptGlam44.Main.SegMu
import MlDsaOptGlam44.Main.SegSib
import MlDsaOptGlam44.Gas
-- set_option warningAsError true  -- TODO restore
/-!
# The long-message schedule (`|M| ≥ 342`): `2436 … 6030`

The jump to `alt`, the previous schedule's three mixed groups (the last one
carrying μ's blocks 0 … 4 through `mub0` / `mulong` / `mub`), `pass3f4b`, then
the shared code with `FLAG = 0`: the side buffers and hints, μ (from `MU`, or
`hash_mu` from the slot state in `KS` via `muimg`), SampleInBall (`sib_call0`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem seg_alt {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (hge : 4074 ≤ s.executionEnv.calldata.size)
    (hfl : word m FLAG = 0) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 2436
          [flag ((okZ s.executionEnv.calldata && okCol s.executionEnv.calldata 0) &&
            okCol s.executionEnv.calldata 1)] m)
        (callState s 6030 [flag (ok2 s.executionEnv.calldata && okC s.executionEnv.calldata)] m')
        (Gas.pAlt (mlenOf s.executionEnv.calldata)) := by
  sorry

end MlDsaOptGlam44.Proofs
