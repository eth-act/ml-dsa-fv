import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Keccak
import MlDsaOptGlam65.Fn.Sponge
import MlDsaOptGlam65.Main.Mu.Spec
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegMu.lean` by `scripts/proofgen_port.py --glam 65`; the statement is v4's, the proof an open item. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError false  -- glam: open items (`sorry`)
/-! # Segment `5356 … 5843`: μ (v4)

`|M| ≤ 613`: the eight `MU` lanes (μ squeezed in group 8's slot 2 by `mub`)
replicated into `FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after blocks
`0 … 4` is slot 2 of `KS` (`MuKs`); `cext [KS, 2, 25]` extracts it in place,
the lanes are replicated for `kf1` (`NOT` on complemented lanes), block 5 is
absorbed, the `kf1` / `absorb17` loop absorbs the rest, the final permutation's
lanes `0 … 7` go to `FIN`. Blocks and composition in `Main/Mu/{Cext,Long,Run}`
(port of the ML-DSA-44 proof). -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5017 [flag b] m) (callState s 5843 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry  -- glam: open item (package 4: `hash_mu` saves the μ slot's state first, `MCOPY` to `0x15040`)

end MlDsaOptGlam65.Proofs
