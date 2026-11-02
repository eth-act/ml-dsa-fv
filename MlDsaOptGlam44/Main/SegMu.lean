import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOptGlam44.Fn.Sponge
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegMu.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `5183 … 6020`: μ (packed schedule)

**Open item** (glam): `hash_mu` and the dispatch before it read `FLAG` (the
long-message switch): the dispatch's bound is `0x10fa − 0x220 · FLAG` (3802 on
the packed schedule), `hash_mu` starts with `FLAG == 0 → muimg`, and the block
loop's offset uses the same bound. On the packed schedule (`FLAG = 1`, in
`InvH`) the path is v4's (`MlDsaOpt44/Main/Mu/*.lean`) plus those
instructions (`Gas.pMu`); the proof is v4's with four blocks extended.

v4's description:

`|M| ≤ 69`: μ's lanes in `MU` (squeezed from the SIMD slot), replicated into
`FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after block 0 is slot 1 of the
saved image `SC`; it is copied to `KS`, extracted in place (`cext`, 25 lanes),
replicated for `kf1`, and the remaining blocks are absorbed by the `kf1` /
`absorb17` loop; the final permutation's lanes 0 … 7 go to `FIN`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5183 [flag b] m) (callState s 6020 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry  -- glam: open item (v4 proof plus the four `FLAG` blocks)

end MlDsaOptGlam44.Proofs
