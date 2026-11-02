import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Keccak
import MlDsaOpt44.Fn.Sponge
/-! # Segment `5075 … 5876`: μ

`|M| ≤ 69`: μ's lanes in `MU` (squeezed from the SIMD slot), replicated into
`FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after block 0 is slot 1 of the
saved image `SC`; it is copied to `KS`, extracted in place (`cext`, 25 lanes),
replicated for `kf1`, and the remaining blocks are absorbed by the `kf1` /
`absorb17` loop; the final permutation's lanes 0 … 7 go to `FIN`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5075 [flag b] m) (callState s 5876 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry

end MlDsaOpt44.Proofs
