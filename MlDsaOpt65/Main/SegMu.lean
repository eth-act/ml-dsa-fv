import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Keccak
import MlDsaOpt65.Fn.Sponge
/-! # Segment `5356 … 6172`: μ (v4, open)

`|M| ≤ 613`: the eight `MU` lanes (μ squeezed in group 8's slot 2 by `mub`)
replicated into `FIN[0, 8)`. Otherwise (`hash_mu`): μ's sponge after blocks
`0 … 4` is slot 2 of `KS` (`MuKs`); `cext [KS, 2, 25]` extracts it in place,
the lanes are replicated for `kf1` (`NOT` on complemented lanes), block 5 is
absorbed, the `kf1` / `absorb17` loop absorbs the rest, the final permutation's
lanes `0 … 7` go to `FIN`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

theorem seg_mu {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvH s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5356 [flag b] m) (callState s 6172 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  sorry

end MlDsaOpt65.Proofs
