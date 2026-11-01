import MlDsaOpt65.Main.Base
/-! # Segment `992 … 1110`: `dz` twice (`ZH`, `ZH2`), the norm-flag check, `dhint`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegZh.lean` with the 65 `dz_call` / `dhint_call`).
`dz [ZH, Z0]`, `dz [ZH2, Z0 + 2560]` (flag word of the second call masked to lane 0, `OR`ed),
the flag check against `zBits` (`ISZERO`), `dhint` (rows into `HP`, `HP + 0x2000`), `AND`:
`okZ ∧ okH` on the stack. Needs: lanes `0 … 3` of the first flag word and lane 0 of the second
together decide `okZ` (`ℓ = 5`), `ZeroOn HP (HP + 0x4000)` for `dhint`. -/
theorem seg_zh {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv0 m) :
    ∃ m', Inv1 s.executionEnv.calldata m' ∧
      Reach (callState s 992 [] m) (callState s 1110 [flag (ok1 s.executionEnv.calldata)] m')
        Gas.pZh := by
  sorry

end MlDsaOpt65.Proofs
