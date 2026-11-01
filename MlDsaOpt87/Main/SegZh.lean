import MlDsaOpt87.Main.Base
/-! # Segment `992 … 1126`: `dz` twice, the norm-flag check, `dhint` -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `992 … 1126`, open: `dz [ZH, Z0]` (`dz_call` with `g = 0`), `OR` into the
flag accumulator; `dz [ZH2, Z0 + 2560]` (`g = 1`), flag word `AND (2^192 − 1)`
(lanes of `z_4 … z_6` only), `OR`; `flag_check` (`acc &&& zBits = 0 ↔ okZ`
by `okZ_iff_zNormOk`); `dhint` (`dhint_call`, `HP` zeroed by `Inv0`); `AND`.
Mirror `MlDsaOpt44/Main/SegZh.lean`. -/
theorem seg_zh {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv0 m) :
    ∃ m', Inv1 s.executionEnv.calldata m' ∧
      Reach (callState s 992 [] m) (callState s 1126 [flag (ok1 s.executionEnv.calldata)] m')
        Gas.pZh := by
  sorry

end MlDsaOpt87.Proofs
