import MlDsaOpt65.Main.Base
/-! # Segment `6610 … 6688`: `intt`, `usehint`, `pack` for both row groups. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegW.lean`). `intt [ACC]`, `usehint [ACC]`,
`pack [4, FIN + 0x100, ACC]`, `intt [ACC + 0x2000]`, `usehint [ACC + 0x2000]`,
`pack [2, FIN + 0x900, ACC + 0x2000]`: `w1Encode` (4 bits per coefficient, 16 lanes per row:
rows 0–3 in lanes `8 … 71`, rows 4, 5 in `72 … 103`) into `FIN[8, 104)`; with `FinMu`,
`FinAt m (finBytes cd)` when `ok3`. -/
theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 6610 [flag b] m) (callState s 6688 [flag b] m') Gas.pW := by
  sorry

end MlDsaOpt65.Proofs
