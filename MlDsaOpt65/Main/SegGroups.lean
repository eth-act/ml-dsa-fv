import MlDsaOpt65.Main.Base
/-! # Segments `3565 … 3634` and `5221 … 5236`: the pure ExpandA groups (`group` calls). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegGroups.lean` `seg_g0`; `group [15, 0, 0]`,
`AND`; `ACC` starts zero (`zIdx`), `gOk cd 15 0 0 = okCol0 cd 0`). -/
theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3565 [flag b] m)
        (callState s 3578 [flag (b && okCol0 s.executionEnv.calldata 0)] m') Gas.pG0 := by
  sorry

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegGroups.lean` `seg_g1`; `group [15, 1, 0]`, `AND`;
column `1` uses `ẑ_1` (lane `1` of `ZH`)). -/
theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3578 [flag b] m)
        (callState s 3592 [flag (b && okCol0 s.executionEnv.calldata 1)] m') Gas.pG1 := by
  sorry

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegGroups.lean` `seg_g1`; `group [15, 2, 0]`, `AND`;
column `2` uses `ẑ_2` (lane `2` of `ZH`)). -/
theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3592 [flag b] m)
        (callState s 3606 [flag (b && okCol0 s.executionEnv.calldata 2)] m') Gas.pG2 := by
  sorry

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegGroups.lean` `seg_g1`; `group [15, 3, 0]`, `AND`;
column `3` uses `ẑ_3` (lane `3` of `ZH`)). -/
theorem seg_g3 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3606 [flag b] m)
        (callState s 3620 [flag (b && okCol0 s.executionEnv.calldata 3)] m') Gas.pG3 := by
  sorry

/-- **Open** (WP: mirror `MlDsaOpt44/Main/SegGroups.lean` `seg_g1`; `group [15, 4, 0]`, `AND`;
column `4` uses `ẑ_4` (lane `0` of `ZH2`)). -/
theorem seg_g4 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3620 [flag b] m)
        (callState s 3634 [flag (b && okCol0 s.executionEnv.calldata 4)] m') Gas.pG4 := by
  sorry

/-- **Open** (WP: as `seg_g1`; `group [3, 4, 1]`: slots 0, 1 squeeze `A[4][4]`, `A[5][4]`
into lanes 0, 1 of `ACC + 0x2000`; lanes 2, 3 add inactive-slot candidates (`< 2^23`) times
`ẑ_4`; `gOk cd 3 4 1 = okCol1 cd 4`. Establishes `Inv5`: `AccAt` from `AccCols0 5`,
`AccCols1 5` (`accSum` bounds, the `azRow` congruence from `ZHatAt`), `SibFresh` from the
zero facts). -/
theorem seg_g9 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvMu s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv5 s.executionEnv.calldata m' ∧
      Reach (callState s 5221 [flag b] m)
        (callState s 5236 [flag (b && okCol1 s.executionEnv.calldata 4)] m') Gas.pG9 := by
  sorry

end MlDsaOpt65.Proofs
