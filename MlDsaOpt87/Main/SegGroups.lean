import MlDsaOpt87.Main.Base
/-! # Segments `3389 … 3530`: the ten pure ExpandA groups `[15, col, rb]` -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-!
Each segment is `PUSH2 ret; PUSH rb; PUSH col; PUSH1 15; PUSH2 group; JUMP;
JUMPDEST; AND`; mirror `MlDsaOpt44/Main/SegGroups.lean`. `group_call` adds
`A[4 rb + r][col][t] · ẑ_col[t]` to lane `r` of `ACC + 0x2000 rb` under its
flag; the accumulator equation (`AccCols`) follows by `accSum`'s recursion
(`ẑ` is not written by `group`). Groups 0 and 7 start from the zeroed
accumulator table (`AccCols _ _ rb 0`).
-/

/-- `3389 … 3402`, open: `group [15, 0, 0]` (`group_call`; flag
`gOk cd 15 0 0 = okCol cd 0 0 4`), `AND`. -/
theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3389 [flag b] m)
        (callState s 3402 [flag (b && okCol s.executionEnv.calldata 0 0 4)] m') Gas.pG0 := by
  sorry

/-- `3402 … 3416`, open: `group [15, 1, 0]` (`group_call`; flag
`gOk cd 15 1 0 = okCol cd 0 1 4`), `AND`. -/
theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3402 [flag b] m)
        (callState s 3416 [flag (b && okCol s.executionEnv.calldata 0 1 4)] m') Gas.pG1 := by
  sorry

/-- `3416 … 3430`, open: `group [15, 2, 0]` (`group_call`; flag
`gOk cd 15 2 0 = okCol cd 0 2 4`), `AND`. -/
theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3416 [flag b] m)
        (callState s 3430 [flag (b && okCol s.executionEnv.calldata 0 2 4)] m') Gas.pG2 := by
  sorry

/-- `3430 … 3444`, open: `group [15, 3, 0]` (`group_call`; flag
`gOk cd 15 3 0 = okCol cd 0 3 4`), `AND`. -/
theorem seg_g3 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3430 [flag b] m)
        (callState s 3444 [flag (b && okCol s.executionEnv.calldata 0 3 4)] m') Gas.pG3 := by
  sorry

/-- `3444 … 3458`, open: `group [15, 4, 0]` (`group_call`; flag
`gOk cd 15 4 0 = okCol cd 0 4 4`), `AND`. -/
theorem seg_g4 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3444 [flag b] m)
        (callState s 3458 [flag (b && okCol s.executionEnv.calldata 0 4 4)] m') Gas.pG4 := by
  sorry

/-- `3458 … 3472`, open: `group [15, 5, 0]` (`group_call`; flag
`gOk cd 15 5 0 = okCol cd 0 5 4`), `AND`. -/
theorem seg_g5 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 6 ∧
      Reach (callState s 3458 [flag b] m)
        (callState s 3472 [flag (b && okCol s.executionEnv.calldata 0 5 4)] m') Gas.pG5 := by
  sorry

/-- `3472 … 3486`, open: `group [15, 6, 0]` (`group_call`; flag
`gOk cd 15 6 0 = okCol cd 0 6 4`), `AND`. -/
theorem seg_g6 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 6) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 7 ∧
      Reach (callState s 3472 [flag b] m)
        (callState s 3486 [flag (b && okCol s.executionEnv.calldata 0 6 4)] m') Gas.pG6 := by
  sorry

/-- `3486 … 3500`, open: `group [15, 0, 1]` (`group_call`; flag
`gOk cd 15 0 1 = okCol cd 1 0 4`), `AND`. -/
theorem seg_g7 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 7) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3486 [flag b] m)
        (callState s 3500 [flag (b && okCol s.executionEnv.calldata 1 0 4)] m') Gas.pG7 := by
  sorry

/-- `3500 … 3515`, open: `group [15, 1, 1]` (`group_call`; flag
`gOk cd 15 1 1 = okCol cd 1 1 4`), `AND`. -/
theorem seg_g8 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3500 [flag b] m)
        (callState s 3515 [flag (b && okCol s.executionEnv.calldata 1 1 4)] m') Gas.pG8 := by
  sorry

/-- `3515 … 3530`, open: `group [15, 2, 1]` (`group_call`; flag
`gOk cd 15 2 1 = okCol cd 1 2 4`), `AND`. -/
theorem seg_g9 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3515 [flag b] m)
        (callState s 3530 [flag (b && okCol s.executionEnv.calldata 1 2 4)] m') Gas.pG9 := by
  sorry

end MlDsaOpt87.Proofs
