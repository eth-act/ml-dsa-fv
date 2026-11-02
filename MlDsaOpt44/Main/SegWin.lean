import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Group
/-! # Segment `3875 … 4973`: the packed window and the fused accumulation

Eight `kf4` calls (`emit_window44`): slot 0 runs `tr`'s blocks 5 … 9 (calls
15 … 19), then `c̃` (20), then `A[1][3]` (21, 22); slot 1 runs `A[0][3]`
(15 … 19), μ's block 0 (20), `A[2][3]` (21, 22); slots 2, 3 run `A[1][3]`,
`A[2][3]` (15 … 17) and `A[3][3]`, `A[3][2]` (18 … 22). `A[1][3]`, `A[2][3]`
pause after call 17 (image `SAVE0`) and resume in slots 0, 1; the staged
column-3 candidates are merged (`lmerge`) in `ACC` / `BASES`. Then the two
fix-ups (`E = (A[3][3], A[3][2])`, copied to `SB + 8192`; `B3 = A[0 … 2][3]`)
and `pass3f4`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The flags ANDed by the groups and the window give `okZ ∧ okA`. -/
def winFlag (cd : ByteArray) : Bool :=
  ((okZ cd && okCol cd 0) && okCol cd 1) && okCol3 cd 2

theorem seg_win {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG2 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3875 [flag (winFlag s.executionEnv.calldata)] m)
        (callState s 4973 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pWin := by
  sorry

end MlDsaOpt44.Proofs
