import MlDsaOptGlam65.Main.S1.Tbl
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegTbl.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `1110 … 3093`: the 248 NTT zeta records (straight line). -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

/-- Proved in `Main/S1/Tbl.lean` (`seg_tbl_proof`; the 248 `MSTORE`s of
`nttRec` to `TBL`, the same table as ML-DSA-44). -/
theorem seg_tbl {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 124 [flag b] m) (callState s 2043 [flag b] m') Gas.pTbl := by
  exact S1.seg_tbl_proof hs hI b

end MlDsaOptGlam65.Proofs
