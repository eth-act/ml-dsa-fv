import MlDsaOptGlam87.Main.S1.Tbl
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegTbl.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-! # Segment `1117 … 3100`: the 248 NTT zeta records -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `1117 … 3100` (proved in `Main/S1/Tbl.lean`): the straight-line stores of the NTT zeta table `TBL`
(`TblAt`; same records as ML-DSA-44, mirror `MlDsaOpt44/Main/SegTbl.lean` +
`Main/Tbl/*`, relocated by `scripts/proofgen_port.py 87`). -/
theorem seg_tbl {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 140 [flag b] m) (callState s 2059 [flag b] m') Gas.pTbl := by
  exact S1.seg_tbl_proof hs hI b

end MlDsaOptGlam87.Proofs
