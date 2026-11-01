import MlDsaOpt87.Main.S1.Tbl
/-! # Segment `1135 … 3118`: the 248 NTT zeta records -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- `1135 … 3118` (proved in `Main/S1/Tbl.lean`): the straight-line stores of the NTT zeta table `TBL`
(`TblAt`; same records as ML-DSA-44, mirror `MlDsaOpt44/Main/SegTbl.lean` +
`Main/Tbl/*`, relocated by `scripts/proofgen_port.py 87`). -/
theorem seg_tbl {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv2 cd m) (b : Bool) :
    ∃ m', Inv3 cd m' ∧
      Reach (callState s 1135 [flag b] m) (callState s 3118 [flag b] m') Gas.pTbl := by
  exact S1.seg_tbl_proof hs hI b

end MlDsaOpt87.Proofs
