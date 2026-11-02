import MlDsaOpt65.Main.S1.Tbl
/-! # Segment `1110 … 3093`: the 248 NTT zeta records (straight line). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- Proved in `Main/S1/Tbl.lean` (`seg_tbl_proof`; the 248 `MSTORE`s of
`nttRec` to `TBL`, the same table as ML-DSA-44). -/
theorem seg_tbl {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 1101 [flag b] m) (callState s 3084 [flag b] m') Gas.pTbl := by
  exact S1.seg_tbl_proof hs hI b

end MlDsaOpt65.Proofs
