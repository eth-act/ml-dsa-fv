import MlDsaOpt44.Main.Tbl.Blocks
/-! # Segment `1085 … 3068`: the 248 NTT zeta records (straight line). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_tbl {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 1076 [flag b] m) (callState s 3059 [flag b] m') Gas.pTbl := by
  exact seg_tbl_proof hs hI b


end MlDsaOpt44.Proofs
