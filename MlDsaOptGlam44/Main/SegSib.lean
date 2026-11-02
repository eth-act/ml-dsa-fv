import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Ball
import MlDsaOpt44.Math.SpongeG234
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegSib.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `6020 … 5886`: `sib`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 6028 [flag a, flag b] m) (callState s 6030 [flag (b && a)] m) 4 := by
  glam44_rreach [2100, 2101] with [flag, ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 6020 [flag b] m)
        (callState s 6030 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 6020 [flag b] m) (callState s 7596 [wd 6028, flag b] m) 15 := by
    glam44_rreach [2096, 2097, 2098, 2099]
  obtain ⟨S, hS, hsc, hS0, -⟩ := hI.sc
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 6028) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    S hS hsc (cStream s.executionEnv.calldata) (cStream_size _) hI.cb
    (fun x hx => by
      have := le64_cStream (cd := s.executionEnv.calldata) (by unfold HDR at hcd; omega)
        (j := 1) (x := x) (by norm_num) hx
      rw [show 8 * (17 * 1 + x) = 136 + 8 * x by omega] at this
      rw [this, hS0]; rfl)
    hI.fresh hI.flag
  refine ⟨m', ⟨hI.rc1.frame hfr (by avoids_tac), hI.tbl.frame hfr (by avoids_tac),
    hI.hp.frame hfr (by avoids_tac), hI.acc.frame hfr (by avoids_tac),
    hI.fmu.frame hfr (by avoids_tac), ?_, hbases⟩,
    ((hblk.trans hcall).trans (and_flags_block hs _ b)).mono (by unfold Gas.pSib; omega)⟩
  intro hc
  unfold okC at hc
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc
  have hc' : Fips204.sampleInBallOf (cStream s.executionEnv.calldata) = some c := hcs
  unfold cD
  rw [hcs]
  exact hpost c hc'

end MlDsaOptGlam44.Proofs
