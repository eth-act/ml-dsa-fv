import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Ct
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegCt.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `5886 … 5913`: `tbuild`, `csum`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem seg_ct {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv7 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv8 s.executionEnv.calldata m' ∧
      Reach (callState s 6030 [flag b] m) (callState s 6057 [flag b] m') Gas.pCt := by
  have hb1 : Reach (callState s 6030 [flag b] m) (callState s 21045 [wd TT, wd 32, wd 6042, flag b] m)
      20 := by
    glam44_rreach [2102, 2103, 2104, 2105, 2106] with [TT]
  obtain ⟨m1, htt, hfr1, hc1⟩ := tbuild_call hs (ret := 6042) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hcd
  have hb2 : Reach (callState s 6042 [flag b] m1) (callState s 21853 [wd SP, wd TT, wd 6056, flag b] m1)
      21 := by
    glam44_rreach [2107, 2108, 2109, 2110, 2111, 2112] with [TT, SP]
  obtain ⟨m2, hsp, hfr2, hc2⟩ := csum_call hs (ret := 6056) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (fun i hi => by
      have : i < 39 := hi
      rw [word_frame hfr1 (lo := BASES) (hi := BASES + 2048) (by avoids_tac) (by omega) (by omega)]
      exact hI.bases i hi)
  have hb3 : Reach (callState s 6056 [flag b] m2) (callState s 6057 [flag b] m2) 1 := by
    glam44_rreach [2113]
  refine ⟨m2, ⟨(hI.rc1.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac),
    (hI.tbl.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac),
    (hI.hp.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac),
    (hI.acc.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac),
    (hI.fmu.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac), ?_⟩,
    ((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).mono (by unfold Gas.pCt; omega)⟩
  intro hc
  have hc0 := hc
  unfold okC at hc0
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc0
  have hc' : Fips204.sampleInBallOf (cStream s.executionEnv.calldata) = some c := hcs
  have hcD : cD s.executionEnv.calldata = c := by unfold cD; rw [hcs]; rfl
  obtain ⟨hsz, hco⟩ := sampleInBallOf_coeffs _ c hc'
  have hrep : CRep m1 c := by
    have := hI.crep hc
    rw [hcD] at this
    exact this.frame hfr1 (by avoids_tac) (by avoids_tac) (by avoids_tac)
  rw [hcD]
  exact hsp c hsz hco hrep htt


end MlDsaOptGlam44.Proofs
