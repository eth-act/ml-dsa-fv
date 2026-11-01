import MlDsaOpt44.Main.Base
set_option warningAsError true
/-! # Segment `5936 … 5963`: `tbuild`, `csum`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_ct {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv7 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv8 s.executionEnv.calldata m' ∧
      Reach (callState s 5936 [flag b] m) (callState s 5963 [flag b] m') Gas.pCt := by
  have hb1 : Reach (callState s 5936 [flag b] m) (callState s 13924 [wd TT, wd 32, wd 5948, flag b] m)
      20 := by
    opt44_reach [1990, 1991, 1992, 1993, 1994] with [TT]
  obtain ⟨m1, htt, hfr1, hc1⟩ := tbuild_call hs (ret := 5948) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hcd
  have hb2 : Reach (callState s 5948 [flag b] m1) (callState s 14732 [wd SP, wd TT, wd 5962, flag b] m1)
      21 := by
    opt44_reach [1995, 1996, 1997, 1998, 1999, 2000] with [TT, SP]
  obtain ⟨m2, hsp, hfr2, hc2⟩ := csum_call hs (ret := 5962) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
  have hb3 : Reach (callState s 5962 [flag b] m2) (callState s 5963 [flag b] m2) 1 := by
    opt44_reach [2001]
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


end MlDsaOpt44.Proofs
