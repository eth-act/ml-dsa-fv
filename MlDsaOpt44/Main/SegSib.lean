import MlDsaOpt44.Main.Base
set_option warningAsError true
/-! # Segment `5926 … 5936`: `sib`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 5934 [flag a, flag b] m) (callState s 5936 [flag (b && a)] m) 4 := by
  opt44_reach [1988, 1989] with [flag, ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv6 cd m) (b : Bool) :
    ∃ m', Inv7 cd m' ∧
      Reach (callState s 5926 [flag b] m) (callState s 5936 [flag (b && okC cd)] m') Gas.pSib := by
  have hblk : Reach (callState s 5926 [flag b] m) (callState s 7301 [wd 5934, flag b] m) 15 := by
    opt44_reach [1984, 1985, 1986, 1987]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 5934) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (cStream cd) (cStream_size cd) hI.cb hI.fresh
  refine ⟨m', ⟨hI.rc1.frame hfr (by avoids_tac), hI.tbl.frame hfr (by avoids_tac),
    hI.hp.frame hfr (by avoids_tac), hI.acc.frame hfr (by avoids_tac),
    hI.fmu.frame hfr (by avoids_tac), ?_, hbases⟩,
    ((hblk.trans hcall).trans (and_flags_block hs _ b)).mono (by unfold Gas.pSib; omega)⟩
  intro hc
  unfold okC at hc
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc
  have hc' : Fips204.sampleInBallOf (cStream cd) = some c := hcs
  unfold cD
  rw [hcs]
  exact hpost c hc'


end MlDsaOpt44.Proofs
