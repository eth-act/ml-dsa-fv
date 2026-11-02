import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Ball
import MlDsaOpt65.Math
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegSib.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `5843 … 6555`: `sib` (stream `cStream cd` from `CB`), `AND`. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem S2.and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 5851 [flag a, flag b] m) (callState s 5853 [flag (b && a)] m) 4 := by
  glam65_rreach [2077, 2078] with [flag, MlDsaOpt44.Proofs.ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv6 cd m) (b : Bool) :
    ∃ m', Inv7 cd m' ∧
      Reach (callState s 5843 [flag b] m) (callState s 5853 [flag (b && okC cd)] m') Gas.pSib := by
  have hblk : Reach (callState s 5843 [flag b] m) (callState s Entry.sib [wd 5851, flag b] m) 15 := by
    glam65_rreach [2073, 2074, 2075, 2076] with [Entry.sib]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 5851) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (cStream cd) (cStream_size cd) hI.cb hI.fresh
  refine ⟨m', ⟨RC1Table.frame hI.rc1 hfr (by avoids_tac), TblAt.frame hI.tbl hfr (by avoids_tac),
    HPAt.frame hI.hp hfr (by avoids_tac), AccAt.frame hI.acc hfr (by avoids_tac),
    FinMu.frame hI.fmu hfr (by avoids_tac), ?_, hbases⟩,
    ((hblk.trans hcall).trans (S2.and_flags_block hs _ b)).mono (by unfold Gas.pSib; omega)⟩
  intro hc
  unfold okC at hc
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc
  have hc' : Fips204.sampleInBallOf P (cStream cd) = some c := hcs
  unfold cD
  rw [hcs]
  exact hpost c hc'

end MlDsaOptGlam65.Proofs
