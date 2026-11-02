import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Fn.Ball
import MlDsaOpt44.Math
import MlDsaOptGlam87.Main.S1.Tac
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegSib.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `6663 … 6672`: `sib` (SampleInBall with its own `kf1` sponge), `AND`.

v4: `sib` runs after μ. `sib_call` needs `RC1Table` and `SibFresh` (`CW`, `IDX`, `NNEG`
zero: `Inv6.fresh`); its frame (`KS`, `KB`, `KZ`, `CW`, `BASES`, `IDX`, `NNEG`) avoids
`TBL`, `HP`, `ACC`, `FIN`. -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem S2.and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 5629 [flag a, flag b] m) (callState s 5631 [flag (b && a)] m) 4 := by
  glam87_rreach [1991, 1992] with [flag, MlDsaOpt44.Proofs.ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 5622 [flag b] m)
        (callState s 5631 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 5622 [flag b] m) (callState s Entry.sib [wd 5629, flag b] m) 14 := by
    glam87_rreach [1988, 1989, 1990] with [Entry.sib]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 5629) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    hI.rc1 hcd hI.fresh
  refine ⟨m', ⟨RC1Table.frame hI.rc1 hfr (by avoids_tac), TblAt.frame hI.tbl hfr (by avoids_tac),
    HPAt.frame hI.hp hfr (by avoids_tac), AccAt.frame hI.acc hfr (by avoids_tac), ⟨?_, hbases⟩,
    FinMu.frame hI.fmu hfr (by avoids_tac)⟩,
    ((hblk.trans hcall).trans (S2.and_flags_block hs _ b)).mono (by unfold Gas.pSib; omega)⟩
  intro hc
  unfold okC at hc
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc
  unfold cD
  rw [hcs]
  exact hpost c hcs

end MlDsaOptGlam87.Proofs
