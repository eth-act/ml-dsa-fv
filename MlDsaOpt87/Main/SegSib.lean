import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Ball
import MlDsaOpt44.Math
import MlDsaOpt87.Main.S1.Tac
set_option warningAsError true
/-! # Segment `6663 … 6672`: `sib` (SampleInBall with its own `kf1` sponge), `AND`.

v4: `sib` runs after μ. `sib_call` needs `RC1Table` and `SibFresh` (`CW`, `IDX`, `NNEG`
zero: `Inv6.fresh`); its frame (`KS`, `KB`, `KZ`, `CW`, `BASES`, `IDX`, `NNEG`) avoids
`TBL`, `HP`, `ACC`, `FIN`. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem S2.and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 6670 [flag a, flag b] m) (callState s 6672 [flag (b && a)] m) 4 := by
  opt87_reach [2209, 2210] with [flag, MlDsaOpt44.Proofs.ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 6663 [flag b] m)
        (callState s 6672 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 6663 [flag b] m) (callState s Entry.sib [wd 6670, flag b] m) 14 := by
    opt87_reach [2206, 2207, 2208] with [Entry.sib]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 6670) (tail := [flag b])
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

end MlDsaOpt87.Proofs
