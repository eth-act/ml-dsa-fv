import MlDsaOptGlam44.Main.SegSib
import MlDsaOptGlam44.Main.Alt.Inv
set_option maxHeartbeats 0
set_option warningAsError true
/-! # Long-message schedule, `6020 … 6030`: `sib` with `FLAG = 0`, `AND`

As `Main/SegSib.lean`, with `sib_call0`: both blocks of the SampleInBall
stream are in `CB[0, 34)`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem seg_sibA {s : State} (hs : Ctx s) {m : ByteArray}
    (hI : Inv6A s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 6020 [flag b] m)
        (callState s 6030 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 6020 [flag b] m) (callState s 7596 [wd 6028, flag b] m) 15 := by
    glam44_rreach [2096, 2097, 2098, 2099]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call0 hs (ret := 6028) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (cStream s.executionEnv.calldata) (cStream_size _) hI.cb hI.fresh hI.flag0
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
