import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Ball
import MlDsaOpt44.Math.SpongeG234
set_option warningAsError true
/-! # Segment `5876 … 5886`: `sib`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 5884 [flag a, flag b] m) (callState s 5886 [flag (b && a)] m) 4 := by
  opt44_reach [1935, 1936] with [flag, ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv6 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 5876 [flag b] m)
        (callState s 5886 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 5876 [flag b] m) (callState s 7240 [wd 5884, flag b] m) 15 := by
    opt44_reach [1931, 1932, 1933, 1934]
  obtain ⟨S, hS, hsc, hS0, -⟩ := hI.sc
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 5884) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    S hS hsc (cStream s.executionEnv.calldata) (cStream_size _) hI.cb
    (fun x hx => by
      have := le64_cStream (cd := s.executionEnv.calldata) (by unfold HDR at hcd; omega)
        (j := 1) (x := x) (by norm_num) hx
      rw [show 8 * (17 * 1 + x) = 136 + 8 * x by omega] at this
      rw [this, hS0]; rfl)
    hI.fresh
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

end MlDsaOpt44.Proofs
