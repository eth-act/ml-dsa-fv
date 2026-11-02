import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Ball
import MlDsaOpt65.Math
set_option warningAsError true
/-! # Segment `6172 … 6555`: `sib` (stream `cStream cd` from `CB`), `AND`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem S2.and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 6180 [flag a, flag b] m) (callState s 6182 [flag (b && a)] m) 4 := by
  opt65_reach [2109, 2110] with [flag, MlDsaOpt44.Proofs.ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv6 cd m) (b : Bool) :
    ∃ m', Inv7 cd m' ∧
      Reach (callState s 6172 [flag b] m) (callState s 6182 [flag (b && okC cd)] m') Gas.pSib := by
  have hblk : Reach (callState s 6172 [flag b] m) (callState s Entry.sib [wd 6180, flag b] m) 15 := by
    opt65_reach [2105, 2106, 2107, 2108] with [Entry.sib]
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 6180) (tail := [flag b])
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

end MlDsaOpt65.Proofs
