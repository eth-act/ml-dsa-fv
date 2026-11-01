import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Ball
import MlDsaOpt44.Math
set_option warningAsError true
/-! # Segment `1126 … 1135`: `sib` (SampleInBall with its own `kf1` sponge), `AND`.

`sib_call` needs `RC1Table` and `SibFresh` (from the zeroed `MISC … ZH` and `BASES … HP`
of `Inv1`); its frame (`KS`, `KB`, `CW`, `BASES`, `IDX`, `NNEG`) avoids `RC4`, `ZH`, `HP`,
`ACC`. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

/-- `AND` of two flags (the code's flag accumulation). -/
theorem S2.and_flags_block {s : State} (hs : Ctx s) {m : ByteArray} (a b : Bool) :
    Reach (callState s 1133 [flag a, flag b] m) (callState s 1135 [flag (b && a)] m) 4 := by
  opt87_reach [232, 233] with [flag, MlDsaOpt44.Proofs.ite01_land]

theorem seg_sib {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv1 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv2 s.executionEnv.calldata m' ∧
      Reach (callState s 1126 [flag b] m)
        (callState s 1135 [flag (b && okC s.executionEnv.calldata)] m') Gas.pSib := by
  have hblk : Reach (callState s 1126 [flag b] m) (callState s Entry.sib [wd 1133, flag b] m) 14 := by
    opt87_reach [229, 230, 231] with [Entry.sib]
  have hfresh : SibFresh m :=
    ⟨ZeroOn.mono hI.zLow (by unfold MISC CW; omega) (by unfold CW ZH; omega),
     ZeroOn.mono hI.zHigh (le_refl _) (by unfold IDX HP; omega),
     ZeroOn.mono hI.zLow (by unfold MISC NNEG; omega) (by unfold NNEG ZH; omega)⟩
  obtain ⟨m', hpost, hbases, hfr, hcall⟩ := sib_call hs (ret := 1133) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    hI.rc1 hcd hfresh
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by avoids_tac), RC1Table.frame hI.rc1 hfr (by avoids_tac),
    ZAt.frame hI.z hfr (by avoids_tac), HPAt.frame hI.hp hfr (by avoids_tac), ⟨?_, hbases⟩,
    ZeroOn.frame (ZeroOn.mono hI.zHigh (by unfold BASES ACC; omega) (le_refl _)) hfr
      (by avoids_tac)⟩,
    ((hblk.trans hcall).trans (S2.and_flags_block hs _ b)).mono (by unfold Gas.pSib; omega)⟩
  intro hc
  unfold okC at hc
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc
  unfold cD
  rw [hcs]
  exact hpost c hcs

end MlDsaOpt87.Proofs
