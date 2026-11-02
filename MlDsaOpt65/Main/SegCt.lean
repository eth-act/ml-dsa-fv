import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.TBuild
import MlDsaOpt65.Fn.Csum
import MlDsaOpt65.Math
set_option warningAsError true
/-! # Segment `6555 … 6610`: `tbuild`, `csum` for both row groups.

`tbuild [TT, 32]`, `csum [SP, TT]` (rows 0–3), `tbuild [TT + 0x1800, 0x520]`,
`csum [SP + 0x2000, TT + 0x1800]` (rows 4–7 of the window table; rows 4, 5 used). The
window tables overlay `ABUF`/`FL`, the sums `ZH`/`ZH2` (dead after ExpandA). -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

theorem seg_ct {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv7 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv8 s.executionEnv.calldata m' ∧
      Reach (callState s 6182 [flag b] m) (callState s 6237 [flag b] m') Gas.pCt := by
  have hb1 : Reach (callState s 6182 [flag b] m)
      (callState s Entry.tbuild [wd TT, wd 32, wd 6194, flag b] m) 20 := by
    opt65_reach [2111, 2112, 2113, 2114, 2115] with [TT, Entry.tbuild]
  obtain ⟨m1, htt1, hfr1, hc1⟩ := tbuild_call hs (ret := 6194) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (tp := TT) (off := 32) (by unfold TT; omega) (by unfold HDR at hcd; omega)
  have hb2 : Reach (callState s 6194 [flag b] m1)
      (callState s Entry.csum [wd (SP + 0x2000 * 0), wd (TT + 0x1800 * 0), wd 6208, flag b] m1)
      21 := by
    opt65_reach [2116, 2117, 2118, 2119, 2120, 2121] with [TT, SP, Entry.csum]
  have hbases1 : ∀ i, i < P.tau → word m1 (BASES + 32 * i) ≤ 6112 := fun i hi => by
    have : i < 49 := hi
    rw [word_frame hfr1 (lo := BASES) (hi := BASES + 2048) (by avoids_tac) (by omega) (by omega)]
    exact hI.bases i hi
  obtain ⟨m2, hsp1, hfr2, hc2⟩ := csum_call hs (ret := 6208) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (g := 0) (by norm_num) hbases1
  have hb3 : Reach (callState s 6208 [flag b] m2)
      (callState s Entry.tbuild [wd (TT + 0x1800 * 1), wd 1312, wd 6222, flag b] m2) 21 := by
    opt65_reach [2122, 2123, 2124, 2125, 2126, 2127] with [TT, Entry.tbuild]
  obtain ⟨m3, htt2, hfr3, hc3⟩ := tbuild_call hs (ret := 6222) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
    (tp := TT + 0x1800 * 1) (off := 1312) (by unfold TT; omega) (by unfold HDR at hcd; omega)
  have hb4 : Reach (callState s 6222 [flag b] m3)
      (callState s Entry.csum [wd (SP + 0x2000 * 1), wd (TT + 0x1800 * 1), wd 6236, flag b] m3)
      21 := by
    opt65_reach [2128, 2129, 2130, 2131, 2132, 2133] with [TT, SP, Entry.csum]
  have hbases3 : ∀ i, i < P.tau → word m3 (BASES + 32 * i) ≤ 6112 := fun i hi => by
    have : i < 49 := hi
    rw [word_frame hfr3 (lo := BASES) (hi := BASES + 2048) (by avoids_tac) (by omega) (by omega),
      word_frame hfr2 (lo := BASES) (hi := BASES + 2048) (by avoids_tac) (by omega) (by omega)]
    exact hbases1 i hi
  obtain ⟨m4, hsp2, hfr4, hc4⟩ := csum_call hs (ret := 6236) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (g := 1) (by norm_num) hbases3
  have hb5 : Reach (callState s 6236 [flag b] m4) (callState s 6237 [flag b] m4) 1 := by
    opt65_reach [2134]
  refine ⟨m4, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ((((((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).trans hc3).trans hb4).trans hc4).trans
      hb5).mono (by unfold Gas.pCt; omega)⟩
  · exact RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame hI.rc1 hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  · exact TblAt.frame (TblAt.frame (TblAt.frame (TblAt.frame hI.tbl hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  · exact HPAt.frame (HPAt.frame (HPAt.frame (HPAt.frame hI.hp hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  · exact AccAt.frame (AccAt.frame (AccAt.frame (AccAt.frame hI.acc hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  · exact FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame hI.fmu hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  intro hc g hg t ht
  have hc0 := hc
  unfold okC at hc0
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp hc0
  have hc' : Fips204.sampleInBallOf P (cStream s.executionEnv.calldata) = some c := hcs
  have hcD : cD s.executionEnv.calldata = c := by unfold cD; rw [hcs]; rfl
  obtain ⟨hsz, hco⟩ := sampleInBallOf_coeffs _ c hc'
  have hrep : CRep m c := by
    have := hI.crep hc
    rwa [hcD] at this
  have hrep1 : CRep m1 c := hrep.frame hfr1 (by avoids_tac) (by avoids_tac) (by avoids_tac)
  have hrep3 : CRep m3 c :=
    (hrep1.frame hfr2 (by avoids_tac) (by avoids_tac) (by avoids_tac)).frame hfr3
      (by avoids_tac) (by avoids_tac) (by avoids_tac)
  rw [hcD]
  interval_cases g
  · rw [word_frame hfr4 (lo := SP) (hi := SP + 8192) (by avoids_tac) (by omega) (by omega),
      word_frame hfr3 (lo := SP) (hi := SP + 8192) (by avoids_tac) (by omega) (by omega)]
    exact hsp1 32 c hsz hco hrep1 (by simpa using htt1) t ht
  · exact hsp2 1312 c hsz hco hrep3 htt2 t ht

end MlDsaOpt65.Proofs
