import MlDsaOptGlam44.Main.Alt.GrpA
import MlDsaOptGlam44.Main.Alt.GrpB
import MlDsaOptGlam44.Main.Alt.GrpK
import MlDsaOptGlam44.Main.Alt.Acc
import MlDsaOptGlam44.Main.Alt.Zd
import MlDsaOptGlam44.Main.Alt.Mu
import MlDsaOptGlam44.Main.Alt.Sib
import MlDsaOptGlam44.Main.SegSwitch
import MlDsaOptGlam44.Main.SegWin
import MlDsaOptGlam44.Gas
set_option warningAsError true
/-!
# The long-message schedule (`|M| ≥ 342`): `2436 … 6030`

The jump to `alt` (`switch_alt_block`), the previous schedule's three mixed
groups (`Main/Alt/GrpA.lean`, `GrpB.lean`: rows 0 … 2 of columns 2, 3 with
`pk`'s blocks in slot 3; `GrpK.lean`: c̃'s stream, μ's blocks 0 … 4 through
`mub0` / `mulong` / `mub`, `(A[3][3], A[3][2])`), `pass3f4b` (`Alt/Acc.lean`),
then the shared code with `FLAG = 0`: the side buffers and hints (`Alt/Zd.lean`),
μ (from `MU`, or `hash_mu` from the slot state in `KS` via `muimg`, `Alt/Mu.lean`),
SampleInBall (`sib_call0`, `Alt/Sib.lean`). Budget `Gas.pAlt` (`Gas.lean`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra
open MlDsaOptGlam44.Proofs.Ex
open MlDsaOptGlam44.Proofs.Alt

set_option maxRecDepth 10000 in
theorem pAlt_eq (mlen : Nat) : Gas.pAlt mlen =
    24 + costA + costB + costK + 18 + Gas.pass3f4b + 1 + Gas.pZd + Gas.pMuA mlen + Gas.pSib := by
  unfold Gas.pAlt Gas.pAltX costA costB costK cLong
  generalize Gas.ginit = a1; generalize Gas.trabs 5 = a2; generalize Gas.trabs 3 = a3
  generalize Gas.kf4 = a4; generalize Gas.blk = a5; generalize Gas.blkh = a6; generalize Gas.cext 8 = a7
  generalize Gas.gfix 3 = a8; generalize Gas.gfix 2 = a9; generalize Gas.mub0 = a10
  generalize Gas.mub = a11; generalize Gas.cext 17 = a12; generalize Gas.pass3f4b = a13
  generalize Gas.pZd = a14; generalize Gas.pMuA mlen = a15; generalize Gas.pSib = a16
  omega

theorem okA_alt (cd : ByteArray) :
    (((((okZ cd && okCol cd 0) && okCol cd 1) && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd) =
      (okZ cd && okA cd) := by
  rw [← winFlag_and, winFlag, Bool.and_assoc _ (okCol3 cd 3), Bool.and_comm (okCol3 cd 3),
    ← Bool.and_assoc]

set_option maxHeartbeats 400000 in
theorem seg_alt {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (hge : 4074 ≤ s.executionEnv.calldata.size)
    (hfl : word m FLAG = 0) :
    ∃ m', Inv7 s.executionEnv.calldata m' ∧
      Reach (callState s 2436
          [flag ((okZ s.executionEnv.calldata && okCol s.executionEnv.calldata 0) &&
            okCol s.executionEnv.calldata 1)] m)
        (callState s 6030 [flag (ok2 s.executionEnv.calldata && okC s.executionEnv.calldata)] m')
        (Gas.pAlt (mlenOf s.executionEnv.calldata)) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  set cd := s.executionEnv.calldata with hcdv
  have hlong : ¬ mlenOf cd ≤ 69 := by unfold mlenOf; omega
  set b0 := (okZ cd && okCol cd 0) && okCol cd 1 with hb0
  have R0 := switch_alt_block hs (m := m) b0 hge
  obtain ⟨m1, hks1, hsb1, hrc1, hf1, R1⟩ := grpA hs hcd (b := b0) hI.rc4 hI.rho
  obtain ⟨m2, -, hsb2, htrl2, hrc2, hf2, R2⟩ := grpB hs hcd (b := b0 && okCol3 cd 2) hrc1
    (hI.rho.frame hf1 (by alt_frame)) hks1
  have hrho2 : Rho1At m2 cd := (hI.rho.frame hf1 (by alt_frame)).frame hf2 (by alt_frame)
  obtain ⟨m3, hab3, hmu3, hks3, hcb3, hf3, R3⟩ := grpK hs hcd hlong
    (b := (b0 && okCol3 cd 2) && okCol3 cd 3) hrc2 hrho2 htrl2
  -- AND, pass3f4b, `altj`
  have gP : Reach (callState s 5071 [flag (Ex.okE cd), flag ((b0 && okCol3 cd 2) && okCol3 cd 3)] m3)
      (callState s 17297 [wd 5080, flag (((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd)] m3) 18 := by
    glam44_rreach [1695, 1696, 1697, 1698, 1699] with [flag, ite01_land]
  obtain ⟨m4, hw4, hf4, hc4⟩ := pass3f4b_call hs (ret := 5080)
    (tail := [flag (((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
  have gJ : Reach (callState s 5080 [flag (((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd)] m4)
      (callState s 5081 [flag (((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd)] m4) 1 := by
    glam44_rreach [1700]
  -- `InvWA` at 5081
  have hf13 := (hf1.trans hf2).trans hf3
  have hfA := hf13.trans hf4
  have hW : InvWA cd m4 := by
    refine ⟨RC1Table.frame hI.rc1 hfA (by alt_frame), TblAt.frame hI.tbl hfA (by alt_frame),
      accAt_alt (hI.zhat.frame hf13 (by alt_frame)) (hI.c0.frame hf13 (by alt_frame))
        (hI.c1.frame hf13 (by alt_frame)) (Col3Lo.frame (Col3Lo.frame hsb1 hf2 (by alt_frame)) hf3 (by alt_frame))
        (Col3Lo.frame hsb2 hf3 (by alt_frame))
        (fun hok => hab3 (by
          unfold Ex.okE; unfold okA at hok; rw [List.all_eq_true] at hok
          have h3 := hok 3 (by simp); rw [List.all_eq_true] at h3
          rw [h3 3 (by simp), h3 2 (by simp)]; rfl)) hw4,
      fun h613 x hx => ?_, fun h613 => ?_, fun x hx => ?_, ZeroOn.frame hI.zIdx hfA (by alt_frame),
      ZeroOn.frame hI.zNeg hfA (by alt_frame), ?_⟩
    · rw [word_frame hf4 (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by alt_frame) (by omega) (by omega)]
      exact hmu3 h613 x hx
    · obtain ⟨S, hS, hks, h1⟩ := hks3 h613
      exact ⟨S, hS, KS4.frame hks hf4 (by alt_frame), h1⟩
    · rw [word_frame hf4 (a := CB + 32 * x) (lo := CB) (hi := CB + 1088) (by alt_frame) (by omega) (by omega)]
      exact hcb3 x hx
    · rw [word_frame hfA (lo := FLAG) (hi := FLAG + 32) (by alt_frame) le_rfl le_rfl]; exact hfl
  -- the tail with `FLAG = 0`
  obtain ⟨m5, hI5, R5⟩ := seg_zdA hs hcd hW (((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd)
  obtain ⟨m6, hI6, R6⟩ := seg_muA hs hcd hI5 ((((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd) && okH cd)
  obtain ⟨m7, hI7, R7⟩ := seg_sibA hs hI6 ((((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd) && okH cd)
  refine ⟨m7, hI7, ?_⟩
  have hflag : ((((b0 && okCol3 cd 2) && okCol3 cd 3) && Ex.okE cd) && okH cd) = ok2 cd := by
    rw [hb0, okA_alt]; rfl
  have hR := ((((((((R0.trans R1).trans R2).trans R3).trans gP).trans hc4).trans gJ).trans R5).trans R6).trans R7
  rw [hflag] at hR
  refine hR.mono (le_of_eq ?_)
  rw [pAlt_eq]

end MlDsaOptGlam44.Proofs
