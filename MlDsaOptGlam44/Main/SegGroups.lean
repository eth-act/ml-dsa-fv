import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Group
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegGroups.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segments `3430 … 3453`, `3453 … 3477`: the two pure ExpandA groups

`group` (columns 0 and 1), then one `MCOPY` of the fixed-up candidates
`ABUF[0, 256)` to the column's side buffer (`CW`, `HP`). -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem aD_lt {cd : ByteArray} {s : Nat} (h : okCol cd s = true) {r : Nat} (hr : r < 4) {t : Nat}
    (ht : t < 256) : ((aD cd r s)[t]!).toNat < Fips204.q := by
  unfold okCol at h
  rw [List.all_eq_true] at h
  have hsome := h r (List.mem_range.mpr hr)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  obtain ⟨-, hrange⟩ := rejNTTPoly_range _ a ha
  have := hrange t ht
  omega

/-- A pure group and the copy of its candidates to `dst`. -/
theorem group_copy {s : State} (hs : Ctx s) {m : ByteArray} {b : Bool} {col : Nat}
    {pc ret : Nat} (i : Fin 34557) (cost : Nat) {dst : Nat}
    (hblk : Reach (callState s pc [flag b] m) (callState s 20814 [wd 15, wd col, wd 0, wd ret, flag b] m)
      cost)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16)
    (hand : ∀ M, Reach (callState s ret [flag (okCol s.executionEnv.calldata col), flag b] M)
      (callState s (ret + 11) [wd dst, wd ABUF, wd 8192, flag (b && okCol s.executionEnv.calldata col)] M) 13)
    (hi : instrAt i.val = .base (.op .MCOPY)) (hpc : pcAt i.val = ret + 11) (hdst : dst + 8192 ≤ 0x10220)
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) (hcol : col < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', ColAt m' dst s.executionEnv.calldata col ∧
      FrameExcept m m' (groupFrame ++ [(dst, dst + 8192)]) ∧
      Reach (callState s pc [flag b] m)
        (callState s (ret + 12) [flag (b && okCol s.executionEnv.calldata col)] m')
        (cost + Gas.group + 13 + 771) := by
  obtain ⟨m1, hpost, hfr, hc⟩ := group_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hret) m hrc hrho hcol hcd
  have hsz : 2616 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hmc := reach_mcopy hs i (d := dst) (src := ABUF) (n := 8192)
    (rest := [flag (b && okCol s.executionEnv.calldata col)]) (m := m1) hi hpc (by omega)
    (by unfold ABUF; omega) (by omega) (by omega) (by omega) (by unfold ABUF; omega) (by simp)
  refine ⟨_, fun hok t ht => ?_, hfr.trans (FrameExcept.mcopy _ _ _ _),
    ((hblk.trans hc).trans ((hand m1).trans hmc)).mono (by omega)⟩
  rw [word_mcopy _ (by omega) (by omega), show ABUF + (dst + 32 * t - dst) = ABUF + 32 * t by omega]
  exact hpost hok t ht

theorem invX_of_inv4 {cd m : ByteArray} (hI : Inv4 cd m) : InvX cd m :=
  ⟨hI.rc4, hI.rc1, hI.tbl, hI.zhat, hI.rho,
    hI.zHigh.mono (by unfold BASES IDX; omega) (by unfold IDX FIN; omega),
    hI.zMisc.mono (by unfold MISC NNEG; omega) (by unfold NNEG TBL; omega)⟩

theorem InvX.frame {cd m m' : ByteArray} {rs : List (Nat × Nat)} (hI : InvX cd m)
    (h : FrameExcept m m' rs) (h1 : Avoids rs RC4 (RC4 + 768)) (h2 : Avoids rs RC1 (RC1 + 768))
    (h3 : Avoids rs TBL (TBL + 7936)) (h4 : Avoids rs ZH (ZH + 8192)) (h5 : Avoids rs RHO1 (RHO1 + 256))
    (h6 : Avoids rs IDX (IDX + 256)) (h7 : Avoids rs NNEG (NNEG + 64)) : InvX cd m' :=
  ⟨hI.rc4.frame h h1, hI.rc1.frame h h2, hI.tbl.frame h h3, hI.zhat.frame h h4, hI.rho.frame h h5,
    hI.zIdx.frame h h6, hI.zNeg.frame h h7⟩

theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG0 s.executionEnv.calldata m' ∧ word m' FLAG = word m FLAG ∧  -- glam: `FLAG` kept
      Reach (callState s 2389 [flag b] m)
        (callState s 2412 [flag (b && okCol s.executionEnv.calldata 0)] m') Gas.pG0 := by
  have hb1 : Reach (callState s 2389 [flag b] m) (callState s 20814 [wd 15, wd 0, wd 0, wd 2400, flag b] m)
      21 := by
    glam44_rreach [916, 917, 918, 919, 920, 921]
  obtain ⟨m', hc0, hfr, hR⟩ := group_copy hs ⟨927, by norm_num⟩ 21 (dst := CW) hb1
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam44_rreach [922, 923, 924, 925, 926] with [flag, ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold CW; omega) hI.rc4 hI.rho (by norm_num : (0 : Nat) < 4) hcd
  refine ⟨m', ⟨(invX_of_inv4 hI).frame hfr (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac), hc0⟩,
    word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG groupFrame; avoids_tac) le_rfl le_rfl,
    hR.mono (by unfold Gas.pG0; generalize Gas.group = g; omega)⟩

theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG0 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG1 s.executionEnv.calldata m' ∧ word m' FLAG = word m FLAG ∧  -- glam: `FLAG` kept
      Reach (callState s 2412 [flag b] m)
        (callState s 2436 [flag (b && okCol s.executionEnv.calldata 1)] m') Gas.pG1 := by  -- glam: switch at 2436
  have hb1 : Reach (callState s 2412 [flag b] m) (callState s 20814 [wd 15, wd 1, wd 0, wd 2424, flag b] m)
      22 := by
    glam44_rreach [928, 929, 930, 931, 932, 933]
  obtain ⟨m', hc1, hfr, hR⟩ := group_copy hs ⟨939, by norm_num⟩ 22 (dst := HP) hb1
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam44_rreach [934, 935, 936, 937, 938] with [flag, ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold HP; omega) hI.rc4 hI.rho (by norm_num : (1 : Nat) < 4) hcd
  refine ⟨m', ⟨⟨hI.toInvX.frame hfr (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac)
    (by unfold groupFrame; avoids_tac) (by unfold groupFrame; avoids_tac),
    hI.c0.frame hfr (by unfold groupFrame; avoids_tac)⟩, hc1⟩,
    word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG groupFrame; avoids_tac) le_rfl le_rfl,
    hR.mono (by unfold Gas.pG1; generalize Gas.group = g; omega)⟩

end MlDsaOptGlam44.Proofs
