import MlDsaOptGlam44.Main.SegZd
import MlDsaOptGlam44.Main.Alt.Inv
set_option maxHeartbeats 0
set_option warningAsError true
/-! # Long-message schedule, `5081 … 5183`: zero the side buffers, HintBitUnpack

The code of `Main/SegZd.lean` (`seg_zd`), on the long-message schedule's
invariants (`InvWA → InvHA`). -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem seg_zdA {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvWA s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvHA s.executionEnv.calldata m' ∧
      Reach (callState s 5081 [flag b] m)
        (callState s 5183 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  have hsz : 2616 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hb0 : Reach (callState s 5081 [flag b] m)
      (callState s 5087 [flag b] (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) CW)) 9 := by
    glam44_rreach [1701, 1702, 1703, 1704] with [CW]
  have hz0 := zeroOn_mstore0 m CW
  obtain ⟨m1, hz1, hf1, hr1⟩ := zd_double hs ⟨1708, by norm_num⟩ (pc := 5087) (pc' := 5095) (k := 32) (rest := [flag b])
    (by glam44_rreach [1705, 1706, 1707] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz0 (by simp) (by norm_num)
  obtain ⟨m2, hz2, hf2, hr2⟩ := zd_double hs ⟨1712, by norm_num⟩ (pc := 5096) (pc' := 5104) (k := 64) (rest := [flag b])
    (by glam44_rreach [1709, 1710, 1711] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz1 (by simp) (by norm_num)
  obtain ⟨m3, hz3, hf3, hr3⟩ := zd_double hs ⟨1716, by norm_num⟩ (pc := 5105) (pc' := 5113) (k := 128) (rest := [flag b])
    (by glam44_rreach [1713, 1714, 1715] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz2 (by simp) (by norm_num)
  obtain ⟨m4, hz4, hf4, hr4⟩ := zd_double hs ⟨1720, by norm_num⟩ (pc := 5114) (pc' := 5123) (k := 256) (rest := [flag b])
    (by glam44_rreach [1717, 1718, 1719] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz3 (by simp) (by norm_num)
  obtain ⟨m5, hz5, hf5, hr5⟩ := zd_double hs ⟨1724, by norm_num⟩ (pc := 5124) (pc' := 5133) (k := 512) (rest := [flag b])
    (by glam44_rreach [1721, 1722, 1723] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz4 (by simp) (by norm_num)
  obtain ⟨m6, hz6, hf6, hr6⟩ := zd_double hs ⟨1728, by norm_num⟩ (pc := 5134) (pc' := 5143) (k := 1024) (rest := [flag b])
    (by glam44_rreach [1725, 1726, 1727] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz5 (by simp) (by norm_num)
  obtain ⟨m7, hz7, hf7, hr7⟩ := zd_double hs ⟨1732, by norm_num⟩ (pc := 5144) (pc' := 5153) (k := 2048) (rest := [flag b])
    (by glam44_rreach [1729, 1730, 1731] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz6 (by simp) (by norm_num)
  obtain ⟨m8, hz8, hf8, hr8⟩ := zd_double hs ⟨1736, by norm_num⟩ (pc := 5154) (pc' := 5163) (k := 4096) (rest := [flag b])
    (by glam44_rreach [1733, 1734, 1735] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz7 (by simp) (by norm_num)
  -- the copy to `HP`
  have hp9 : Reach (callState s 5164 [flag b] m8)
      (callState s 5173 [wd HP, wd CW, wd 8192, flag b] m8) 9 := by
    glam44_rreach [1737, 1738, 1739] with [CW, HP]
  have hmc := reach_mcopy hs ⟨1740, by norm_num⟩ (pc := 5173) (d := HP) (src := CW) (n := 8192)
    (rest := [flag b]) (m := m8) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold HP; omega) (by unfold CW; omega) (by omega) (by omega) (by unfold HP; omega)
    (by unfold CW; omega) (by simp)
  have hz9 : ZeroOn (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP) HP (HP + 8192) :=
    zeroOn_mcopy hz8
  have hf9 := FrameExcept.mcopy m8 CW HP 8192
  -- `dhint`
  have hb10 : Reach (callState s 5174 [flag b]
      (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP))
      (callState s 8291 [wd 5181, flag b]
        (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP)) 14 := by
    glam44_rreach [1741, 1742, 1743]
  obtain ⟨m', hh1, hh2, hf10, hc10⟩ := dhint_call hs (ret := 5181) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) _ hcd hz9
  have hb11 : Reach (callState s 5181 [flag (okH s.executionEnv.calldata), flag b] m')
      (callState s 5183 [flag (b && okH s.executionEnv.calldata)] m') 4 := by
    glam44_rreach [1744, 1745] with [flag, ite01_land]
  have hfr := (FrameExcept.mstore m CW 0).trans (hf1.trans (hf2.trans (hf3.trans (hf4.trans
    (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans hf10)))))))))
  refine ⟨m', ⟨⟨hI.rc1.frame hfr (by avoids_tac),
    hI.tbl.frame hfr (by avoids_tac), hI.acc.frame hfr (by avoids_tac),
    fun hl x hx => by rw [word_frame hfr (lo := MU) (hi := MU + 256) (by avoids_tac) (by omega) (by omega)]
                      exact hI.mu hl x hx,
    fun hl => by
      obtain ⟨S, hS, hK, hS1⟩ := hI.muks hl
      exact ⟨S, hS, fun x hx => by
        rw [word_frame hfr (lo := KS) (hi := KS + 800) (by avoids_tac) (by omega) (by omega)]
        exact hK x hx, hS1⟩,
    fun x hx => by rw [word_frame hfr (lo := CB) (hi := CB + 1088) (by avoids_tac) (by omega) (by omega)]
                   exact hI.cb x hx,
    hI.zIdx.frame hfr (by avoids_tac),
    hI.zNeg.frame hfr (by avoids_tac),
    by rw [word_frame hfr (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
       exact hI.flag0⟩, ⟨hh1, hh2⟩,
    (hz8.frame hf9 (by avoids_tac)).frame hf10 (by avoids_tac)⟩, ?_⟩
  have hR := (hb0.trans (hr1.trans (hr2.trans (hr3.trans (hr4.trans (hr5.trans (hr6.trans
    (hr7.trans (hr8.trans (hp9.trans (hmc.trans (hb10.trans (hc10.trans hb11)))))))))))))
  exact hR.mono (by unfold Gas.pZd; generalize Gas.dhint = g; omega)

end MlDsaOptGlam44.Proofs
