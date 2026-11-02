import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Decode
set_option warningAsError true
/-! # Segment `4973 … 5075`: zero the side buffers, HintBitUnpack

`CW` and `HP` served as side buffers during ExpandA: one `MSTORE` of zero at
`CW`, the zero prefix doubled by `MCOPY` up to 8 KB, then copied to `HP`;
`dhint` decodes the hints into `HP`; `AND`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem zeroOn_mstore0 (m : ByteArray) (a : Nat) :
    ZeroOn (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) a) a (a + 32) := by
  intro x h1 h2
  have hb : ∀ i, i < 32 → byteAt (Data.Bytes.natToBytesPadded 0 32) i = 0 := by decide +kernel
  rw [byteAt_writeBytes, natToBytesPadded_size, if_pos ⟨h1, h2⟩]
  exact hb _ (by omega)

/-- `MCOPY` of a zero range: the destination is zero. -/
theorem zeroOn_mcopy {m : ByteArray} {src d n : Nat} (hz : ZeroOn m src (src + n)) :
    ZeroOn (MachineState.writeBytes m (MachineState.readPadded m src n) d) d (d + n) := by
  intro a h1 h2
  rw [byteAt_mcopy, if_pos ⟨h1, h2⟩]
  exact hz _ (by omega) (by omega)

/-- `MCOPY` of the zero prefix `[lo, lo + k)` right behind itself doubles it. -/
theorem zeroOn_mcopy_double {m : ByteArray} {lo k : Nat} (hz : ZeroOn m lo (lo + k)) :
    ZeroOn (MachineState.writeBytes m (MachineState.readPadded m lo k) (lo + k)) lo (lo + 2 * k) := by
  intro a h1 h2
  rw [byteAt_mcopy]
  split
  · exact hz _ (by omega) (by omega)
  · exact hz _ h1 (by omega)

/-- Three pushes and one doubling `MCOPY` of the zero prefix at `CW`. -/
theorem zd_double {s : State} (hs : Ctx s) (i : Fin 12125) {pc pc' k : Nat} {rest : List UInt256}
    {m : ByteArray}
    (hpush : Reach (callState s pc rest m) (callState s pc' (wd (CW + k) :: wd CW :: wd k :: rest) m) 9)
    (hi : instrAt i.val = .op .MCOPY) (hpc : pcAt i.val = pc') (hk : 2 * k ≤ 8192)
    (hz : ZeroOn m CW (CW + k)) (hlen : rest.length ≤ 1000) (hpcs : pc' < 2 ^ 16) :
    ∃ m', ZeroOn m' CW (CW + 2 * k) ∧ FrameExcept m m' [(CW, CW + 8192)] ∧
      Reach (callState s pc rest m) (callState s (pc' + 1) rest m') (9 + (3 + 3 * ((k + 31) / 32))) := by
  have hsz : 2616 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hmc := reach_mcopy hs i (d := CW + k) (src := CW) (n := k) (rest := rest) (m := m) hi hpc
    (by unfold CW; omega) (by unfold CW; omega) (by omega) (by omega)
    (by unfold CW; omega) (by unfold CW; omega) hlen
  exact ⟨_, zeroOn_mcopy_double hz,
    (FrameExcept.mcopy _ _ _ _).mono (fun r hr => ⟨(CW, CW + 8192), by simp,
      by simp at hr; subst hr; simp, by simp at hr; subst hr; simp; omega⟩),
    hpush.trans hmc⟩

theorem seg_zd {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvW s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvH s.executionEnv.calldata m' ∧
      Reach (callState s 4973 [flag b] m)
        (callState s 5075 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  have hsz : 2616 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hb0 : Reach (callState s 4973 [flag b] m)
      (callState s 4979 [flag b] (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) CW)) 9 := by
    opt44_reach [1556, 1557, 1558, 1559] with [CW]
  have hz0 := zeroOn_mstore0 m CW
  obtain ⟨m1, hz1, hf1, hr1⟩ := zd_double hs ⟨1563, by norm_num⟩ (pc := 4979) (pc' := 4987) (k := 32) (rest := [flag b])
    (by opt44_reach [1560, 1561, 1562] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz0 (by simp) (by norm_num)
  obtain ⟨m2, hz2, hf2, hr2⟩ := zd_double hs ⟨1567, by norm_num⟩ (pc := 4988) (pc' := 4996) (k := 64) (rest := [flag b])
    (by opt44_reach [1564, 1565, 1566] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz1 (by simp) (by norm_num)
  obtain ⟨m3, hz3, hf3, hr3⟩ := zd_double hs ⟨1571, by norm_num⟩ (pc := 4997) (pc' := 5005) (k := 128) (rest := [flag b])
    (by opt44_reach [1568, 1569, 1570] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz2 (by simp) (by norm_num)
  obtain ⟨m4, hz4, hf4, hr4⟩ := zd_double hs ⟨1575, by norm_num⟩ (pc := 5006) (pc' := 5015) (k := 256) (rest := [flag b])
    (by opt44_reach [1572, 1573, 1574] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz3 (by simp) (by norm_num)
  obtain ⟨m5, hz5, hf5, hr5⟩ := zd_double hs ⟨1579, by norm_num⟩ (pc := 5016) (pc' := 5025) (k := 512) (rest := [flag b])
    (by opt44_reach [1576, 1577, 1578] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz4 (by simp) (by norm_num)
  obtain ⟨m6, hz6, hf6, hr6⟩ := zd_double hs ⟨1583, by norm_num⟩ (pc := 5026) (pc' := 5035) (k := 1024) (rest := [flag b])
    (by opt44_reach [1580, 1581, 1582] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz5 (by simp) (by norm_num)
  obtain ⟨m7, hz7, hf7, hr7⟩ := zd_double hs ⟨1587, by norm_num⟩ (pc := 5036) (pc' := 5045) (k := 2048) (rest := [flag b])
    (by opt44_reach [1584, 1585, 1586] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz6 (by simp) (by norm_num)
  obtain ⟨m8, hz8, hf8, hr8⟩ := zd_double hs ⟨1591, by norm_num⟩ (pc := 5046) (pc' := 5055) (k := 4096) (rest := [flag b])
    (by opt44_reach [1588, 1589, 1590] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz7 (by simp) (by norm_num)
  -- the copy to `HP`
  have hp9 : Reach (callState s 5056 [flag b] m8)
      (callState s 5065 [wd HP, wd CW, wd 8192, flag b] m8) 9 := by
    opt44_reach [1592, 1593, 1594] with [CW, HP]
  have hmc := reach_mcopy hs ⟨1595, by norm_num⟩ (pc := 5065) (d := HP) (src := CW) (n := 8192)
    (rest := [flag b]) (m := m8) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold HP; omega) (by unfold CW; omega) (by omega) (by omega) (by unfold HP; omega)
    (by unfold CW; omega) (by simp)
  have hz9 : ZeroOn (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP) HP (HP + 8192) :=
    zeroOn_mcopy hz8
  have hf9 := FrameExcept.mcopy m8 CW HP 8192
  -- `dhint`
  have hb10 : Reach (callState s 5066 [flag b]
      (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP))
      (callState s 7740 [wd 5073, flag b]
        (MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP)) 14 := by
    opt44_reach [1596, 1597, 1598]
  obtain ⟨m', hh1, hh2, hf10, hc10⟩ := dhint_call hs (ret := 5073) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) _ hcd hz9
  have hb11 : Reach (callState s 5073 [flag (okH s.executionEnv.calldata), flag b] m')
      (callState s 5075 [flag (b && okH s.executionEnv.calldata)] m') 4 := by
    opt44_reach [1599, 1600] with [flag, ite01_land]
  have hfr := (FrameExcept.mstore m CW 0).trans (hf1.trans (hf2.trans (hf3.trans (hf4.trans
    (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans hf10)))))))))
  refine ⟨m', ⟨⟨hI.rc4.frame hfr (by avoids_tac), hI.rc1.frame hfr (by avoids_tac),
    hI.tbl.frame hfr (by avoids_tac), hI.acc.frame hfr (by avoids_tac),
    fun hl x hx => by rw [word_frame hfr (lo := MU) (hi := MU + 256) (by avoids_tac) (by omega) (by omega)]
                      exact hI.mu hl x hx,
    fun x hx => by rw [word_frame hfr (lo := CB) (hi := CB + 544) (by avoids_tac) (by omega) (by omega)]
                   exact hI.cb x hx,
    hI.sc.frame hfr (by avoids_tac), hI.zIdx.frame hfr (by avoids_tac),
    hI.zNeg.frame hfr (by avoids_tac)⟩, ⟨hh1, hh2⟩,
    (hz8.frame hf9 (by avoids_tac)).frame hf10 (by avoids_tac)⟩, ?_⟩
  have hR := (hb0.trans (hr1.trans (hr2.trans (hr3.trans (hr4.trans (hr5.trans (hr6.trans
    (hr7.trans (hr8.trans (hp9.trans (hmc.trans (hb10.trans (hc10.trans hb11)))))))))))))
  exact hR.mono (by unfold Gas.pZd; generalize Gas.dhint = g; omega)

end MlDsaOpt44.Proofs
