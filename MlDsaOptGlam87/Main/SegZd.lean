import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Fn.Decode
import MlDsaOpt87.Math
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegZd.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `4510 … 5665`: zero the side buffers, HintBitUnpack

`CW`, `HP`, `HP + 0x2000` served as side buffers during ExpandA: one `MSTORE`
of zero at `CW`, the zero prefix doubled by `MCOPY` up to 8 KB, copied to
`HP`, `HP + 0x2000`; `dhint` decodes the hints into `HP`; `AND`. -/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs.Infra

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
theorem zd_double {s : State} (hs : Ctx s) (i : Fin 34160) {pc pc' k : Nat} {rest : List UInt256}
    {m : ByteArray}
    (hpush : Reach (callState s pc rest m) (callState s pc' (wd (CW + k) :: wd CW :: wd k :: rest) m) 9)
    (hi : instrAt i.val = .base (.op .MCOPY)) (hpc : pcAt i.val = pc') (hk : 2 * k ≤ 8192)
    (hz : ZeroOn m CW (CW + k)) (hlen : rest.length ≤ 1000) (hpcs : pc' < 2 ^ 16) :
    ∃ m', ZeroOn m' CW (CW + 2 * k) ∧ FrameExcept m m' [(CW, CW + 8192)] ∧
      Reach (callState s pc rest m) (callState s (pc' + 1) rest m') (9 + (3 + 3 * ((k + 31) / 32))) := by
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
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
      Reach (callState s 4510 [flag b] m)
        (callState s 4624 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hb0 : Reach (callState s 4510 [flag b] m)
      (callState s 4516 [flag b] (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) CW)) 9 := by
    glam87_rreach [1523, 1524, 1525, 1526] with [CW]
  have hz0 := zeroOn_mstore0 m CW
  obtain ⟨m1, hz1, hf1, hr1⟩ := zd_double hs ⟨1530, by norm_num⟩ (pc := 4516) (pc' := 4524) (k := 32) (rest := [flag b])
    (by glam87_rreach [1527, 1528, 1529] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz0 (by simp) (by norm_num)
  obtain ⟨m2, hz2, hf2, hr2⟩ := zd_double hs ⟨1534, by norm_num⟩ (pc := 4525) (pc' := 4533) (k := 64) (rest := [flag b])
    (by glam87_rreach [1531, 1532, 1533] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz1 (by simp) (by norm_num)
  obtain ⟨m3, hz3, hf3, hr3⟩ := zd_double hs ⟨1538, by norm_num⟩ (pc := 4534) (pc' := 4542) (k := 128) (rest := [flag b])
    (by glam87_rreach [1535, 1536, 1537] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz2 (by simp) (by norm_num)
  obtain ⟨m4, hz4, hf4, hr4⟩ := zd_double hs ⟨1542, by norm_num⟩ (pc := 4543) (pc' := 4552) (k := 256) (rest := [flag b])
    (by glam87_rreach [1539, 1540, 1541] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz3 (by simp) (by norm_num)
  obtain ⟨m5, hz5, hf5, hr5⟩ := zd_double hs ⟨1546, by norm_num⟩ (pc := 4553) (pc' := 4562) (k := 512) (rest := [flag b])
    (by glam87_rreach [1543, 1544, 1545] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz4 (by simp) (by norm_num)
  obtain ⟨m6, hz6, hf6, hr6⟩ := zd_double hs ⟨1550, by norm_num⟩ (pc := 4563) (pc' := 4572) (k := 1024) (rest := [flag b])
    (by glam87_rreach [1547, 1548, 1549] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz5 (by simp) (by norm_num)
  obtain ⟨m7, hz7, hf7, hr7⟩ := zd_double hs ⟨1554, by norm_num⟩ (pc := 4573) (pc' := 4582) (k := 2048) (rest := [flag b])
    (by glam87_rreach [1551, 1552, 1553] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz6 (by simp) (by norm_num)
  obtain ⟨m8, hz8, hf8, hr8⟩ := zd_double hs ⟨1558, by norm_num⟩ (pc := 4583) (pc' := 4592) (k := 4096) (rest := [flag b])
    (by glam87_rreach [1555, 1556, 1557] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz7 (by simp) (by norm_num)
  -- the copies to `HP`, `HP + 0x2000`
  have hp9 : Reach (callState s 4593 [flag b] m8)
      (callState s 4603 [wd HP, wd CW, wd 8192, flag b] m8) 9 := by
    glam87_rreach [1559, 1560, 1561] with [CW, HP]
  have hmc := reach_mcopy hs ⟨1562, by norm_num⟩ (pc := 4603) (d := HP) (src := CW) (n := 8192)
    (rest := [flag b]) (m := m8) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold HP; omega) (by unfold CW; omega) (by omega) (by omega) (by unfold HP; omega)
    (by unfold CW; omega) (by simp)
  set m9 := MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP with hm9
  have hz9 : ZeroOn m9 HP (HP + 8192) := zeroOn_mcopy hz8
  have hf9 := FrameExcept.mcopy m8 CW HP 8192
  have hz8' : ZeroOn m9 CW (CW + 8192) := ZeroOn.frame hz8 hf9 (by avoids_tac)
  have hp10 : Reach (callState s 4604 [flag b] m9)
      (callState s 4614 [wd (HP + 8192), wd CW, wd 8192, flag b] m9) 9 := by
    glam87_rreach [1563, 1564, 1565] with [CW, HP]
  have hmc2 := reach_mcopy hs ⟨1566, by norm_num⟩ (pc := 4614) (d := HP + 8192) (src := CW) (n := 8192)
    (rest := [flag b]) (m := m9) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold HP; omega) (by unfold CW; omega) (by omega) (by omega) (by unfold HP; omega)
    (by unfold CW; omega) (by simp)
  set m10 := MachineState.writeBytes m9 (MachineState.readPadded m9 CW 8192) (HP + 8192) with hm10
  have hf10 := FrameExcept.mcopy m9 CW (HP + 8192) 8192
  have hz10 : ZeroOn m10 HP (HP + 0x4000) := by
    intro a h1 h2
    by_cases ha : a < HP + 8192
    · exact (ZeroOn.frame hz9 hf10 (by avoids_tac)) a h1 ha
    · have hz10b : ZeroOn m10 (HP + 8192) (HP + 8192 + 8192) := by rw [hm10]; exact zeroOn_mcopy hz8'
      exact hz10b a (Nat.le_of_not_lt ha) (by have : HP + 0x4000 = HP + 8192 + 8192 := rfl; omega)
  -- `dhint`
  have hb11 : Reach (callState s 4615 [flag b] m10)
      (callState s 8196 [wd 4622, flag b] m10) 14 := by
    glam87_rreach [1567, 1568, 1569]
  obtain ⟨m', hh1, hh2, hf11, hc11⟩ := dhint_call hs (ret := 4622) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) _ hcd hz10
  have hb12 : Reach (callState s 4622 [flag (okH s.executionEnv.calldata), flag b] m')
      (callState s 4624 [flag (b && okH s.executionEnv.calldata)] m') 4 := by
    glam87_rreach [1570, 1571] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hfr := (FrameExcept.mstore m CW 0).trans (hf1.trans (hf2.trans (hf3.trans (hf4.trans
    (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans (hf10.trans hf11))))))))))
  refine ⟨m', ⟨⟨RC1Table.frame hI.rc1 hfr (by avoids_tac),
    TblAt.frame hI.tbl hfr (by avoids_tac),
    AccAt.frame hI.acc hfr (by avoids_tac),
    TrlAt.frame hI.trl hfr (by avoids_tac),
    ZeroOn.frame hI.zBases hfr (by avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by avoids_tac),
    ZeroOn.frame hI.zNeg hfr (by avoids_tac)⟩,
    ⟨hh1, fun h hh r hr t ht => hh2 h hh r (by omega) t ht⟩,
    ZeroOn.frame (ZeroOn.frame hz8' hf10 (by avoids_tac)) hf11 (by avoids_tac)⟩, ?_⟩
  have hR := (hb0.trans (hr1.trans (hr2.trans (hr3.trans (hr4.trans (hr5.trans (hr6.trans
    (hr7.trans (hr8.trans (hp9.trans (hmc.trans (hp10.trans (hmc2.trans (hb11.trans
      (hc11.trans hb12)))))))))))))))
  exact hR.mono (by unfold Gas.pZd; generalize Gas.dhint = g; omega)

end MlDsaOptGlam87.Proofs
