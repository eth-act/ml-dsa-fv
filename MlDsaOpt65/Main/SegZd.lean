import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Decode
import MlDsaOpt65.Math
set_option warningAsError true
/-! # Segment `5242 … 5356`: zero the side buffers, HintBitUnpack

`CW`, `HP`, `HP + 0x2000` served as side buffers during ExpandA: one `MSTORE`
of zero at `CW`, the zero prefix doubled by `MCOPY` up to 8 KB, copied to
`HP`, `HP + 0x2000`; `dhint` decodes the hints into `HP`; `AND`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

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
theorem zd_double {s : State} (hs : Ctx s) (i : Fin 12202) {pc pc' k : Nat} {rest : List UInt256}
    {m : ByteArray}
    (hpush : Reach (callState s pc rest m) (callState s pc' (wd (CW + k) :: wd CW :: wd k :: rest) m) 9)
    (hi : instrAt i.val = .op .MCOPY) (hpc : pcAt i.val = pc') (hk : 2 * k ≤ 8192)
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
      Reach (callState s 5242 [flag b] m)
        (callState s 5356 [flag (b && okH s.executionEnv.calldata)] m') Gas.pZd := by
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hb0 : Reach (callState s 5242 [flag b] m)
      (callState s 5248 [flag b] (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) CW)) 9 := by
    opt65_reach [1731, 1732, 1733, 1734] with [CW]
  have hz0 := zeroOn_mstore0 m CW
  obtain ⟨m1, hz1, hf1, hr1⟩ := zd_double hs ⟨1738, by norm_num⟩ (pc := 5248) (pc' := 5256) (k := 32) (rest := [flag b])
    (by opt65_reach [1735, 1736, 1737] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz0 (by simp) (by norm_num)
  obtain ⟨m2, hz2, hf2, hr2⟩ := zd_double hs ⟨1742, by norm_num⟩ (pc := 5257) (pc' := 5265) (k := 64) (rest := [flag b])
    (by opt65_reach [1739, 1740, 1741] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz1 (by simp) (by norm_num)
  obtain ⟨m3, hz3, hf3, hr3⟩ := zd_double hs ⟨1746, by norm_num⟩ (pc := 5266) (pc' := 5274) (k := 128) (rest := [flag b])
    (by opt65_reach [1743, 1744, 1745] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz2 (by simp) (by norm_num)
  obtain ⟨m4, hz4, hf4, hr4⟩ := zd_double hs ⟨1750, by norm_num⟩ (pc := 5275) (pc' := 5284) (k := 256) (rest := [flag b])
    (by opt65_reach [1747, 1748, 1749] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz3 (by simp) (by norm_num)
  obtain ⟨m5, hz5, hf5, hr5⟩ := zd_double hs ⟨1754, by norm_num⟩ (pc := 5285) (pc' := 5294) (k := 512) (rest := [flag b])
    (by opt65_reach [1751, 1752, 1753] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz4 (by simp) (by norm_num)
  obtain ⟨m6, hz6, hf6, hr6⟩ := zd_double hs ⟨1758, by norm_num⟩ (pc := 5295) (pc' := 5304) (k := 1024) (rest := [flag b])
    (by opt65_reach [1755, 1756, 1757] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz5 (by simp) (by norm_num)
  obtain ⟨m7, hz7, hf7, hr7⟩ := zd_double hs ⟨1762, by norm_num⟩ (pc := 5305) (pc' := 5314) (k := 2048) (rest := [flag b])
    (by opt65_reach [1759, 1760, 1761] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz6 (by simp) (by norm_num)
  obtain ⟨m8, hz8, hf8, hr8⟩ := zd_double hs ⟨1766, by norm_num⟩ (pc := 5315) (pc' := 5324) (k := 4096) (rest := [flag b])
    (by opt65_reach [1763, 1764, 1765] with [CW]) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) hz7 (by simp) (by norm_num)
  -- the copies to `HP`, `HP + 0x2000`
  have hp9 : Reach (callState s 5325 [flag b] m8)
      (callState s 5335 [wd HP, wd CW, wd 8192, flag b] m8) 9 := by
    opt65_reach [1767, 1768, 1769] with [CW, HP]
  have hmc := reach_mcopy hs ⟨1770, by norm_num⟩ (pc := 5335) (d := HP) (src := CW) (n := 8192)
    (rest := [flag b]) (m := m8) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by unfold HP; omega) (by unfold CW; omega) (by omega) (by omega) (by unfold HP; omega)
    (by unfold CW; omega) (by simp)
  set m9 := MachineState.writeBytes m8 (MachineState.readPadded m8 CW 8192) HP with hm9
  have hz9 : ZeroOn m9 HP (HP + 8192) := zeroOn_mcopy hz8
  have hf9 := FrameExcept.mcopy m8 CW HP 8192
  have hz8' : ZeroOn m9 CW (CW + 8192) := ZeroOn.frame hz8 hf9 (by avoids_tac)
  have hp10 : Reach (callState s 5336 [flag b] m9)
      (callState s 5346 [wd (HP + 8192), wd CW, wd 8192, flag b] m9) 9 := by
    opt65_reach [1771, 1772, 1773] with [CW, HP]
  have hmc2 := reach_mcopy hs ⟨1774, by norm_num⟩ (pc := 5346) (d := HP + 8192) (src := CW) (n := 8192)
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
  have hb11 : Reach (callState s 5347 [flag b] m10)
      (callState s 8318 [wd 5354, flag b] m10) 14 := by
    opt65_reach [1775, 1776, 1777]
  obtain ⟨m', hh1, hh2, hf11, hc11⟩ := dhint_call hs (ret := 5354) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) _ hcd hz10
  have hb12 : Reach (callState s 5354 [flag (okH s.executionEnv.calldata), flag b] m')
      (callState s 5356 [flag (b && okH s.executionEnv.calldata)] m') 4 := by
    opt65_reach [1778, 1779] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hfr := (FrameExcept.mstore m CW 0).trans (hf1.trans (hf2.trans (hf3.trans (hf4.trans
    (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans (hf10.trans hf11))))))))))
  refine ⟨m', ⟨⟨RC1Table.frame hI.rc1 hfr (by avoids_tac),
    TblAt.frame hI.tbl hfr (by avoids_tac),
    AccAt.frame hI.acc hfr (by avoids_tac),
    MuAt.frame hI.mu hfr (by avoids_tac),
    fun hl => by
      obtain ⟨S, hS, hks, h2⟩ := hI.muks hl
      exact ⟨S, hS, fun x hx => by
        rw [word_frame hfr (lo := KS) (hi := KS + 800) (by avoids_tac) (by omega) (by omega)]
        exact hks x hx, h2⟩,
    CbAt.frame hI.cb hfr (by avoids_tac),
    ZeroOn.frame hI.zBases hfr (by avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by avoids_tac),
    ZeroOn.frame hI.zNeg hfr (by avoids_tac)⟩,
    ⟨hh1, fun h hh r hr t ht => hh2 h hh r (by omega) t ht⟩,
    ZeroOn.frame (ZeroOn.frame hz8' hf10 (by avoids_tac)) hf11 (by avoids_tac)⟩, ?_⟩
  have hR := (hb0.trans (hr1.trans (hr2.trans (hr3.trans (hr4.trans (hr5.trans (hr6.trans
    (hr7.trans (hr8.trans (hp9.trans (hmc.trans (hp10.trans (hmc2.trans (hb11.trans
      (hc11.trans hb12)))))))))))))))
  exact hR.mono (by unfold Gas.pZd; generalize Gas.dhint = g; omega)

end MlDsaOpt65.Proofs
