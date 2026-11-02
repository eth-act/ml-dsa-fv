import MlDsaOptGlam65.Main.Exp.Bound
import MlDsaOpt44.Math
set_option warningAsError true
/-!
# ExpandA, calls 0–14: the three pure groups (glam ML-DSA-65)

`2515 … 2588`: `group [15, s, 0]` for `s < 3`, each followed by `AND` and one
`MCOPY` of `ABUF[0, 8192)` to the side buffers `CW`, `HP`, `HP + 0x2000`
(`BufCol`). The glam port of groups 0–2 of v4's `exp_pure`
(`MlDsaOpt65/Main/Exp/Pure.lean`, `group_copy`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

namespace Exp

namespace G

theorem gOk_g0 (cd : ByteArray) (s : Nat) : gOk cd 15 s 0 = okCol0 cd s := by
  simp only [gOk, okCol0, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show Nat.testBit 15 0 = true by decide, show Nat.testBit 15 1 = true by decide,
    show Nat.testBit 15 2 = true by decide, show Nat.testBit 15 3 = true by decide,
    Bool.not_true, Bool.false_or, Bool.and_true, Nat.mul_zero, Nat.zero_add, Bool.and_assoc]

theorem pack4_ite15 {v w : Nat → Nat} :
    pack4 (fun r => if (15 : Nat).testBit r then v r else w r) = pack4 v := by
  unfold pack4
  simp only [show Nat.testBit 15 0 = true by decide, show Nat.testBit 15 1 = true by decide,
    show Nat.testBit 15 2 = true by decide, show Nat.testBit 15 3 = true by decide, if_true]

/-- One pure group `[15, col, 0]`, the `AND`, and the copy of `ABUF` to `dst`. -/
theorem group_copy {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {b : Bool} {col pc ret pcm dst c1 : Nat}
    (hcol : col < 5)
    (g1 : Reach (callState s pc [flag b] m) (callState s 20575 [wd 15, wd col, wd 0, wd ret, flag b] m) c1)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16)
    (g2 : ∀ M, Reach (callState s ret [flag (okCol0 s.executionEnv.calldata col), flag b] M)
      (callState s pcm [wd dst, wd ABUF, wd 8192, flag (b && okCol0 s.executionEnv.calldata col)] M) 13)
    (i : Fin 34203) (hi : instrAt i.val = .base (.op .MCOPY)) (hpc : pcAt i.val = pcm) (hpcm : pcm < 2 ^ 16)
    (hdst : dst + 8192 ≤ 0x1a700) :
    ∃ m', BufCol m' dst s.executionEnv.calldata col ∧
      FrameExcept m m' (groupFrame 0 ++ [(dst, dst + 8192)]) ∧
      Reach (callState s pc [flag b] m)
        (callState s (pcm + 1) [flag (b && okCol0 s.executionEnv.calldata col)] m')
        (c1 + Gas.group + 13 + 771) := by
  obtain ⟨m1, hpost, hfr, hc⟩ := group_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hret) m hrc hrho (amask := 15) (col := col) (rb := 0)
    (by norm_num) (by omega) (by norm_num) hcd
  rw [call_iff, gOk_g0] at hc
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hmc := reach_mcopy hs i (d := dst) (src := ABUF) (n := 8192)
    (rest := [flag (b && okCol0 s.executionEnv.calldata col)]) (m := m1) hi hpc (by omega)
    (by unfold ABUF; omega) (by omega) (by omega) (by omega) (by unfold ABUF; omega) (by simp)
  refine ⟨_, fun hok t ht => ?_, hfr.trans (FrameExcept.mcopy _ _ _ _),
    ((g1.trans hc).trans ((g2 m1).trans hmc)).mono (by omega)⟩
  rw [word_mcopy _ (by omega) (by omega), show ABUF + (dst + 32 * t - dst) = ABUF + 32 * t by omega]
  obtain ⟨junk, -, hw⟩ := hpost (by rw [gOk_g0]; exact hok)
  rw [hw t ht, pack4_ite15]
  simp only [colBuf, Nat.mul_zero, Nat.zero_add]

end G

/-- Glue of calls 0–14: three times pushes (21, 22, 22), `AND` and pushes (13), `MCOPY` (771). -/
def gG02 : Nat := 21 + 22 + 22 + 3 * (13 + 771) + 3 * Gas.group

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem exp_g02 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', G3In s.executionEnv.calldata m' ∧
      Reach (callState s 2515 [flag b] m)
        (callState s 2588 [flag (((b && okCol0 s.executionEnv.calldata 0) && okCol0 s.executionEnv.calldata 1) &&
          okCol0 s.executionEnv.calldata 2)] m') gG02 := by
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  -- group 0 → CW
  obtain ⟨m1, hb1, hf1, hr1⟩ := G.group_copy hs hcd hI.rc4 hI.rho (b := b)
    (col := 0) (pc := 2515) (ret := 2526) (pcm := 2537) (dst := CW) (c1 := 21) (by norm_num)
    (by glam65_rreach [988, 989, 990, 991, 992, 993]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by glam65_rreach [994, 995, 996, 997, 998] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, CW]) ⟨999, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by unfold groupFrame; avoids_tac)
  have hrho1 := Rho1At.frame hI.rho hf1 (by unfold groupFrame; avoids_tac)
  -- group 1 → HP
  obtain ⟨m2, hb2, hf2, hr2⟩ := G.group_copy hs hcd hrc1 hrho1 (b := b && okCol0 s.executionEnv.calldata 0)
    (col := 1) (pc := 2538) (ret := 2550) (pcm := 2562) (dst := HP) (c1 := 22) (by norm_num)
    (by glam65_rreach [1000, 1001, 1002, 1003, 1004, 1005]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by glam65_rreach [1006, 1007, 1008, 1009, 1010] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, HP]) ⟨1011, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hrc2 := RC4Table.frame hrc1 hf2 (by unfold groupFrame; avoids_tac)
  have hrho2 := Rho1At.frame hrho1 hf2 (by unfold groupFrame; avoids_tac)
  -- group 2 → HP + 0x2000
  obtain ⟨m3, hb3, hf3, hr3⟩ := G.group_copy hs hcd hrc2 hrho2
    (b := b && okCol0 s.executionEnv.calldata 0 && okCol0 s.executionEnv.calldata 1)
    (col := 2) (pc := 2563) (ret := 2575) (pcm := 2587) (dst := HP + 8192) (c1 := 22) (by norm_num)
    (by glam65_rreach [1012, 1013, 1014, 1015, 1016, 1017]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by glam65_rreach [1018, 1019, 1020, 1021, 1022] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, HP]) ⟨1023, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hfA : FrameExcept m m3 (groupFrame 0 ++ [(CW, CW + 8192)] ++ (groupFrame 0 ++ [(HP, HP + 8192)]) ++
      (groupFrame 0 ++ [(HP + 8192, HP + 8192 + 8192)])) := (hf1.trans hf2).trans hf3
  refine ⟨m3, ⟨RC4Table.frame hI.rc4 hfA (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfA (by unfold groupFrame; avoids_tac),
    TblAt.frame hI.tbl hfA (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfA (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfA (by unfold groupFrame; avoids_tac),
    (hb1.frame hf2 (by unfold groupFrame; avoids_tac)).frame hf3 (by unfold groupFrame; avoids_tac),
    hb2.frame hf3 (by unfold groupFrame; avoids_tac), hb3,
    ZeroOn.frame (ZeroOn.mono hI.zMisc (by unfold MISC NNEG; omega) (by unfold NNEG TBL; omega)) hfA
      (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (le_refl _) (by unfold BASES FIN; omega)) hfA
      (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (by unfold BASES IDX; omega) (by unfold IDX FIN; omega)) hfA
      (by unfold groupFrame; avoids_tac)⟩, ?_⟩
  rw [show (2537 : Nat) + 1 = 2538 from rfl] at hr1
  rw [show (2562 : Nat) + 1 = 2563 from rfl] at hr2
  rw [show (2587 : Nat) + 1 = 2588 from rfl] at hr3
  refine ((hr1.trans hr2).trans hr3).mono ?_
  unfold gG02
  generalize Gas.group = G
  omega

end Exp

end MlDsaOptGlam65.Proofs
