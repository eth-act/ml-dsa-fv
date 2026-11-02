import MlDsaOptGlam65.Main.Exp.WinB2
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The window (calls 35–41), `gfix 3` and `pass3f8` (`3739 … 4903`)

`win_A` (calls 35–39, `gfix 12`, `pass3f7`), `win_B1` (`KX`'s blocks 0 … 2,
call 40's slots), `win_B2` (calls 40, 41), then the state image `MUIMG`,
`HAVE6 := 0`, `gfix 3` (`KX = (A44, A54)`), `AND`, `pass3f8`, and the
accumulation (`accAt_glam`).
-/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding Rho1At ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

theorem flag_KX {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(3 : Nat).testBit sl || (aI (IKX cd sl)).isSome) = okKX cd := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (3 : Nat).testBit 0 = true by decide, show (3 : Nat).testBit 1 = true by decide,
    show (3 : Nat).testBit 2 = false by decide, show (3 : Nat).testBit 3 = false by decide,
    IKX, okKX, if_true, if_false, show (1 : Nat) ≠ 0 by decide, sA, GroupP.aI_aSeed hcd,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_true]

/-- `4870 … 4903`. -/
def cB3 : Nat := 9 + 78 + 25 + Gas.gfix 2 + 18 + Gas.pass3f8

/-- The window's cost (the `mulong`-free path of `mub0`'s two returns is 3 gas cheaper). -/
def cWin : Nat := cW1 + cW2a + cW2b + cB1 + cB2 + cB3

set_option maxHeartbeats 1000000 in
theorem exp_win {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : WinIn s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 3739 [flag b] m)
        (callState s 4903 [flag ((b && okP s.executionEnv.calldata) && okKX s.executionEnv.calldata)] m')
        cWin := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  obtain ⟨m1, hW, hR1⟩ := win_A hs hcd hI b
  obtain ⟨m2, hKX2, hks2, hf2, hR2⟩ := win_B1 hs hcd hW (b && okP s.executionEnv.calldata)
  have hrho2 := hW.g5.rho.frame hf2 (by w_frame)
  obtain ⟨m3, hks3, hsh3, hcb3, hmu3, hf3, c3, hc3le, hR3⟩ := win_B2 hs hcd hrho2 hKX2 hks2
    (b && okP s.executionEnv.calldata)
  -- MUIMG
  have g4 : Reach (callState s 4870 [flag (b && okP s.executionEnv.calldata)] m3)
      (callState s 4879 [wd 0x15040, wd 0, wd 800, flag (b && okP s.executionEnv.calldata)] m3) 9 := by
    glam65_rreach [1677, 1678, 1679, 1680]
  have hmc := reach_mcopy hs ⟨1681, by norm_num⟩ (pc := 4879) (d := 0x15040) (src := 0) (n := 800)
    (rest := [flag (b && okP s.executionEnv.calldata)]) (m := m3) (by simp only [Infra.instrAt_lit])
    (by simp only [Infra.pcAt_lit]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)
    (by omega) (by simp)
  generalize hm4 : MachineState.writeBytes m3 (MachineState.readPadded m3 0 800) 0x15040 = m4 at hmc
  have hf4 : FrameExcept m3 m4 [(MUIMG, MUIMG + 800)] := hm4 ▸ FrameExcept.mcopy m3 0 0x15040 800
  have himg : MlDsaOpt44.Proofs.St4At m4 MUIMG (W s.executionEnv.calldata 6) := fun x hx => by
    rw [← hm4, show MUIMG = 0x15040 from rfl, word_mcopy _ (by omega) (by omega),
      show 0 + (0x15040 + 32 * x - 0x15040) = KS + 32 * x by unfold KS; omega]
    exact hks3 x hx
  -- HAVE6 := 0, gfix 3
  have g5 : Reach (callState s 4880 [flag (b && okP s.executionEnv.calldata)] m4)
      (callState s 17249 [wd 3, wd 4894, flag (b && okP s.executionEnv.calldata)]
        (MachineState.writeBytes m4 (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 25 := by
    glam65_rreach [1682, 1683, 1684, 1685, 1686, 1687, 1688] with [HAVE6]
  generalize hm5 : MachineState.writeBytes m4 (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m5 at g5
  have hf5 : FrameExcept m4 m5 [(HAVE6, HAVE6 + 32)] := hm5 ▸ FrameExcept.mstore m4 HAVE6 0
  have h65 : word m5 HAVE6 = 0 := hm5 ▸ word_mstore m4 HAVE6 0 (by norm_num)
  have hf35 := hf4.trans hf5
  obtain ⟨m6, hlanes6, hks6, -, -, hf6, hc6⟩ := gfix_call hs (ret := 4894)
    (tail := [flag (b && okP s.executionEnv.calldata)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5 trivial
    (amask := 3) (by norm_num) 2 (by decide) (W s.executionEnv.calldata 6) (W_sized _ 6)
    (KS4.frame (KS4.frame hks3 hf4 (by w_frame)) hf5 (by w_frame)) (IKX s.executionEnv.calldata) h65
    (fun sl hsl hbit => by
      have h01 : sl < 2 := by
        by_contra h
        interval_cases sl <;> first | omega | exact absurd hbit (by decide)
      refine ⟨⟨fun t ht => ?_, fun g hg => ?_⟩, (W_KX _ h01).2.2 (by norm_num) (by norm_num)⟩
      · rw [wfr hf35 (ABUF + 32 * t) (by w_frame)]; exact (hsh3 sl h01).1 t ht
      · rw [wfr hf35 (FL + 32 * g) (by w_frame)]; exact (hsh3 sl h01).2 g hg)
  rw [flag_KX hcd32] at hc6
  -- AND, pass3f8
  have g7 : Reach (callState s 4894 [flag (okKX s.executionEnv.calldata), flag (b && okP s.executionEnv.calldata)] m6)
      (callState s 17053 [wd 4903, flag ((b && okP s.executionEnv.calldata) && okKX s.executionEnv.calldata)] m6)
      18 := by
    glam65_rreach [1689, 1690, 1691, 1692, 1693] with [flag, MlDsaOpt44.Proofs.ite01_land]
  obtain ⟨m7, hw7, hf7, hc7⟩ := pass3f8_call hs (ret := 4903)
    (tail := [flag ((b && okP s.executionEnv.calldata) && okKX s.executionEnv.calldata)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
  -- frames
  have hfB := (((hf2.trans hf3).trans hf4).trans hf5).trans hf6
  have hg6 := hW.g5.frame hfB (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame) (by w_frame)
    (by w_frame) (by w_frame) (by w_frame) (by w_frame)
  have hfC := hfB.trans hf7
  obtain ⟨m0, hacc7, hz0, b0, b1, b2, c3, c4, hP⟩ := hW.acc7
  refine ⟨m7, ⟨trivial, hg6.tbl.frame hf7 (by w_frame), ?_, hmu3.frame (((hf4.trans hf5).trans hf6).trans hf7) (by w_frame),
    ⟨W s.executionEnv.calldata 6, W_sized _ 6, fun x hx => by
      rw [wfr ((hf5.trans hf6).trans hf7) (MUIMG + 32 * x) (by w_frame)]; exact himg x hx, by
        unfold W; simp⟩,
    hcb3.frame (((hf4.trans hf5).trans hf6).trans hf7) (by w_frame), hg6.zBases.frame hf7 (by w_frame),
    hg6.zIdx.frame hf7 (by w_frame), hg6.zNeg.frame hf7 (by w_frame)⟩, ?_⟩
  · refine accAt_glam hz0 b0 b1 b2 c3 c4 hP hg6.zhat hg6.r4 hg6.r5 (fun hok t ht => ?_)
      (fun t ht => ?_) hw7
    · obtain ⟨a4, ha4⟩ := Option.isSome_iff_exists.mp (s3_okA_get hok (r := 4) (s := 4) (by norm_num) (by norm_num))
      obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp (s3_okA_get hok (r := 5) (s := 4) (by norm_num) (by norm_num))
      refine ⟨?_, ?_⟩
      · rw [hlanes6 0 (by norm_num) (by decide) a4 (by
          rw [show IKX s.executionEnv.calldata 0 = sA s.executionEnv.calldata 4 4 from by unfold IKX; simp, sA,
            GroupP.aI_aSeed hcd32]
          exact ha4) t ht]
        unfold aD; rw [ha4]; rfl
      · rw [hlanes6 1 (by norm_num) (by decide) a5 (by
          rw [show IKX s.executionEnv.calldata 1 = sA s.executionEnv.calldata 5 4 from by unfold IKX; simp, sA,
            GroupP.aI_aSeed hcd32]
          exact ha5) t ht]
        unfold aD; rw [ha5]; rfl
    · rw [wfr hfC (ACC + 32 * t) (by w_frame)]; exact hacc7 t ht
  · have hR := ((((((((hR1.trans hR2).trans hR3).trans g4).trans hmc).trans g5).trans hc6).trans g7).trans hc7)
    refine hR.mono ?_
    unfold cWin cB3
    have := hc3le
    generalize cW1 = a1 at *; generalize cW2a = a2; generalize cW2b = a3; generalize cB1 = a4
    generalize cB2 = a5 at *; generalize Gas.gfix 2 = a6; generalize Gas.pass3f8 = a7
    omega

end MlDsaOptGlam65.Proofs.Exp
