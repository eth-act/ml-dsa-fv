import MlDsaOptGlam87.Main.Exp.Bound
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Exp/Pure.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# The ten pure ExpandA groups (`3371 … 3612`, ML-DSA-87, v4)

Each group is `PUSH2 ret; PUSH rb; PUSH col; PUSH1 15; PUSH2 group; JUMP;
JUMPDEST; AND`, then either an `MCOPY` of `ABUF[0, 8192)` to a side buffer or a
fused pass call:

| group | col, rb | after |
|---|---|---|
| 0–3 | 0–3, 0 | copy to `CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000` |
| 4 | 4, 0 | `pass3f4` (`ACC` := columns 0–4) |
| 5 | 5, 0 | copy to `CW` |
| 6 | 6, 0 | `pass3f6` (`ACC` += columns 5, 6) |
| 7–9 | 0–2, 1 | copy to `CW`, `HP`, `HP + 0x2000` |
-/

namespace MlDsaOptGlam87.Proofs.Exp

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs
open MlDsaOptGlam87.Proofs.Infra

/-- `group [15, col, rb]` and the glue around it. -/
theorem pure_group {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {b : Bool} {col rb pc ret pc1 c0 c1 : Nat}
    {stk : List UInt256} (hcol : col < 7) (hrb : rb < 2)
    (g0 : Reach (callState s pc [flag b] m)
      (callState s 20382 [wd 15, wd col, wd rb, wd ret, flag b] m) c0)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hr : ret < 2 ^ 16)
    (g1 : ∀ M, Reach (callState s ret [flag (okCol s.executionEnv.calldata rb col 4), flag b] M)
      (callState s pc1 stk M) c1) :
    ∃ m', ColAt m' s.executionEnv.calldata ABUF rb col ∧ FrameExcept m m' (groupFrame rb) ∧
      Reach (callState s pc [flag b] m) (callState s pc1 stk m') (c0 + Gas.group + c1) := by
  obtain ⟨m1, hpost, hfr, hc⟩ := group_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m hrc hrho (amask := 15) (col := col) (rb := rb)
    (by norm_num) (by omega) hrb hcd
  rw [gOk_15] at hc
  exact ⟨m1, colAt_group hcol hrb hpost, hfr,
    (g0.trans hc).trans (g1 m1)⟩

/-- A pure group and the copy of its candidates to `dst`. -/
theorem pure_copy {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {b : Bool}
    {col rb pc ret pcm c0 dst : Nat} (hcol : col < 7) (hrb : rb < 2) (i : Fin 34160)
    (g0 : Reach (callState s pc [flag b] m)
      (callState s 20382 [wd 15, wd col, wd rb, wd ret, flag b] m) c0)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hr : ret < 2 ^ 16)
    (g1 : ∀ M, Reach (callState s ret [flag (okCol s.executionEnv.calldata rb col 4), flag b] M)
      (callState s pcm [wd dst, wd ABUF, wd 8192, flag (b && okCol s.executionEnv.calldata rb col 4)] M) 13)
    (hi : instrAt i.val = .base (.op .MCOPY)) (hpc : pcAt i.val = pcm) (hpcm : pcm < 2 ^ 16)
    (hdst : dst + 8192 ≤ 0x16a20) :
    ∃ m', ColAt m' s.executionEnv.calldata dst rb col ∧
      FrameExcept m m' (groupFrame rb ++ [(dst, dst + 8192)]) ∧
      Reach (callState s pc [flag b] m)
        (callState s (pcm + 1) [flag (b && okCol s.executionEnv.calldata rb col 4)] m')
        (c0 + Gas.group + 13 + 771) := by
  obtain ⟨m1, hcol1, hfr, hR⟩ := pure_group hs hcd hrc hrho hcol hrb g0 hj hr g1
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hmc := reach_mcopy hs i (d := dst) (src := ABUF) (n := 8192)
    (rest := [flag (b && okCol s.executionEnv.calldata rb col 4)]) (m := m1) hi hpc (by omega)
    (by unfold ABUF; omega) (by omega) (by omega) (by omega) (by unfold ABUF; omega) (by simp)
  exact ⟨_, colAt_mcopy hcol1, hfr.trans (FrameExcept.mcopy _ _ _ _), hR.trans hmc⟩

/-- The flag of the ten pure groups. -/
def pureFlag (cd : ByteArray) (b : Bool) : Bool :=
  (((((((((b && okCol cd 0 0 4) && okCol cd 0 1 4) && okCol cd 0 2 4) && okCol cd 0 3 4) &&
    okCol cd 0 4 4) && okCol cd 0 5 4) && okCol cd 0 6 4) && okCol cd 1 0 4) && okCol cd 1 1 4) &&
    okCol cd 1 2 4

/-- The glue of the ten pure groups (pushes, `AND`s, copies, return `JUMPDEST`s):
the exact static cost of `3371 … 3612` outside the calls. -/
def pureGlue : Nat := 6531

/-- The exact cost of `3371 … 3612`. -/
def pureCost : Nat := pureGlue + 10 * Gas.group + Gas.pass3f4 + Gas.pass3f6

theorem exp_pure {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvE s.executionEnv.calldata m) (b : Bool) :
    ∃ m', MixIn s.executionEnv.calldata m' ∧
      Reach (callState s 2330 [flag b] m)
        (callState s 2571 [flag (pureFlag s.executionEnv.calldata b)] m')
        pureCost := by
  have hzhf : ∀ {m m' : ByteArray} {rs : List (Nat × Nat)}, FrameExcept m m' rs →
      Avoids rs ZH (ZH + 0x4000) → ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t :=
    fun hf ha k hk t ht => zhLane_frame hf ha (by omega) ht
  -- group 0 → CW
  obtain ⟨m1, h0, hf1, hR1⟩ := pure_copy hs hcd hI.rc4 hI.rho (b := b) (col := 0) (rb := 0) (dst := CW)
    (by norm_num) (by norm_num) ⟨861, by norm_num⟩ (pc := 2330) (ret := 2341) (pcm := 2352) (c0 := 21) (by glam87_rreach [850, 851, 852, 853, 854, 855])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [856, 857, 858, 859, 860] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI1 := inve_frame hI hf1
  -- group 1 → HP
  obtain ⟨m2, h1, hf2, hR2⟩ := pure_copy hs hcd hI1.rc4 hI1.rho (b := b && okCol s.executionEnv.calldata 0 0 4) (col := 1) (rb := 0) (dst := HP)
    (by norm_num) (by norm_num) ⟨873, by norm_num⟩ (pc := 2353) (ret := 2365) (pcm := 2377) (c0 := 22) (by glam87_rreach [862, 863, 864, 865, 866, 867])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [868, 869, 870, 871, 872] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI2 := inve_frame hI1 hf2
  -- group 2 → HP + 0x2000
  obtain ⟨m3, h2, hf3, hR3⟩ := pure_copy hs hcd hI2.rc4 hI2.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4) (col := 2) (rb := 0) (dst := HP + 8192)
    (by norm_num) (by norm_num) ⟨885, by norm_num⟩ (pc := 2378) (ret := 2390) (pcm := 2402) (c0 := 22) (by glam87_rreach [874, 875, 876, 877, 878, 879])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [880, 881, 882, 883, 884] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI3 := inve_frame hI2 hf3
  -- group 3 → ACC + 0x2000
  obtain ⟨m4, h3, hf4, hR4⟩ := pure_copy hs hcd hI3.rc4 hI3.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4) (col := 3) (rb := 0) (dst := ACC + 8192)
    (by norm_num) (by norm_num) ⟨897, by norm_num⟩ (pc := 2403) (ret := 2415) (pcm := 2426) (c0 := 22) (by glam87_rreach [886, 887, 888, 889, 890, 891])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [892, 893, 894, 895, 896] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, ACC])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold ACC; omega)
  have hI4 := inve_frame hI3 hf4
  -- group 4, pass3f4
  obtain ⟨m5, h4, hf5, hR5⟩ := pure_group hs hcd hI4.rc4 hI4.rho (b := b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4) (col := 4) (rb := 0) (pc1 := 17390) (pc := 2427) (ret := 2439) (c0 := 22) (c1 := 18)
    (stk := [wd 2448, flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)])
    (by norm_num) (by norm_num) (by glam87_rreach [898, 899, 900, 901, 902, 903])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [904, 905, 906, 907, 908] with [flag, MlDsaOpt44.Proofs.ite01_land])
  have hI5 := inve_frame hI4 hf5
  obtain ⟨m6, hw6, hf6, hc6⟩ := pass3f4_call hs (ret := 2448) (tail := [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
  have hI6 := inve_frame hI5 hf6
  have hacc6 : Acc0 m6 s.executionEnv.calldata 5 :=
    acc0_p3f4 hI5.zhat
      (((h0.frame hf2 (by exp_av)).frame hf3 (by exp_av)).frame hf4 (by exp_av) |>.frame hf5 (by exp_av))
      ((h1.frame hf3 (by exp_av)).frame hf4 (by exp_av) |>.frame hf5 (by exp_av))
      ((h2.frame hf4 (by exp_av)).frame hf5 (by exp_av))
      (h3.frame hf5 (by exp_av)) h4 hw6 (hzhf hf6 (by exp_av))
  have hJ6 : Reach (callState s 2448 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)] m6)
      (callState s 2449 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)] m6) 1 := by
    glam87_rreach [909]
  -- group 5 → CW
  obtain ⟨m7, h5, hf7, hR7⟩ := pure_copy hs hcd hI6.rc4 hI6.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4) (col := 5) (rb := 0) (dst := CW)
    (by norm_num) (by norm_num) ⟨921, by norm_num⟩ (pc := 2449) (ret := 2461) (pcm := 2472) (c0 := 22) (by glam87_rreach [910, 911, 912, 913, 914, 915])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [916, 917, 918, 919, 920] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI7 := inve_frame hI6 hf7
  -- group 6, pass3f6
  obtain ⟨m8, h6, hf8, hR8⟩ := pure_group hs hcd hI7.rc4 hI7.rho (b := b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4) (col := 6) (rb := 0) (pc1 := 17582) (pc := 2473) (ret := 2485) (c0 := 22) (c1 := 18)
    (stk := [wd 2494, flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)])
    (by norm_num) (by norm_num) (by glam87_rreach [922, 923, 924, 925, 926, 927])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [928, 929, 930, 931, 932] with [flag, MlDsaOpt44.Proofs.ite01_land])
  have hI8 := inve_frame hI7 hf8
  obtain ⟨m9, hw9, hf9, hc9⟩ := pass3f6_call hs (ret := 2494) (tail := [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
  have hI9 := inve_frame hI8 hf9
  have hacc9 : Acc0 m9 s.executionEnv.calldata 7 :=
    acc0_p3f6 hI8.zhat (((hacc6.frame (by norm_num) hf7 (by exp_av) (by exp_av)).frame (by norm_num) hf8
        (by exp_av) (by exp_av)))
      (h5.frame hf8 (by exp_av)) h6 hw9 (hzhf hf9 (by exp_av))
  have hJ9 : Reach (callState s 2494 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)] m9)
      (callState s 2495 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)] m9) 1 := by
    glam87_rreach [933]
  -- group 7 → CW
  obtain ⟨m10, h7, hf10, hR10⟩ := pure_copy hs hcd hI9.rc4 hI9.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4) (col := 0) (rb := 1) (dst := CW)
    (by norm_num) (by norm_num) ⟨945, by norm_num⟩ (pc := 2495) (ret := 2507) (pcm := 2518) (c0 := 22) (by glam87_rreach [934, 935, 936, 937, 938, 939])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [940, 941, 942, 943, 944] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI10 := inve_frame hI9 hf10
  -- group 8 → HP
  obtain ⟨m11, h8, hf11, hR11⟩ := pure_copy hs hcd hI10.rc4 hI10.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4 && okCol s.executionEnv.calldata 1 0 4) (col := 1) (rb := 1) (dst := HP)
    (by norm_num) (by norm_num) ⟨957, by norm_num⟩ (pc := 2519) (ret := 2532) (pcm := 2544) (c0 := 23) (by glam87_rreach [946, 947, 948, 949, 950, 951])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [952, 953, 954, 955, 956] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI11 := inve_frame hI10 hf11
  -- group 9 → HP + 0x2000
  obtain ⟨m12, h9, hf12, hR12⟩ := pure_copy hs hcd hI11.rc4 hI11.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4 && okCol s.executionEnv.calldata 1 0 4 && okCol s.executionEnv.calldata 1 1 4) (col := 2) (rb := 1) (dst := HP + 8192)
    (by norm_num) (by norm_num) ⟨969, by norm_num⟩ (pc := 2545) (ret := 2558) (pcm := 2570) (c0 := 23) (by glam87_rreach [958, 959, 960, 961, 962, 963])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by glam87_rreach [964, 965, 966, 967, 968] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI12 := inve_frame hI11 hf12
  refine ⟨m12, ⟨hI12,
    ((hacc9.frame (by norm_num) hf10 (by exp_av) (by exp_av)).frame (by norm_num) hf11 (by exp_av)
      (by exp_av)).frame (by norm_num) hf12 (by exp_av) (by exp_av),
    (h7.frame hf11 (by exp_av)).frame hf12 (by exp_av), h8.frame hf12 (by exp_av), h9⟩, ?_⟩
  have hR := ((((((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hc6).trans hJ6).trans
    hR7).trans hR8).trans hc9).trans hJ9).trans hR10).trans hR11).trans hR12
  refine hR.mono ?_
  clear hcd
  unfold pureCost pureGlue
  omega

end MlDsaOptGlam87.Proofs.Exp
