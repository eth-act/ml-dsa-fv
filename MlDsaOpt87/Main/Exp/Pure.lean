import MlDsaOpt87.Main.Exp.Bound
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

namespace MlDsaOpt87.Proofs.Exp

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra

/-- `group [15, col, rb]` and the glue around it. -/
theorem pure_group {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {b : Bool} {col rb pc ret pc1 c0 c1 : Nat}
    {stk : List UInt256} (hcol : col < 7) (hrb : rb < 2)
    (g0 : Reach (callState s pc [flag b] m)
      (callState s 15188 [wd 15, wd col, wd rb, wd ret, flag b] m) c0)
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
    {col rb pc ret pcm c0 dst : Nat} (hcol : col < 7) (hrb : rb < 2) (i : Fin 12313)
    (g0 : Reach (callState s pc [flag b] m)
      (callState s 15188 [wd 15, wd col, wd rb, wd ret, flag b] m) c0)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hr : ret < 2 ^ 16)
    (g1 : ∀ M, Reach (callState s ret [flag (okCol s.executionEnv.calldata rb col 4), flag b] M)
      (callState s pcm [wd dst, wd ABUF, wd 8192, flag (b && okCol s.executionEnv.calldata rb col 4)] M) 13)
    (hi : instrAt i.val = .op .MCOPY) (hpc : pcAt i.val = pcm) (hpcm : pcm < 2 ^ 16)
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
      Reach (callState s 3371 [flag b] m)
        (callState s 3612 [flag (pureFlag s.executionEnv.calldata b)] m')
        pureCost := by
  have hzhf : ∀ {m m' : ByteArray} {rs : List (Nat × Nat)}, FrameExcept m m' rs →
      Avoids rs ZH (ZH + 0x4000) → ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t :=
    fun hf ha k hk t ht => zhLane_frame hf ha (by omega) ht
  -- group 0 → CW
  obtain ⟨m1, h0, hf1, hR1⟩ := pure_copy hs hcd hI.rc4 hI.rho (b := b) (col := 0) (rb := 0) (dst := CW)
    (by norm_num) (by norm_num) ⟨1079, by norm_num⟩ (pc := 3371) (ret := 3382) (pcm := 3393) (c0 := 21) (by opt87_reach [1068, 1069, 1070, 1071, 1072, 1073])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1074, 1075, 1076, 1077, 1078] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI1 := inve_frame hI hf1
  -- group 1 → HP
  obtain ⟨m2, h1, hf2, hR2⟩ := pure_copy hs hcd hI1.rc4 hI1.rho (b := b && okCol s.executionEnv.calldata 0 0 4) (col := 1) (rb := 0) (dst := HP)
    (by norm_num) (by norm_num) ⟨1091, by norm_num⟩ (pc := 3394) (ret := 3406) (pcm := 3418) (c0 := 22) (by opt87_reach [1080, 1081, 1082, 1083, 1084, 1085])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1086, 1087, 1088, 1089, 1090] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI2 := inve_frame hI1 hf2
  -- group 2 → HP + 0x2000
  obtain ⟨m3, h2, hf3, hR3⟩ := pure_copy hs hcd hI2.rc4 hI2.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4) (col := 2) (rb := 0) (dst := HP + 8192)
    (by norm_num) (by norm_num) ⟨1103, by norm_num⟩ (pc := 3419) (ret := 3431) (pcm := 3443) (c0 := 22) (by opt87_reach [1092, 1093, 1094, 1095, 1096, 1097])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1098, 1099, 1100, 1101, 1102] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI3 := inve_frame hI2 hf3
  -- group 3 → ACC + 0x2000
  obtain ⟨m4, h3, hf4, hR4⟩ := pure_copy hs hcd hI3.rc4 hI3.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4) (col := 3) (rb := 0) (dst := ACC + 8192)
    (by norm_num) (by norm_num) ⟨1115, by norm_num⟩ (pc := 3444) (ret := 3456) (pcm := 3467) (c0 := 22) (by opt87_reach [1104, 1105, 1106, 1107, 1108, 1109])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1110, 1111, 1112, 1113, 1114] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, ACC])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold ACC; omega)
  have hI4 := inve_frame hI3 hf4
  -- group 4, pass3f4
  obtain ⟨m5, h4, hf5, hR5⟩ := pure_group hs hcd hI4.rc4 hI4.rho (b := b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4) (col := 4) (rb := 0) (pc1 := 12196) (pc := 3468) (ret := 3480) (c0 := 22) (c1 := 18)
    (stk := [wd 3489, flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)])
    (by norm_num) (by norm_num) (by opt87_reach [1116, 1117, 1118, 1119, 1120, 1121])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1122, 1123, 1124, 1125, 1126] with [flag, MlDsaOpt44.Proofs.ite01_land])
  have hI5 := inve_frame hI4 hf5
  obtain ⟨m6, hw6, hf6, hc6⟩ := pass3f4_call hs (ret := 3489) (tail := [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
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
  have hJ6 : Reach (callState s 3489 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)] m6)
      (callState s 3490 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4)] m6) 1 := by
    opt87_reach [1127]
  -- group 5 → CW
  obtain ⟨m7, h5, hf7, hR7⟩ := pure_copy hs hcd hI6.rc4 hI6.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4) (col := 5) (rb := 0) (dst := CW)
    (by norm_num) (by norm_num) ⟨1139, by norm_num⟩ (pc := 3490) (ret := 3502) (pcm := 3513) (c0 := 22) (by opt87_reach [1128, 1129, 1130, 1131, 1132, 1133])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1134, 1135, 1136, 1137, 1138] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI7 := inve_frame hI6 hf7
  -- group 6, pass3f6
  obtain ⟨m8, h6, hf8, hR8⟩ := pure_group hs hcd hI7.rc4 hI7.rho (b := b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4) (col := 6) (rb := 0) (pc1 := 12388) (pc := 3514) (ret := 3526) (c0 := 22) (c1 := 18)
    (stk := [wd 3535, flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)])
    (by norm_num) (by norm_num) (by opt87_reach [1140, 1141, 1142, 1143, 1144, 1145])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1146, 1147, 1148, 1149, 1150] with [flag, MlDsaOpt44.Proofs.ite01_land])
  have hI8 := inve_frame hI7 hf8
  obtain ⟨m9, hw9, hf9, hc9⟩ := pass3f6_call hs (ret := 3535) (tail := [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8
  have hI9 := inve_frame hI8 hf9
  have hacc9 : Acc0 m9 s.executionEnv.calldata 7 :=
    acc0_p3f6 hI8.zhat (((hacc6.frame (by norm_num) hf7 (by exp_av) (by exp_av)).frame (by norm_num) hf8
        (by exp_av) (by exp_av)))
      (h5.frame hf8 (by exp_av)) h6 hw9 (hzhf hf9 (by exp_av))
  have hJ9 : Reach (callState s 3535 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)] m9)
      (callState s 3536 [flag (b && okCol s.executionEnv.calldata 0 0 4 &&
      okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 &&
      okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 &&
      okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4)] m9) 1 := by
    opt87_reach [1151]
  -- group 7 → CW
  obtain ⟨m10, h7, hf10, hR10⟩ := pure_copy hs hcd hI9.rc4 hI9.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4) (col := 0) (rb := 1) (dst := CW)
    (by norm_num) (by norm_num) ⟨1163, by norm_num⟩ (pc := 3536) (ret := 3548) (pcm := 3559) (c0 := 22) (by opt87_reach [1152, 1153, 1154, 1155, 1156, 1157])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1158, 1159, 1160, 1161, 1162] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, CW])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW; omega)
  have hI10 := inve_frame hI9 hf10
  -- group 8 → HP
  obtain ⟨m11, h8, hf11, hR11⟩ := pure_copy hs hcd hI10.rc4 hI10.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4 && okCol s.executionEnv.calldata 1 0 4) (col := 1) (rb := 1) (dst := HP)
    (by norm_num) (by norm_num) ⟨1175, by norm_num⟩ (pc := 3560) (ret := 3573) (pcm := 3585) (c0 := 23) (by opt87_reach [1164, 1165, 1166, 1167, 1168, 1169])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1170, 1171, 1172, 1173, 1174] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP; omega)
  have hI11 := inve_frame hI10 hf11
  -- group 9 → HP + 0x2000
  obtain ⟨m12, h9, hf12, hR12⟩ := pure_copy hs hcd hI11.rc4 hI11.rho (b := b && okCol s.executionEnv.calldata 0 0 4 && okCol s.executionEnv.calldata 0 1 4 && okCol s.executionEnv.calldata 0 2 4 && okCol s.executionEnv.calldata 0 3 4 && okCol s.executionEnv.calldata 0 4 4 && okCol s.executionEnv.calldata 0 5 4 && okCol s.executionEnv.calldata 0 6 4 && okCol s.executionEnv.calldata 1 0 4 && okCol s.executionEnv.calldata 1 1 4) (col := 2) (rb := 1) (dst := HP + 8192)
    (by norm_num) (by norm_num) ⟨1187, by norm_num⟩ (pc := 3586) (ret := 3599) (pcm := 3611) (c0 := 23) (by opt87_reach [1176, 1177, 1178, 1179, 1180, 1181])
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    (fun M => by opt87_reach [1182, 1183, 1184, 1185, 1186] with [flag, MlDsaOpt44.Proofs.ite01_land, ABUF, HP])
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

end MlDsaOpt87.Proofs.Exp
