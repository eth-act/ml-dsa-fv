import MlDsaOpt87.Main.S5.Round
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# Mixed group 10 of ML-DSA-87 (`3530 … 3963`, WP S5)

Slots 0–2 squeeze `A[4][3]`, `A[5][3]`, `A[6][3]`; slot 3 (fresh) absorbs the
first five blocks of the padded public key. Then `gfix 7` and `pass3m`
(rows 4–6 of column 3 into `ACC + 0x2000`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

theorem s5_g10_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (s5X s.executionEnv.calldata 3 0 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 3530 [flag b] m) (callState s 3558 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have g0 : Reach (callState s 3530 [flag b] m)
      (callState s 12945 [wd 0x0777770000074200000077, wd 0, wd 7, wd 0, wd 3558, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    opt87_reach [1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 3558) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 7) (cmult := 0) (l4 := 0x0777770000074200000077)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by avoids_tac)
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have hks : KS4 m1 (s5X cd 3 0 0) :=
    s5_ks4_ginit (kmask := 0) (L := fun k => if k < 3 then 3 + 256 * (4 + k) + 0x1F0000 else 0)
      (S := s5X cd 3 0 0) hrho0 (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        by_cases h3 : k < 3
        · have e : s5X cd 3 0 0 k = seedState 168 (aSeed cd (4 + k) 3) := by
            unfold s5X; rw [if_pos h3]; rfl
          rw [e]
          exact s5_freshLane_aSeed hcd32 (by omega) (by norm_num)
            (by interval_cases k <;> decide) (by simp [h3]) hx
        · have e : s5X cd 3 0 0 k = Fips202.emptyState := by unfold s5X; rw [if_neg h3]; rfl
          rw [e]
          have hk3 : k = 3 := by omega
          subst hk3
          exact s5_freshLane_zero (by decide) (by simp) x)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- Group 10's cost: glue 405 and its calls. -/
theorem s5_g10_cost :
    405 + Gas.ginit + 5 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + Gas.gfix 3 + Gas.pass3m = Gas.pG10 := by
  unfold Gas.pG10; ring

theorem s5_seg_g10 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvT s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3530 [flag b] m)
        (callState s 3963 [flag (b && okCol s.executionEnv.calldata 1 3 3)] m') Gas.pG10 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 2592 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := s5_g10_ginit hs hcd hI.rho b
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 3558) (r0 := 3605) (r1 := 3613) (r2 := 3627) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 0) (off := 0) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176])
    (fun _ => by opt87_reach [1177, 1178, 1179, 1180])
    (fun _ => by opt87_reach [1181, 1182, 1183, 1184, 1185, 1186] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (s5X_sized _ 3 0 0) hks1 (S5Blocks.zero _ _)
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 3 0 b k)) (fun k _ => rfl)
  have hks2 : KS4 m2 (s5X s.executionEnv.calldata 3 0 1) :=
    s5_KS4_congr hks2' fun k hk => s5_permute_Y _ 3 0 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 3627) (r0 := 3675) (r1 := 3683) (r2 := 3697) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 1) (off := 136) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195])
    (fun _ => by opt87_reach [1196, 1197, 1198, 1199])
    (fun _ => by opt87_reach [1200, 1201, 1202, 1203, 1204, 1205] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (s5X_sized _ 3 0 1) hks2 hB2
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 3 0 b k)) (fun k _ => rfl)
  have hks3 : KS4 m3 (s5X s.executionEnv.calldata 3 0 2) :=
    s5_KS4_congr hks3' fun k hk => s5_permute_Y _ 3 0 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 3697) (r0 := 3746) (r1 := 3754) (r2 := 3768) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 2) (off := 272) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214])
    (fun _ => by opt87_reach [1215, 1216, 1217, 1218])
    (fun _ => by opt87_reach [1219, 1220, 1221, 1222, 1223, 1224] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (s5X_sized _ 3 0 2) hks3 hB3
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 3 0 b k)) (fun k _ => rfl)
  have hks4 : KS4 m4 (s5X s.executionEnv.calldata 3 0 3) :=
    s5_KS4_congr hks4' fun k hk => s5_permute_Y _ 3 0 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 3768) (r0 := 3817) (r1 := 3825) (r2 := 3839) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 3) (off := 408) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233])
    (fun _ => by opt87_reach [1234, 1235, 1236, 1237])
    (fun _ => by opt87_reach [1238, 1239, 1240, 1241, 1242, 1243] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (s5X_sized _ 3 0 3) hks4 hB4
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 3 0 b k)) (fun k _ => rfl)
  have hks5 : KS4 m5 (s5X s.executionEnv.calldata 3 0 4) :=
    s5_KS4_congr hks5' fun k hk => s5_permute_Y _ 3 0 3 hk
  -- squeeze 4
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := s5_absorb_round hs hcd' (fb := flag b) (m := m5)
    (pc0 := 3839) (r0 := 3888) (r1 := 3896) (r2 := 3910) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 4) (off := 544) (by norm_num) (by norm_num) (by norm_num)
    (by opt87_reach [1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252])
    (fun _ => by opt87_reach [1253, 1254, 1255, 1256])
    (fun _ => by opt87_reach [1257, 1258, 1259, 1260, 1261, 1262] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (s5X_sized _ 3 0 4) hks5 hB5
    (St := fun b k => Keccak.permute (s5Y s.executionEnv.calldata 3 0 b k)) (fun k _ => rfl)
  have hks6 : KS4 m6 (s5X s.executionEnv.calldata 3 0 5) :=
    s5_KS4_congr hks6' fun k hk => s5_permute_Y _ 3 0 4 hk
  -- gfix 7
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by s5_frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 3910 [flag b] m6) (callState s 12615 [wd 7, wd 3920, flag b] m6) 18 := by
    opt87_reach [1263, 1264, 1265, 1266, 1267]
  obtain ⟨m7, hlanes, hks7, -, hf7, hc7⟩ := gfix_call hs (ret := 3920) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 7) (by norm_num) 3 (by decide) (s5X s.executionEnv.calldata 3 0 5) (s5X_sized _ 3 0 5) hks6
    (fun k => if k < 3 then seedState 168 (aSeed s.executionEnv.calldata (4 + k) 3) else Fips202.emptyState)
    h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB6.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (s5Y _ 3 0 b' sl) = _
        rw [s5_permute_Y _ 3 0 b' hsl]; unfold s5X; rw [if_pos hsl3]
      · unfold s5X; rw [if_pos hsl3])
  rw [s5_gfix7_flag hcd32] at hc7
  -- pass3m (rows 4..6 of column 3)
  have gP : Reach (callState s 3920 [flag (okCol s.executionEnv.calldata 1 3 3), flag b] m7)
      (callState s 12229 [wd (2 ^ 192 - 1), wd (64 * 3), wd ZH, wd (ACC + 0x2000), wd 3962,
        flag (b && okCol s.executionEnv.calldata 1 3 3)] m7) 30 := by
    opt87_reach [1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3m_call hs (ret := 3962)
    (tail := [flag (b && okCol s.executionEnv.calldata 1 3 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 3) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num) (zh := ZH) (acc := ACC + 0x2000)
    (by unfold ZH ACC; norm_num) (by omega) (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 3962 [flag (b && okCol s.executionEnv.calldata 1 3 3)] m8)
      (callState s 3963 [flag (b && okCol s.executionEnv.calldata 1 3 3)] m8) 1 := by
    opt87_reach [1277]
  -- frames
  have hfA : FrameExcept m m7 GroupP.gsFrame :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7) (by s5_sub)
  have hfG : FrameExcept m m8 (groupFrame 1) :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans hfA hf8) (by s5_sub)
  have hfW := s5_frame_widen hfG
  refine ⟨m8, ⟨⟨s5_invE_frame hI.toInvE hfW, s5_acc0_frame hI.acc0 hfW, ?_⟩, ?_⟩, ?_⟩
  · -- rows 4..6 gain column 3
    refine s5_accMid_step (by norm_num) (by norm_num) (s5_accMid3 hI.acc1)
      (fun k hk t ht => (hI.zhat k hk t ht).1) (s5_zh_frame hfW) fun hrows t ht => ?_
    have e1 := s5_gs_acc1 hfA ht
    have e2 : lane (word m7 (ZH + 32 * t)) 3 = zhLane m 3 t := by
      rw [← s5_zhLane_lo m7 (by norm_num) t]; exact s5_gs_zh hfA (by norm_num) ht
    have e3 := s5_pass3m_rows (m6 := m7) (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl] at this
        exact this ((GroupP.aI_aSeed hcd32 _ _).trans ha) t ht) hrows ht
    rw [hacc t ht, e3, e1, e2]
  · -- the tr slot
    refine ⟨s5X s.executionEnv.calldata 3 0 5, s5X_sized _ 3 0 5,
      s5_KS4_frame hks7 hf8 (by s5_frame_tac), ?_⟩
    unfold s5X; rfl
  · have hR := (((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gP).trans hc8).trans gE
    exact hR.mono (by rw [← s5_g10_cost]; omega)

end MlDsaOpt87.Proofs
