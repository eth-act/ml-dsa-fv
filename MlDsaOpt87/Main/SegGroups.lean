import MlDsaOpt87.Main.S3.Lemmas
set_option warningAsError true
/-! # Segments `3389 … 3530`: the ten pure ExpandA groups `[15, col, rb]`

Each segment is `PUSH2 ret; PUSH rb; PUSH col; PUSH1 15; PUSH2 group; JUMP;
JUMPDEST; AND`; mirror `MlDsaOpt44/Main/SegGroups.lean`. `group_call` adds
`A[4 rb + r][col][t] · ẑ_col[t]` to lane `r` of `ACC + 0x2000 rb` under its
flag; the accumulator equation (`AccCols`) follows by `accSum`'s recursion
(`s3_accCols_step`, `Main/S3/Lemmas.lean`; `ẑ` is not written by `group`).
Groups 0 and 7 start from the zeroed accumulator table (`AccCols _ _ rb 0`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

/-- `3389 … 3402`: `group [15, 0, 0]` (flag `gOk cd 15 0 0 = okCol cd 0 0 4`), `AND`. -/
theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3389 [flag b] m)
        (callState s 3402 [flag (b && okCol s.executionEnv.calldata 0 0 4)] m') Gas.pG0 := by
  have hb1 : Reach (callState s 3389 [flag b] m)
      (callState s Entry.group [wd 15, wd 0, wd 0, wd 3400, flag b] m) 21 := by
    unfold Entry.group
    opt87_reach [1078, 1079, 1080, 1081, 1082, 1083]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3400) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 0) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3400 [flag (gOk s.executionEnv.calldata 15 0 0), flag b] m')
      (callState s 3402 [flag (b && okCol s.executionEnv.calldata 0 0 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1084, 1085] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num)
      ⟨hI.rc4, hI.rc1, hI.tbl, hI.zhat, hI.hp, hI.c, hI.rho⟩ hfr,
    s3_accCols_step (by norm_num)
      (s3_accCols_zero (rb := 0) (ZeroOn.mono hI.zAcc (by omega) (by unfold ACC HP; omega))) hI.zhat hzh hpost,
    ZeroOn.frame (ZeroOn.mono hI.zAcc (by omega) (le_refl _)) hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG0; omega)⟩

/-- `3402 … 3416`: `group [15, 1, 0]` (flag `gOk cd 15 1 0 = okCol cd 0 1 4`), `AND`. -/
theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3402 [flag b] m)
        (callState s 3416 [flag (b && okCol s.executionEnv.calldata 0 1 4)] m') Gas.pG1 := by
  have hb1 : Reach (callState s 3402 [flag b] m)
      (callState s Entry.group [wd 15, wd 1, wd 0, wd 3414, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1086, 1087, 1088, 1089, 1090, 1091]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3414) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 1) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3414 [flag (gOk s.executionEnv.calldata 15 1 0), flag b] m')
      (callState s 3416 [flag (b && okCol s.executionEnv.calldata 0 1 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1092, 1093] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG1; omega)⟩

/-- `3416 … 3430`: `group [15, 2, 0]` (flag `gOk cd 15 2 0 = okCol cd 0 2 4`), `AND`. -/
theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3416 [flag b] m)
        (callState s 3430 [flag (b && okCol s.executionEnv.calldata 0 2 4)] m') Gas.pG2 := by
  have hb1 : Reach (callState s 3416 [flag b] m)
      (callState s Entry.group [wd 15, wd 2, wd 0, wd 3428, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1094, 1095, 1096, 1097, 1098, 1099]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3428) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 2) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3428 [flag (gOk s.executionEnv.calldata 15 2 0), flag b] m')
      (callState s 3430 [flag (b && okCol s.executionEnv.calldata 0 2 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1100, 1101] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG2; omega)⟩

/-- `3430 … 3444`: `group [15, 3, 0]` (flag `gOk cd 15 3 0 = okCol cd 0 3 4`), `AND`. -/
theorem seg_g3 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3430 [flag b] m)
        (callState s 3444 [flag (b && okCol s.executionEnv.calldata 0 3 4)] m') Gas.pG3 := by
  have hb1 : Reach (callState s 3430 [flag b] m)
      (callState s Entry.group [wd 15, wd 3, wd 0, wd 3442, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1102, 1103, 1104, 1105, 1106, 1107]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3442) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 3) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3442 [flag (gOk s.executionEnv.calldata 15 3 0), flag b] m')
      (callState s 3444 [flag (b && okCol s.executionEnv.calldata 0 3 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1108, 1109] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG3; omega)⟩

/-- `3444 … 3458`: `group [15, 4, 0]` (flag `gOk cd 15 4 0 = okCol cd 0 4 4`), `AND`. -/
theorem seg_g4 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3444 [flag b] m)
        (callState s 3458 [flag (b && okCol s.executionEnv.calldata 0 4 4)] m') Gas.pG4 := by
  have hb1 : Reach (callState s 3444 [flag b] m)
      (callState s Entry.group [wd 15, wd 4, wd 0, wd 3456, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1110, 1111, 1112, 1113, 1114, 1115]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3456) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 4) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3456 [flag (gOk s.executionEnv.calldata 15 4 0), flag b] m')
      (callState s 3458 [flag (b && okCol s.executionEnv.calldata 0 4 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1116, 1117] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG4; omega)⟩

/-- `3458 … 3472`: `group [15, 5, 0]` (flag `gOk cd 15 5 0 = okCol cd 0 5 4`), `AND`. -/
theorem seg_g5 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 5) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 6 ∧
      Reach (callState s 3458 [flag b] m)
        (callState s 3472 [flag (b && okCol s.executionEnv.calldata 0 5 4)] m') Gas.pG5 := by
  have hb1 : Reach (callState s 3458 [flag b] m)
      (callState s Entry.group [wd 15, wd 5, wd 0, wd 3470, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1118, 1119, 1120, 1121, 1122, 1123]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3470) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 5) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3470 [flag (gOk s.executionEnv.calldata 15 5 0), flag b] m')
      (callState s 3472 [flag (b && okCol s.executionEnv.calldata 0 5 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1124, 1125] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG5; omega)⟩

/-- `3472 … 3486`: `group [15, 6, 0]` (flag `gOk cd 15 6 0 = okCol cd 0 6 4`), `AND`. -/
theorem seg_g6 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 6) (b : Bool) :
    ∃ m', InvA s.executionEnv.calldata m' 7 ∧
      Reach (callState s 3472 [flag b] m)
        (callState s 3486 [flag (b && okCol s.executionEnv.calldata 0 6 4)] m') Gas.pG6 := by
  have hb1 : Reach (callState s 3472 [flag b] m)
      (callState s Entry.group [wd 15, wd 6, wd 0, wd 3484, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1126, 1127, 1128, 1129, 1130, 1131]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3484) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 6) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3484 [flag (gOk s.executionEnv.calldata 15 6 0), flag b] m')
      (callState s 3486 [flag (b && okCol s.executionEnv.calldata 0 6 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1132, 1133] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_step (by norm_num) hI.acc0 hI.zhat hzh hpost,
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG6; omega)⟩

/-- `3486 … 3500`: `group [15, 0, 1]` (flag `gOk cd 15 0 1 = okCol cd 1 0 4`), `AND`. -/
theorem seg_g7 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvA s.executionEnv.calldata m 7) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3486 [flag b] m)
        (callState s 3500 [flag (b && okCol s.executionEnv.calldata 1 0 4)] m') Gas.pG7 := by
  have hb1 : Reach (callState s 3486 [flag b] m)
      (callState s Entry.group [wd 15, wd 0, wd 1, wd 3498, flag b] m) 22 := by
    unfold Entry.group
    opt87_reach [1134, 1135, 1136, 1137, 1138, 1139]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3498) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 0) (rb := 1) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3498 [flag (gOk s.executionEnv.calldata 15 0 1), flag b] m')
      (callState s 3500 [flag (b && okCol s.executionEnv.calldata 1 0 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1140, 1141] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  have hz1 : ZeroOn m (ACC + 0x2000 * 1) (ACC + 0x2000 * 1 + 8192) :=
    ZeroOn.mono hI.zAcc1 (by simp only [Nat.mul_one, le_refl]) (by unfold ACC HP; norm_num)
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_frame hI.acc0
      (fun t ht => word_frame hfr (lo := ACC) (hi := ACC + 8192) (by unfold groupFrame; avoids_tac)
        (by omega) (by omega))
      (fun k hk t ht => hzh k (by omega) t ht),
    s3_accCols_step (by norm_num) (s3_accCols_zero hz1) hI.zhat hzh hpost⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG7; omega)⟩

/-- `3500 … 3515`: `group [15, 1, 1]` (flag `gOk cd 15 1 1 = okCol cd 1 1 4`), `AND`. -/
theorem seg_g8 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3500 [flag b] m)
        (callState s 3515 [flag (b && okCol s.executionEnv.calldata 1 1 4)] m') Gas.pG8 := by
  have hb1 : Reach (callState s 3500 [flag b] m)
      (callState s Entry.group [wd 15, wd 1, wd 1, wd 3513, flag b] m) 23 := by
    unfold Entry.group
    opt87_reach [1142, 1143, 1144, 1145, 1146, 1147]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3513) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 1) (rb := 1) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3513 [flag (gOk s.executionEnv.calldata 15 1 1), flag b] m')
      (callState s 3515 [flag (b && okCol s.executionEnv.calldata 1 1 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1148, 1149] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_frame hI.acc0
      (fun t ht => word_frame hfr (lo := ACC) (hi := ACC + 8192) (by unfold groupFrame; avoids_tac)
        (by omega) (by omega))
      (fun k hk t ht => hzh k (by omega) t ht),
    s3_accCols_step (by norm_num) hI.acc1 hI.zhat hzh hpost⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG8; omega)⟩

/-- `3515 … 3530`: `group [15, 2, 1]` (flag `gOk cd 15 2 1 = okCol cd 1 2 4`), `AND`. -/
theorem seg_g9 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvB s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvB s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3515 [flag b] m)
        (callState s 3530 [flag (b && okCol s.executionEnv.calldata 1 2 4)] m') Gas.pG9 := by
  have hb1 : Reach (callState s 3515 [flag b] m)
      (callState s Entry.group [wd 15, wd 2, wd 1, wd 3528, flag b] m) 23 := by
    unfold Entry.group
    opt87_reach [1150, 1151, 1152, 1153, 1154, 1155]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3528) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 2) (rb := 1) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3528 [flag (gOk s.executionEnv.calldata 15 2 1), flag b] m')
      (callState s 3530 [flag (b && okCol s.executionEnv.calldata 1 2 4)] m') 4 := by
    rw [s3_gOk_15]
    opt87_reach [1156, 1157] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) (by omega) ht
  refine ⟨m', ⟨s3_invE_frame (by norm_num) hI.toInvE hfr,
    s3_accCols_frame hI.acc0
      (fun t ht => word_frame hfr (lo := ACC) (hi := ACC + 8192) (by unfold groupFrame; avoids_tac)
        (by omega) (by omega))
      (fun k hk t ht => hzh k (by omega) t ht),
    s3_accCols_step (by norm_num) hI.acc1 hI.zhat hzh hpost⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG9; omega)⟩

end MlDsaOpt87.Proofs
