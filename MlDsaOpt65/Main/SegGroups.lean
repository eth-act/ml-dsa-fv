import MlDsaOpt65.Main.S3.Lemmas
set_option warningAsError true
/-! # Segments `3565 … 3634`: the pure ExpandA groups (`group` calls).

Each segment is `PUSH2 ret; PUSH rb; PUSH col; PUSH1 amask; PUSH2 group; JUMP;
JUMPDEST; AND` (as `MlDsaOpt44/Main/SegGroups.lean`); the accumulator steps,
flags and `AccAt` are in `Main/S3/Lemmas.lean`. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

/-- `3565 … 3578`: `group [15, 0, 0]`, `AND`; `ACC` starts zeroed (`Inv4.zHigh`). -/
theorem seg_g0 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 1 ∧
      Reach (callState s 3565 [flag b] m)
        (callState s 3578 [flag (b && okCol0 s.executionEnv.calldata 0)] m') Gas.pG0 := by
  have hb1 : Reach (callState s 3565 [flag b] m)
      (callState s Entry.group [wd 15, wd 0, wd 0, wd 3576, flag b] m) 21 := by
    unfold Entry.group
    opt65_reach [1211, 1212, 1213, 1214, 1215, 1216]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3576) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 0) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3576 [flag (gOk s.executionEnv.calldata 15 0 0), flag b] m')
      (callState s 3578 [flag (b && okCol0 s.executionEnv.calldata 0)] m') 4 := by
    rw [s3_gOk_g0]
    opt65_reach [1217, 1218] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) hk ht
  have hacc0 : AccCols0 m s.executionEnv.calldata 0 := fun _ t _ => by
    rw [MlDsaOpt44.Proofs.word_zero_of_zeroOn hI.zHigh (by unfold BASES ACC; omega)
      (by unfold ACC HP; omega)]
    rfl
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac), TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac), HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac),
    s3_accCols0_step (by norm_num) hacc0 hI.zhat hzh hpost,
    ZeroOn.frame (ZeroOn.mono hI.zMisc (le_refl _) (by unfold MISC TBL; omega)) hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zCw hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (le_refl _) (by unfold ACC HP; omega)) hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (by unfold BASES ACC; omega) (le_refl _)) hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG0; omega)⟩

/-- `3578 … 3592`: `group [15, 1, 0]`, `AND`. -/
theorem seg_g1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 1) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 2 ∧
      Reach (callState s 3578 [flag b] m)
        (callState s 3592 [flag (b && okCol0 s.executionEnv.calldata 1)] m') Gas.pG1 := by
  have hb1 : Reach (callState s 3578 [flag b] m)
      (callState s Entry.group [wd 15, wd 1, wd 0, wd 3590, flag b] m) 22 := by
    unfold Entry.group
    opt65_reach [1219, 1220, 1221, 1222, 1223, 1224]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3590) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 1) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3590 [flag (gOk s.executionEnv.calldata 15 1 0), flag b] m')
      (callState s 3592 [flag (b && okCol0 s.executionEnv.calldata 1)] m') 4 := by
    rw [s3_gOk_g0]
    opt65_reach [1225, 1226] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) hk ht
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac), TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac), HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac),
    s3_accCols0_step (by norm_num) hI.acc hI.zhat hzh hpost,
    ZeroOn.frame hI.zMisc hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zCw hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG1; omega)⟩

/-- `3592 … 3606`: `group [15, 2, 0]`, `AND`. -/
theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 2) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 3 ∧
      Reach (callState s 3592 [flag b] m)
        (callState s 3606 [flag (b && okCol0 s.executionEnv.calldata 2)] m') Gas.pG2 := by
  have hb1 : Reach (callState s 3592 [flag b] m)
      (callState s Entry.group [wd 15, wd 2, wd 0, wd 3604, flag b] m) 22 := by
    unfold Entry.group
    opt65_reach [1227, 1228, 1229, 1230, 1231, 1232]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3604) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 2) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3604 [flag (gOk s.executionEnv.calldata 15 2 0), flag b] m')
      (callState s 3606 [flag (b && okCol0 s.executionEnv.calldata 2)] m') 4 := by
    rw [s3_gOk_g0]
    opt65_reach [1233, 1234] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) hk ht
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac), TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac), HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac),
    s3_accCols0_step (by norm_num) hI.acc hI.zhat hzh hpost,
    ZeroOn.frame hI.zMisc hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zCw hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG2; omega)⟩

/-- `3606 … 3620`: `group [15, 3, 0]`, `AND`. -/
theorem seg_g3 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 3) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 4 ∧
      Reach (callState s 3606 [flag b] m)
        (callState s 3620 [flag (b && okCol0 s.executionEnv.calldata 3)] m') Gas.pG3 := by
  have hb1 : Reach (callState s 3606 [flag b] m)
      (callState s Entry.group [wd 15, wd 3, wd 0, wd 3618, flag b] m) 22 := by
    unfold Entry.group
    opt65_reach [1235, 1236, 1237, 1238, 1239, 1240]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3618) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 3) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3618 [flag (gOk s.executionEnv.calldata 15 3 0), flag b] m')
      (callState s 3620 [flag (b && okCol0 s.executionEnv.calldata 3)] m') 4 := by
    rw [s3_gOk_g0]
    opt65_reach [1241, 1242] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) hk ht
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac), TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac), HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac),
    s3_accCols0_step (by norm_num) hI.acc hI.zhat hzh hpost,
    ZeroOn.frame hI.zMisc hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zCw hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG3; omega)⟩

/-- `3620 … 3634`: `group [15, 4, 0]`, `AND`. -/
theorem seg_g4 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG s.executionEnv.calldata m 4) (b : Bool) :
    ∃ m', InvG s.executionEnv.calldata m' 5 ∧
      Reach (callState s 3620 [flag b] m)
        (callState s 3634 [flag (b && okCol0 s.executionEnv.calldata 4)] m') Gas.pG4 := by
  have hb1 : Reach (callState s 3620 [flag b] m)
      (callState s Entry.group [wd 15, wd 4, wd 0, wd 3632, flag b] m) 22 := by
    unfold Entry.group
    opt65_reach [1243, 1244, 1245, 1246, 1247, 1248]
  obtain ⟨m', hpost, hfr, hc⟩ := group_call hs (ret := 3632) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.rc4
    hI.rho (amask := 15) (col := 4) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  have hb2 : Reach (callState s 3632 [flag (gOk s.executionEnv.calldata 15 4 0), flag b] m')
      (callState s 3634 [flag (b && okCol0 s.executionEnv.calldata 4)] m') 4 := by
    rw [s3_gOk_g0]
    opt65_reach [1249, 1250] with [flag, MlDsaOpt44.Proofs.ite01_land]
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfr (by unfold groupFrame; avoids_tac) hk ht
  refine ⟨m', ⟨RC4Table.frame hI.rc4 hfr (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfr (by unfold groupFrame; avoids_tac), TblAt.frame hI.tbl hfr (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfr (by unfold groupFrame; avoids_tac), HPAt.frame hI.hp hfr (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfr (by unfold groupFrame; avoids_tac),
    s3_accCols0_step (by norm_num) hI.acc hI.zhat hzh hpost,
    ZeroOn.frame hI.zMisc hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zCw hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zIdx hfr (by unfold groupFrame; avoids_tac),
    ZeroOn.frame hI.zAcc1 hfr (by unfold groupFrame; avoids_tac)⟩,
    ((hb1.trans hc).trans hb2).mono (by unfold Gas.pG4; omega)⟩

end MlDsaOpt65.Proofs
