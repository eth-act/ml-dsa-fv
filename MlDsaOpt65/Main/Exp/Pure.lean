import MlDsaOpt65.Main.Exp.Bound
set_option warningAsError true
/-!
# ExpandA, row group 0: the five pure groups (ML-DSA-65, v4)

`3556 … 3674`: `group [15, s, 0]` for `s < 5`; after groups 0 … 3 one `MCOPY`
of `ABUF[0, 256)` to the side buffers `CW`, `HP`, `HP + 0x2000`, `ACC + 0x2000`;
after group 4 the fused pass `pass3f4` stores `Σ_s A[r][s] ẑ_s` into `ACC`
(`AccCols0 · 5`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

namespace Exp

/-- Column `col` of rows `0 … 3` of `A` as a row-packed word. -/
def colBuf (cd : ByteArray) (col t : Nat) : Nat := pack4 fun r => ((aD cd r col)[t]!).toNat

/-- The side buffer at `dst` holds column `col` of row group 0 (when it exists). -/
def BufCol (m : ByteArray) (dst : Nat) (cd : ByteArray) (col : Nat) : Prop :=
  okCol0 cd col = true → ∀ t, t < 256 → word m (dst + 32 * t) = colBuf cd col t

theorem BufCol.frame {m m' : ByteArray} {dst : Nat} {cd : ByteArray} {col : Nat} {rs : List (Nat × Nat)}
    (h : BufCol m dst cd col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    BufCol m' dst cd col := fun hok t ht => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht

theorem zl_eq (m : ByteArray) (j t : Nat) : zl m j t = zhLane m j t := rfl

/-- `pass3f4`'s word: the five columns of row group 0, lane-wise. -/
theorem p3f4_acc {m : ByteArray} {cd : ByteArray} (hz : ZHatAt m cd) (b0 : BufCol m CW cd 0)
    (b1 : BufCol m HP cd 1) (b2 : BufCol m (HP + 8192) cd 2) (b3 : BufCol m (ACC + 8192) cd 3)
    (b4 : BufCol m ABUF cd 4) (hok : okUpTo0 cd 5 = true) {t : Nat} (ht : t < 256) :
    p3f4Word m t = pack4 fun r => accSum cd m r t 5 := by
  have hA := s3_okUpTo0_get hok
  have hc : ∀ s, s < 5 → okCol0 cd s = true := fun s hs => by
    simp only [okCol0, Bool.and_eq_true]
    exact ⟨⟨⟨hA s hs 0 (by omega), hA s hs 1 (by omega)⟩, hA s hs 2 (by omega)⟩, hA s hs 3 (by omega)⟩
  unfold p3f4Word bz
  rw [b0 (hc 0 (by omega)) t ht, b1 (hc 1 (by omega)) t ht, b2 (hc 2 (by omega)) t ht,
    b3 (hc 3 (by omega)) t ht, b4 (hc 4 (by omega)) t ht]
  simp only [zl_eq]
  have e : colBuf cd 0 t * zhLane m 0 t + colBuf cd 1 t * zhLane m 1 t +
      colBuf cd 2 t * zhLane m 2 t + colBuf cd 3 t * zhLane m 3 t + colBuf cd 4 t * zhLane m 4 t =
      pack4 fun r => accSum cd m r t 5 := by
    simp only [colBuf, pack4, accSum]; ring
  rw [e]
  refine Nat.mod_eq_of_lt (MlDsaOpt44.Proofs.pack4_lt fun r hr => ?_)
  have := s3_accSum_le ht (fun k hk => (hz k hk t ht).1) 5 le_rfl (fun s hs => hA s hs r hr)
  omega

/-- One pure group `[15, col, 0]`, the `AND`, and the copy of `ABUF` to `dst`. -/
theorem group_copy {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {b : Bool} {col pc ret pcm dst c1 : Nat}
    (hcol : col < 5)
    (g1 : Reach (callState s pc [flag b] m) (callState s 14460 [wd 15, wd col, wd 0, wd ret, flag b] m) c1)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hret : ret < 2 ^ 16)
    (g2 : ∀ M, Reach (callState s ret [flag (okCol0 s.executionEnv.calldata col), flag b] M)
      (callState s pcm [wd dst, wd ABUF, wd 8192, flag (b && okCol0 s.executionEnv.calldata col)] M) 13)
    (i : Fin 12202) (hi : instrAt i.val = .op .MCOPY) (hpc : pcAt i.val = pcm) (hpcm : pcm < 2 ^ 16)
    (hdst : dst + 8192 ≤ TOP) :
    ∃ m', BufCol m' dst s.executionEnv.calldata col ∧
      FrameExcept m m' (groupFrame 0 ++ [(dst, dst + 8192)]) ∧
      Reach (callState s pc [flag b] m)
        (callState s (pcm + 1) [flag (b && okCol0 s.executionEnv.calldata col)] m')
        (c1 + Gas.group + 13 + 771) := by
  obtain ⟨m1, hpost, hfr, hc⟩ := group_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hret) m hrc hrho (amask := 15) (col := col) (rb := 0)
    (by norm_num) (by omega) (by norm_num) hcd
  rw [call_iff, s3_gOk_g0] at hc
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  simp only [TOP] at hdst
  have hmc := reach_mcopy hs i (d := dst) (src := ABUF) (n := 8192)
    (rest := [flag (b && okCol0 s.executionEnv.calldata col)]) (m := m1) hi hpc (by omega)
    (by unfold ABUF; omega) (by omega) (by omega) (by omega) (by unfold ABUF; omega) (by simp)
  refine ⟨_, fun hok t ht => ?_, hfr.trans (FrameExcept.mcopy _ _ _ _),
    ((g1.trans hc).trans ((g2 m1).trans hmc)).mono (by omega)⟩
  rw [word_mcopy _ (by omega) (by omega), show ABUF + (dst + 32 * t - dst) = ABUF + 32 * t by omega]
  obtain ⟨junk, -, hw⟩ := hpost (by rw [s3_gOk_g0]; exact hok)
  rw [hw t ht, s3_pack4_ite (fun r hr => by interval_cases r <;> decide)]
  simp only [colBuf, Nat.mul_zero, Nat.zero_add]

theorem okUpTo0_five (cd : ByteArray) (b : Bool) :
    (((((b && okCol0 cd 0) && okCol0 cd 1) && okCol0 cd 2) && okCol0 cd 3) && okCol0 cd 4) =
      (b && okUpTo0 cd 5) := by
  simp only [okUpTo0, Bool.true_and, Bool.and_assoc]

/-- The ExpandA flag: rows `0 … 3` (row group 0) and the ten row-group-1 instances. -/
theorem okA_eq (cd : ByteArray) : okA cd = (okUpTo0 cd 5 && (okIUpTo cd 9 && okI cd 9)) := by
  have h10 : (okIUpTo cd 9 && okI cd 9) = okUpTo1 cd 5 := by
    rw [← s3_okIUpTo10]; rfl
  rw [h10]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  refine ⟨fun h => ⟨s3_okUpTo0_of_okA h 5 le_rfl, s3_okUpTo1_of_okA h 5 le_rfl⟩, fun ⟨h0, h1⟩ => ?_⟩
  unfold okA
  rw [List.all_eq_true]
  intro r hr
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hr hc
  by_cases h4 : r < 4
  · exact s3_okUpTo0_get h0 c hc r h4
  · have : ∀ n, okUpTo1 cd n = true → ∀ s, s < n → (aOf cd 4 s).isSome = true ∧ (aOf cd 5 s).isSome = true := by
      intro n
      induction n with
      | zero => intro _ s hs; omega
      | succ n ih =>
        intro h s hs
        simp only [okUpTo1, okCol1, Bool.and_eq_true] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact ih h.1 s hs
        · exact h.2
    obtain ⟨a4, a5⟩ := this 5 h1 c hc
    rcases (by omega : r = 4 ∨ r = 5) with rfl | rfl
    · exact a4
    · exact a5

/-- The glue cost of row group 0 (pushes, `AND`s, `MCOPY`s). -/
def gPure : Nat := 21 + 3 * 22 + 4 * (13 + 771) + 22 + 18

set_option maxRecDepth 10000 in
theorem exp_pure {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv4 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', PureOut s.executionEnv.calldata m' ∧
      Reach (callState s 3556 [flag b] m)
        (callState s 3674 [flag (b && okUpTo0 s.executionEnv.calldata 5)] m')
        (gPure + 5 * Gas.group + Gas.pass3f4) := by
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  -- group 0 → CW
  obtain ⟨m1, hb1, hf1, hr1⟩ := group_copy hs hcd hI.rc4 hI.rho (b := b)
    (col := 0) (pc := 3556) (ret := 3567) (pcm := 3578) (dst := CW) (c1 := 21) (by norm_num)
    (by opt65_reach [1206, 1207, 1208, 1209, 1210, 1211]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by opt65_reach [1212, 1213, 1214, 1215, 1216] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, CW]) ⟨1217, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold CW TOP; omega)
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by unfold groupFrame; avoids_tac)
  have hrho1 := Rho1At.frame hI.rho hf1 (by unfold groupFrame; avoids_tac)
  -- group 1 → HP
  obtain ⟨m2, hb2, hf2, hr2⟩ := group_copy hs hcd hrc1 hrho1 (b := b && okCol0 s.executionEnv.calldata 0)
    (col := 1) (pc := 3579) (ret := 3591) (pcm := 3603) (dst := HP) (c1 := 22) (by norm_num)
    (by opt65_reach [1218, 1219, 1220, 1221, 1222, 1223]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by opt65_reach [1224, 1225, 1226, 1227, 1228] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, HP]) ⟨1229, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP TOP; omega)
  have hrc2 := RC4Table.frame hrc1 hf2 (by unfold groupFrame; avoids_tac)
  have hrho2 := Rho1At.frame hrho1 hf2 (by unfold groupFrame; avoids_tac)
  -- group 2 → HP + 0x2000
  obtain ⟨m3, hb3, hf3, hr3⟩ := group_copy hs hcd hrc2 hrho2
    (b := b && okCol0 s.executionEnv.calldata 0 && okCol0 s.executionEnv.calldata 1)
    (col := 2) (pc := 3604) (ret := 3616) (pcm := 3628) (dst := HP + 8192) (c1 := 22) (by norm_num)
    (by opt65_reach [1230, 1231, 1232, 1233, 1234, 1235]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by opt65_reach [1236, 1237, 1238, 1239, 1240] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, HP]) ⟨1241, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold HP TOP; omega)
  have hrc3 := RC4Table.frame hrc2 hf3 (by unfold groupFrame; avoids_tac)
  have hrho3 := Rho1At.frame hrho2 hf3 (by unfold groupFrame; avoids_tac)
  -- group 3 → ACC + 0x2000
  obtain ⟨m4, hb4, hf4, hr4⟩ := group_copy hs hcd hrc3 hrho3
    (b := b && okCol0 s.executionEnv.calldata 0 && okCol0 s.executionEnv.calldata 1 &&
      okCol0 s.executionEnv.calldata 2)
    (col := 3) (pc := 3629) (ret := 3641) (pcm := 3652) (dst := ACC + 8192) (c1 := 22) (by norm_num)
    (by opt65_reach [1242, 1243, 1244, 1245, 1246, 1247]) (by simp only [isValidJumpDest_lit])
    (by norm_num) (fun M => by opt65_reach [1248, 1249, 1250, 1251, 1252] with [flag,
      MlDsaOpt44.Proofs.ite01_land, ABUF, ACC]) ⟨1253, by norm_num⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by norm_num) (by unfold ACC TOP; omega)
  have hrc4 := RC4Table.frame hrc3 hf4 (by unfold groupFrame; avoids_tac)
  have hrho4 := Rho1At.frame hrho3 hf4 (by unfold groupFrame; avoids_tac)
  -- group 4, `pass3f4`
  generalize hb4' : (b && okCol0 s.executionEnv.calldata 0 && okCol0 s.executionEnv.calldata 1 &&
      okCol0 s.executionEnv.calldata 2 && okCol0 s.executionEnv.calldata 3) = b4 at hr4
  have g41 : Reach (callState s 3653 [flag b4] m4)
      (callState s 14460 [wd 15, wd 4, wd 0, wd 3665, flag b4] m4) 22 := by
    opt65_reach [1254, 1255, 1256, 1257, 1258, 1259]
  obtain ⟨m5, hpost5, hf5, hc5⟩ := group_call hs (ret := 3665) (tail := [flag b4])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4 hrc4 hrho4
    (amask := 15) (col := 4) (rb := 0) (by norm_num) (by norm_num) (by norm_num) hcd
  rw [call_iff, s3_gOk_g0] at hc5
  have g42 : Reach (callState s 3665 [flag (okCol0 s.executionEnv.calldata 4), flag b4] m5)
      (callState s 11019 [wd 3674, flag (b4 && okCol0 s.executionEnv.calldata 4)] m5) 18 := by
    opt65_reach [1260, 1261, 1262, 1263, 1264] with [flag, MlDsaOpt44.Proofs.ite01_land]
  obtain ⟨m6, hw6, hf6, hc6⟩ := pass3f4_call hs (ret := 3674)
    (tail := [flag (b4 && okCol0 s.executionEnv.calldata 4)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
  rw [call_iff] at hc6
  -- the buffers at `pass3f4`
  have hb5 : BufCol m5 ABUF s.executionEnv.calldata 4 := fun hok t ht => by
    obtain ⟨junk, -, hw⟩ := hpost5 (by rw [s3_gOk_g0]; exact hok)
    rw [hw t ht, s3_pack4_ite (fun r hr => by interval_cases r <;> decide)]
    simp only [colBuf, Nat.mul_zero, Nat.zero_add]
  have c0 := ((hb1.frame hf2 (by unfold groupFrame; avoids_tac)).frame hf3 (by unfold groupFrame; avoids_tac)
    |>.frame hf4 (by unfold groupFrame; avoids_tac)).frame hf5 (by unfold groupFrame; avoids_tac)
  have c1 := (hb2.frame hf3 (by unfold groupFrame; avoids_tac)
    |>.frame hf4 (by unfold groupFrame; avoids_tac)).frame hf5 (by unfold groupFrame; avoids_tac)
  have c2 := (hb3.frame hf4 (by unfold groupFrame; avoids_tac)).frame hf5 (by unfold groupFrame; avoids_tac)
  have c3 := hb4.frame hf5 (by unfold groupFrame; avoids_tac)
  have hfA : FrameExcept m m5 (groupFrame 0 ++ [(CW, CW + 8192)] ++ (groupFrame 0 ++ [(HP, HP + 8192)]) ++
      (groupFrame 0 ++ [(HP + 8192, HP + 8192 + 8192)]) ++ (groupFrame 0 ++ [(ACC + 8192, ACC + 8192 + 8192)]) ++
      groupFrame 0) := (((hf1.trans hf2).trans hf3).trans hf4).trans hf5
  have hfB := hfA.trans hf6
  have hz5 : ZHatAt m5 s.executionEnv.calldata :=
    ZHatAt.frame hI.zhat hfA (by unfold groupFrame; avoids_tac)
  refine ⟨m6, ⟨RC4Table.frame hI.rc4 hfB (by unfold groupFrame; avoids_tac),
    RC1Table.frame hI.rc1 hfB (by unfold groupFrame; avoids_tac),
    TblAt.frame hI.tbl hfB (by unfold groupFrame; avoids_tac),
    ZHatAt.frame hI.zhat hfB (by unfold groupFrame; avoids_tac),
    Rho1At.frame hI.rho hfB (by unfold groupFrame; avoids_tac), ?_,
    ZeroOn.frame (ZeroOn.mono hI.zMisc (by unfold MISC NNEG; omega) (by unfold NNEG TBL; omega)) hfB
      (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (le_refl _) (by unfold BASES FIN; omega)) hfB
      (by unfold groupFrame; avoids_tac),
    ZeroOn.frame (ZeroOn.mono hI.zHigh (by unfold BASES IDX; omega) (by unfold IDX FIN; omega)) hfB
      (by unfold groupFrame; avoids_tac)⟩, ?_⟩
  · intro hok t ht
    rw [hw6 t ht, p3f4_acc hz5 c0 c1 c2 c3 hb5 hok ht]
    exact congrArg pack4 (funext fun r => (s3_accSum_congr 5 fun k hk =>
      zhLane_frame hf6 (by avoids_tac) (by omega) ht).symm)
  · have e : (b4 && okCol0 s.executionEnv.calldata 4) = (b && okUpTo0 s.executionEnv.calldata 5) := by
      rw [← hb4', okUpTo0_five]
    rw [e] at hc6 g42
    simp only [List.nil_append, Entry.pass3f4] at hc6
    rw [show (3578 : Nat) + 1 = 3579 from rfl] at hr1
    rw [show (3603 : Nat) + 1 = 3604 from rfl] at hr2
    rw [show (3628 : Nat) + 1 = 3629 from rfl] at hr3
    rw [show (3652 : Nat) + 1 = 3653 from rfl] at hr4
    have h12 := hr1.trans hr2
    have h123 := h12.trans hr3
    have h1234 := h123.trans hr4
    have h5 := g41.trans hc5
    have h56 := g42.trans hc6
    have h := h1234.trans (h5.trans h56)
    refine h.mono ?_
    unfold gPure
    generalize Gas.group = G
    generalize Gas.pass3f4 = P
    omega

end Exp

end MlDsaOpt65.Proofs
