import MlDsaOpt44.Main.SegG234.Round
import MlDsaOpt44.Fn.Group
set_option warningAsError true
/-!
# Group 2 of `seg_g234` (`3466 … 3898`)

Slots 0–2 squeeze `A[0][2]`, `A[1][2]`, `A[2][2]`; slot 3 absorbs the first five
blocks of the padded public key (the `tr` rider). Then `gfix 7` and
`pass3m` (rows 0–2 of column 2 into `ACC`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The padded public key (input of `tr = H(pk)`). -/
def padPk (cd : ByteArray) : ByteArray := Fips202.pad 136 0x1F (pkOf cd)

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    aI (seedA cd r col) = aOf cd r col :=
  aI_seedState (by rw [aSeed_size hcd]; norm_num)

/-- Rows `0 … 2` of column `col` exist. -/
def rows3 (cd : ByteArray) (col : Nat) : Bool :=
  (aOf cd 0 col).isSome && (aOf cd 1 col).isSome && (aOf cd 2 col).isSome

/-- The `ACC` update of a masked group (rows `0 … 2`). -/
def acc3 (cd m : ByteArray) (col t : Nat) : Nat :=
  (word m (ACC + 32 * t) +
    pack4 (fun r => if r < 3 then ((aD cd r col)[t]!).toNat else 0) * lane (word m (ZH + 32 * t)) col) %
      2 ^ 256

/-- `gfix 7`'s flag on the seeds of column `col`. -/
theorem gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl || (aI (if sl < 3 then seedA cd sl col
      else Fips202.emptyState)).isSome) = rows3 cd col := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide, show (2 : Nat) < 3 by decide,
    if_true, aI_seedA hcd, rows3]
  cases (aOf cd 0 col).isSome <;> cases (aOf cd 1 col).isSome <;> cases (aOf cd 2 col).isSome <;> rfl

theorem and_low3 (w : Nat) : w &&& (2 ^ 192 - 1) = pack4 fun r => if r < 3 then lane w r else 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  unfold pack4 lane
  simp only [show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide,
    show (2 : Nat) < 3 by decide, if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
  norm_num
  omega

/-- The masked `pass3m` of a group whose slots `0 … 2` hold column `col`. -/
theorem pass3m_rows {cd m6 : ByteArray} {col : Nat}
    (hlanes : ∀ sl, sl < 3 → ∀ a, aOf cd sl col = some a →
      ∀ t, t < 256 → lane (word m6 (ABUF + 32 * t)) sl = (a[t]!).toNat)
    (hrows : rows3 cd col = true) {t : Nat} (ht : t < 256) :
    (word m6 (ABUF + 32 * t) &&& (2 ^ 192 - 1)) =
      pack4 fun r => if r < 3 then ((aD cd r col)[t]!).toNat else 0 := by
  rw [and_low3]
  apply pack4_congr
  intro r hr
  split
  · have hs : (aOf cd r col).isSome = true := by
      unfold rows3 at hrows
      simp only [Bool.and_eq_true] at hrows
      interval_cases r
      · exact hrows.1.1
      · exact hrows.1.2
      · exact hrows.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    rw [hlanes r (by omega) a ha t ht]
    unfold aD; rw [ha]; rfl
  · rfl

/-! ## Slot states -/

/-- Group 2 at the start of squeeze `b`: rows of column 2 in slots 0–2, the
`tr` sponge in slot 3. -/
def X2 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedA cd k 2) else absorbPre 136 (padPk cd) b

theorem X2_sized (cd : ByteArray) (b : Nat) : Sized4 (X2 cd b) := fun k _ => by
  unfold X2; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ b

/-- After absorbing block `b` into slot 3. -/
def Y2 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 3 then Fips202.xorBlock 136 (padPk cd) (b * 136) (X2 cd b 3) else X2 cd b k

theorem Y2_sized (cd : ByteArray) (b : Nat) : Sized4 (Y2 cd b) := fun k hk => by
  unfold Y2; split
  · rw [xorBlock_size]; exact X2_sized cd b 3 (by omega)
  · exact X2_sized cd b k hk

theorem permute_Y2 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (Y2 cd b k) = X2 cd (b + 1) k := by
  unfold Y2 X2
  by_cases h3 : k = 3
  · subst h3; simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), permN_succ]

/-- Group 2's cost: glue 404 and its calls. -/
def costG2 : Nat :=
  404 + Gas.ginit + 5 * (Gas.trabs 5 + Gas.kf4 + Gas.blk) + Gas.gfix 3 + Gas.pass3m

theorem g2_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (X2 s.executionEnv.calldata 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 3466 [flag b] m) (callState s 3494 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have g0 : Reach (callState s 3466 [flag b] m)
      (callState s 11084 [wd 0x0777770000004200000070, wd 0, wd 7, wd 0, wd 3494, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    opt44_reach [1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 3494) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 7) (cmult := 0) (l4 := 0x0777770000004200000070)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := hrho.frame hf0 (by avoids_tac)
  have hks : KS4 m1 (X2 cd 0) :=
    ks4_ginit (kmask := 0) (L := fun k => if k < 3 then 2 + 256 * k + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := X2 cd 0)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        by_cases h3 : k < 3
        · have e : X2 cd 0 k = seedA cd k 2 := by unfold X2; rw [if_pos h3]; rfl
          rw [e]
          exact freshLane_aSeed (by unfold HDR at hcd; omega) (fun _ _ => rfl) (by omega) (by norm_num)
            (by interval_cases k <;> decide) (by simp) (by simp [h3]) hx
        · have e : X2 cd 0 k = Fips202.emptyState := by unfold X2; rw [if_neg h3]; rfl
          rw [e]
          have hk3 : k = 3 := by omega
          subst hk3
          exact freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m', KS4 m' (X2 s.executionEnv.calldata 5) ∧ RC4Table m' ∧
      (rows3 s.executionEnv.calldata 2 = true → ∀ t, t < 256 →
        word m' (ACC + 32 * t) = acc3 s.executionEnv.calldata m 2 t) ∧
      FrameExcept m m' groupFrame ∧
      Reach (callState s 3466 [flag b] m)
        (callState s 3898 [flag (b && rows3 s.executionEnv.calldata 2)] m') costG2 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1312 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g2_ginit hs hcd hrho b
  have hrc1 := hrc.frame hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcd' (fb := flag b) (m := m1)
    (pc0 := 3494) (r0 := 3541) (r1 := 3549) (r2 := 3563) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 0) (off := 0) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173])
    (fun _ => by opt44_reach [1174, 1175, 1176, 1177])
    (fun _ => by opt44_reach [1178, 1179, 1180, 1181, 1182, 1183] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (X2_sized _ 0) hks1 (Blocks.zero _ _) (St := fun b k => Keccak.permute (Y2 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks2 : KS4 m2 (X2 s.executionEnv.calldata 1) :=
    hks2'.congr fun k hk => permute_Y2 _ 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcd' (fb := flag b) (m := m2)
    (pc0 := 3563) (r0 := 3611) (r1 := 3619) (r2 := 3633) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 1) (j := 1) (off := 136) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192])
    (fun _ => by opt44_reach [1193, 1194, 1195, 1196])
    (fun _ => by opt44_reach [1197, 1198, 1199, 1200, 1201, 1202] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X2_sized _ 1) hks2 hB2 (St := fun b k => Keccak.permute (Y2 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks3 : KS4 m3 (X2 s.executionEnv.calldata 2) :=
    hks3'.congr fun k hk => permute_Y2 _ 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcd' (fb := flag b) (m := m3)
    (pc0 := 3633) (r0 := 3682) (r1 := 3690) (r2 := 3704) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 2) (j := 2) (off := 272) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211])
    (fun _ => by opt44_reach [1212, 1213, 1214, 1215])
    (fun _ => by opt44_reach [1216, 1217, 1218, 1219, 1220, 1221] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (X2_sized _ 2) hks3 hB3 (St := fun b k => Keccak.permute (Y2 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks4 : KS4 m4 (X2 s.executionEnv.calldata 3) :=
    hks4'.congr fun k hk => permute_Y2 _ 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcd' (fb := flag b) (m := m4)
    (pc0 := 3704) (r0 := 3753) (r1 := 3761) (r2 := 3775) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 3) (j := 3) (off := 408) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230])
    (fun _ => by opt44_reach [1231, 1232, 1233, 1234])
    (fun _ => by opt44_reach [1235, 1236, 1237, 1238, 1239, 1240] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (X2_sized _ 3) hks4 hB4 (St := fun b k => Keccak.permute (Y2 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks5 : KS4 m5 (X2 s.executionEnv.calldata 4) :=
    hks5'.congr fun k hk => permute_Y2 _ 3 hk
  -- squeeze 4
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round hs hcd' (fb := flag b) (m := m5)
    (pc0 := 3775) (r0 := 3824) (r1 := 3832) (r2 := 3846) (c0 := 29) (c1 := 15) (c2 := 21)
    (b := 4) (j := 4) (off := 544) (by norm_num) (by norm_num) (by norm_num)
    (by opt44_reach [1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249])
    (fun _ => by opt44_reach [1250, 1251, 1252, 1253])
    (fun _ => by opt44_reach [1254, 1255, 1256, 1257, 1258, 1259] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X2_sized _ 4) hks5 hB5 (St := fun b k => Keccak.permute (Y2 s.executionEnv.calldata b k))
    (fun k _ => rfl)
  have hks6 : KS4 m6 (X2 s.executionEnv.calldata 5) :=
    hks6'.congr fun k hk => permute_Y2 _ 4 hk
  -- gfix 7
  have h66 : word m6 HAVE6 = 0 := by
    have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
    rw [word_frame hf (lo := HAVE6) (hi := HAVE6 + 32) (by frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 3846 [flag b] m6) (callState s 10754 [wd 7, wd 3856, flag b] m6) 18 := by
    opt44_reach [1260, 1261, 1262, 1263, 1264]
  obtain ⟨m7, hlanes, hks7, hf7, hc7⟩ := gfix_call hs (ret := 3856) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 7) (by norm_num) 3 (by decide) (X2 s.executionEnv.calldata 5) (X2_sized _ 5) hks6
    (fun k => if k < 3 then seedA s.executionEnv.calldata k 2 else Fips202.emptyState) h66
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        have : sl = 3 := by omega
        subst this; exact absurd hbit (by decide)
      simp only [if_pos hsl3]
      refine hB6.pending hsl (fun b' hb' => ?_) h66 ?_
      · show Keccak.permute (Y2 _ b' sl) = _
        rw [permute_Y2 _ b' hsl]; unfold X2; rw [if_pos hsl3]
      · unfold X2; rw [if_pos hsl3])
  rw [gfix7_flag hcd32] at hc7
  -- pass3m (rows 0..2 of column 2)
  have gP : Reach (callState s 3856 [flag (rows3 s.executionEnv.calldata 2), flag b] m7)
      (callState s 10344 [wd (2 ^ 192 - 1), wd (64 * 2), wd ZH, wd ACC, wd 3898,
        flag (b && rows3 s.executionEnv.calldata 2)] m7) 30 := by
    opt44_reach [1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3m_call hs (ret := 3898)
    (tail := [flag (b && rows3 s.executionEnv.calldata 2)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
    (k := 2) (by norm_num) (lm := 2 ^ 192 - 1) (by norm_num)
  have hfA := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans (FrameExcept.trans hf1 hf2) hf3) hf4) hf5) hf6) hf7
  refine ⟨m8, hks7.frame hf8 (by avoids_tac), (hrc6.frame hf7 (by avoids_tac)).frame hf8 (by avoids_tac),
    fun hrows t ht => ?_, (FrameExcept.trans hfA hf8).mono (by unfold groupFrame; decide), ?_⟩
  · rw [hacc t ht, pass3m_rows (fun sl hsl a ha t ht => by
        have := hlanes sl (by omega) (by interval_cases sl <;> decide) a
        rw [if_pos hsl, aI_seedA hcd32] at this
        exact this ha t ht) hrows ht,
      word_frame hfA (a := ACC + 32 * t) (lo := ACC) (hi := ACC + 8192) (by frame_tac) (by omega) (by omega),
      word_frame hfA (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by frame_tac) (by omega) (by omega)]
    rfl
  · have hR := ((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gP).trans hc8
    exact hR.mono (by unfold costG2; omega)

end MlDsaOpt44.Proofs
