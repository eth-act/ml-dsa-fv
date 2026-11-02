import MlDsaOpt44.Main.SegG2
set_option warningAsError true
/-!
# Slot states of the packed window (`seg_win`) and its first part

Calls 15 … 22 of `emit_window44`:

| call | slot 0 | slot 1 | slot 2 | slot 3 |
|---|---|---|---|---|
| 15–17 | tr 5–7 | A03 | A13 | A23 |
| 18, 19 | tr 8, 9 | A03 | A33 | A32 |
| 20 | c | μ block 0 | A33 | A32 |
| 21, 22 | A13 | A23 | A33 | A32 |

`W1 b` is the state before call `15 + b`, `W2 b` before call `18 + b`, `W3`
before call 20, `W4 b` before call `21 + b`; `EB b` is the state squeezed by
call `18 + b` (its block is `ABUF` block `b`).
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

def W1 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 0 then absorbPre 136 (padPk cd) (5 + b) else permN b (seedA cd (k - 1) 3)

def W2 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 0 then absorbPre 136 (padPk cd) (8 + b)
  else if k = 1 then permN (3 + b) (seedA cd 0 3)
  else if k = 2 then permN b (seedA cd 3 3) else permN b (seedA cd 3 2)

/-- `c̃`'s seed state and μ's state after absorbing block 0 (unpermuted). -/
def C0 (cd : ByteArray) : Fips202.SpongeState := seedState 136 (ctOf cd)
def Mu0 (cd : ByteArray) : Fips202.SpongeState := Fips202.xorBlock 136 (padMu cd) 0 Fips202.emptyState

def W3 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then C0 cd else if k = 1 then Mu0 cd else W2 cd 2 k

def W4 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 0 then permN (3 + b) (seedA cd 1 3)
  else if k = 1 then permN (3 + b) (seedA cd 2 3)
  else if k = 2 then permN (3 + b) (seedA cd 3 3) else permN (3 + b) (seedA cd 3 2)

def EB (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if b < 2 then W2 cd (b + 1) k else if b = 2 then Keccak.permute (W3 cd k) else W4 cd (b - 2) k

theorem seedA_size (cd : ByteArray) (r col : Nat) : (seedA cd r col).size = 25 := seedState_size _ _

theorem W1_sized (cd : ByteArray) (b : Nat) : Sized4 (W1 cd b) := fun k _ => by
  unfold W1; split
  · exact absorbPre_size _ _ _
  · exact permN_size (seedA_size _ _ _) _

theorem W2_sized (cd : ByteArray) (b : Nat) : Sized4 (W2 cd b) := fun k _ => by
  unfold W2; split
  · exact absorbPre_size _ _ _
  · split
    · exact permN_size (seedA_size _ _ _) _
    · split <;> exact permN_size (seedA_size _ _ _) _

theorem W3_sized (cd : ByteArray) : Sized4 (W3 cd) := fun k hk => by
  unfold W3; split
  · exact seedState_size _ _
  · split
    · unfold Mu0; rw [xorBlock_size]; exact emptyState_size
    · exact W2_sized cd 2 k hk

theorem W4_sized (cd : ByteArray) (b : Nat) : Sized4 (W4 cd b) := fun k _ => by
  unfold W4; split
  · exact permN_size (seedA_size _ _ _) _
  · split
    · exact permN_size (seedA_size _ _ _) _
    · split <;> exact permN_size (seedA_size _ _ _) _

theorem permute_upd_W1 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (upd (W1 cd b) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) ((5 + b) * 136) (W1 cd b 0)) k) =
      W1 cd (b + 1) k := by
  unfold upd W1
  by_cases h0 : k = 0
  · subst h0; simp only [if_true]
    rw [show 5 + (b + 1) = (5 + b) + 1 by omega, absorbPre_succ]; rfl
  · rw [if_neg h0, if_neg h0, if_neg h0, permN_succ]

theorem permute_upd_W2 (cd : ByteArray) {k : Nat} (hk : k < 4) :
    Keccak.permute (upd (W2 cd 0) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) ((8 + 0) * 136) (W2 cd 0 0)) k) =
      W2 cd 1 k := by
  unfold upd W2
  by_cases h0 : k = 0
  · subst h0; simp only [if_true]
    rw [show 8 + 1 = (8 + 0) + 1 by omega, absorbPre_succ]; rfl
  · rw [if_neg h0, if_neg h0, if_neg h0]
    split
    · rw [← permN_succ]
    · split <;> rw [← permN_succ]

/-! ## Part A: `3875 … 4149` (`ginit`, calls 15 … 17, the image `SAVE0`) -/

/-- Block buffers `ACC` / `BASES` (staging of `B3`). -/
theorem bufOK_acc : BufOK ACC BASES := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem winA_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState}
    (hks : KS4 m S) (hS0 : S 0 = absorbPre 136 (padPk s.executionEnv.calldata) 5) :
    ∃ m1, KS4 m1 (W1 s.executionEnv.calldata 0) ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s 3875 [flag w] m) (callState s 3930 [flag w] m1) (25 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho hS0
  have g0 : Reach (callState s 3875 [flag w] m)
      (callState s 10911 [wd 0x0eeeee00000084000000ee, wd 0, wd 14,
        wd 0x1111111111111111111111111111111111111111111111111111111111111111, wd 3930, flag w] m) 25 := by
    opt44_reach [1274, 1275, 1276, 1277, 1278, 1279, 1280]
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 3930) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (keep := 0x1111111111111111111111111111111111111111111111111111111111111111) (amult := 14)
    (cmult := 0) (l4 := 0x0eeeee00000084000000ee)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hkeep : (0x1111111111111111111111111111111111111111111111111111111111111111 : Nat) =
      il fun k => if (1 : Nat).testBit k then M64 else 0 := by decide +kernel
  have hks1 : KS4 m1 (W1 cd 0) :=
    ks4_ginit (kmask := 1) (L := fun k => if k = 0 then 0 else 3 + 256 * (k - 1) + 0x1F0000)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := S)
      (by norm_num) (by norm_num) hkeep (by decide +kernel)
      (fun x hx => (hrho x hx).1) (fun x hx => (hrho x hx).2)
      (fun x hx => by rw [hkeep]; exact ks4_and_keep hks 1 hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k hk h => by
        have : k = 0 := by
          by_contra hne
          interval_cases k <;> first | omega | exact absurd h (by decide)
        subst this; exact ⟨by decide, by decide, rfl⟩)
      (fun k hk h => by
        have : k = 0 := by
          by_contra hne
          interval_cases k <;> first | omega | exact absurd h (by decide)
        subst this; unfold W1; rw [if_pos rfl, hS0])
      (fun k hk h x hx => by
        have h0 : k ≠ 0 := by rintro rfl; simp at h
        have e : W1 cd 0 k = seedA cd (k - 1) 3 := by unfold W1; rw [if_neg h0]; rfl
        rw [e]
        exact freshLane_aSeed (by unfold HDR at hcd; omega) (fun _ _ => rfl) (by omega) (by norm_num)
          (by interval_cases k <;> first | omega | decide) (by simp)
          (by simp only [if_neg h0]) hx)
      hg
  exact ⟨m1, hks1, hf1, g0.trans hc1⟩

theorem winA {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState}
    (hks : KS4 m S) (hS0 : S 0 = absorbPre 136 (padPk s.executionEnv.calldata) 5) :
    ∃ m', KS4 m' (W1 s.executionEnv.calldata 3) ∧
      HBlocks m' ACC BASES (fun b k => W1 s.executionEnv.calldata (b + 1) k) 3 ∧
      St4At m' SAVE0 (W1 s.executionEnv.calldata 3) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ACC, ACC + 1792 * 3), (BASES, BASES + 224 * 3),
        (SAVE0, SAVE0 + 800)] ∧
      Reach (callState s 3875 [flag w] m) (callState s 4149 [flag w] m')
        (25 + Gas.ginit + 3 * (28 + Gas.trabs 5 + (15 + Gas.kf4 + 21 + Gas.blk)) + 9 + 78) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1312 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have htl : [flag w].length ≤ 8 := by simp
  obtain ⟨m1, hks1, hf1, hR1⟩ := winA_ginit hs hcd hrho hks hS0
  have hrc1 := hrc.frame hf1 (by avoids_tac)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcd' htl (m := m1)
    (pc0 := 3930) (r0 := 3978) (r1 := 3986) (r2 := 4000) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 0) (j := 5) (off := 680) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_acc
    (by opt44_reach [1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289])
    (fun _ => by opt44_reach [1290, 1291, 1292, 1293])
    (fun _ => by opt44_reach [1294, 1295, 1296, 1297, 1298, 1299] with [ACC, BASES])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (W1_sized _ 0) hks1 (HBlocks.zero _ _ _ _) (St := fun b k => W1 s.executionEnv.calldata (b + 1) k)
    (fun k hk => (permute_upd_W1 _ 0 hk).symm)
  have hks2 : KS4 m2 (W1 s.executionEnv.calldata 1) := KS4.congr hks2' fun k hk => permute_upd_W1 _ 0 hk
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcd' htl (m := m2)
    (pc0 := 4000) (r0 := 4048) (r1 := 4056) (r2 := 4070) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 1) (j := 6) (off := 816) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_acc
    (by opt44_reach [1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308])
    (fun _ => by opt44_reach [1309, 1310, 1311, 1312])
    (fun _ => by opt44_reach [1313, 1314, 1315, 1316, 1317, 1318] with [ACC, BASES])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (W1_sized _ 1) hks2 hB2 (St := fun b k => W1 s.executionEnv.calldata (b + 1) k)
    (fun k hk => (permute_upd_W1 _ 1 hk).symm)
  have hks3 : KS4 m3 (W1 s.executionEnv.calldata 2) := KS4.congr hks3' fun k hk => permute_upd_W1 _ 1 hk
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcd' htl (m := m3)
    (pc0 := 4070) (r0 := 4118) (r1 := 4126) (r2 := 4140) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 2) (j := 7) (off := 952) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_acc
    (by opt44_reach [1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327])
    (fun _ => by opt44_reach [1328, 1329, 1330, 1331])
    (fun _ => by opt44_reach [1332, 1333, 1334, 1335, 1336, 1337] with [ACC, BASES])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (W1_sized _ 2) hks3 hB3 (St := fun b k => W1 s.executionEnv.calldata (b + 1) k)
    (fun k hk => (permute_upd_W1 _ 2 hk).symm)
  have hks4 : KS4 m4 (W1 s.executionEnv.calldata 3) := KS4.congr hks4' fun k hk => permute_upd_W1 _ 2 hk
  -- the image SAVE0
  have g5 : Reach (callState s 4140 [flag w] m4) (callState s 4148 [wd SAVE0, wd KS, wd 800, flag w] m4) 9 := by
    opt44_reach [1338, 1339, 1340, 1341] with [SAVE0, KS]
  have hmc := reach_mcopy hs ⟨1342, by norm_num⟩ (pc := 4148) (d := SAVE0) (src := KS) (n := 800)
    (rest := [flag w]) (m := m4)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold SAVE0; norm_num)
    (by unfold KS; norm_num) (by norm_num) (by norm_num) (by unfold SAVE0; omega) (by unfold KS; omega) (by simp)
  have hf5 := FrameExcept.mcopy m4 KS SAVE0 800
  refine ⟨_, KS4.frame hks4 hf5 (by avoids_tac), HBlocks.frame hB4 hf5 (by avoids_tac) (by avoids_tac),
    fun x hx => ?_, hrc4.frame hf5 (by avoids_tac), ?_, ?_⟩
  · rw [word_mcopy _ (by omega) (by omega), show KS + (SAVE0 + 32 * x - SAVE0) = KS + 32 * x by omega]
    exact hks4 x hx
  · have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hf2) hf3) hf4) hf5
    exact hf.mono (by decide)
  · have hR := ((((hR1.trans hR2).trans hR3).trans hR4).trans g5).trans hmc
    refine hR.mono (le_of_eq ?_)
    generalize Gas.ginit = a; generalize Gas.trabs 5 = c; generalize Gas.kf4 = d; generalize Gas.blk = e
    omega

end MlDsaOpt44.Proofs.Ex
