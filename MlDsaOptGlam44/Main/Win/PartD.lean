import MlDsaOptGlam44.Main.Win.States
import MlDsaOptGlam44.Main.Win.Math
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/Win/PartD.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Window part D: `4544 … 3720`

`kmove` resumes `A[1][3]`, `A[2][3]` (paused in `SAVE0` after call 17) in slots
0, 1; calls 21, 22 squeeze blocks 3, 4; two `lmerge` calls stage the heads of
blocks 3, 4 of `B3 = (A03, A13, A23)` (lanes 1 … 3) at `ACC + 3·1792` /
`BASES + 3·224`: lane 1 from `A03`'s blocks 3, 4 (`ABUF` blocks 0, 1, slot 1),
lanes 2, 3 from `ABUF` blocks 3, 4, slots 0, 1.
-/

namespace MlDsaOptGlam44.Proofs.Ex

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs MlDsaOpt44.Proofs
open MlDsaOptGlam44.Proofs.Infra

/-- The fix-up flag of group `g` of the stream started from `I` (as in `SlotHead`). -/
def FlagOf (I : Fips202.SpongeState) (g : Nat) : Nat :=
  if ((List.range 8).any fun i => decide (Fips204.q ≤ candI I (8 * g + i))) then 1 else 0

theorem HBlocks.laneI {m : ByteArray} {ab fl n : Nat} {St : Nat → Nat → Fips202.SpongeState}
    (h : HBlocks m ab fl St n) {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState} {b0 b i : Nat}
    (hb : b < n) (hi : i < 56) (hh : b * 56 + i < 256) (hSt : St b sl = permN (b0 + b + 1) I) :
    lane (word m (ab + 1792 * b + 32 * i)) sl = candI I ((b0 + b) * 56 + i) := by
  rw [(h b hb).1 i hi hh, lane_pack4_cand _ _ hsl, hSt]
  unfold candI
  rw [show ((b0 + b) * 56 + i) / 56 = b0 + b by omega, show ((b0 + b) * 56 + i) % 56 = i by omega]

theorem HBlocks.flagI {m : ByteArray} {ab fl n : Nat} {St : Nat → Nat → Fips202.SpongeState}
    (h : HBlocks m ab fl St n) {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState} {b0 b g : Nat}
    (hb : b < n) (hg : g < 7) (hh : b * 7 + g < 32) (hSt : St b sl = permN (b0 + b + 1) I) :
    flagBit (word m (fl + 224 * b + 32 * g)) sl = FlagOf I ((b0 + b) * 7 + g) := by
  rw [(h b hb).2 g hg hh, flagBit_flagWord _ _ hsl, hSt]
  unfold FlagOf
  rw [any_congr_mem (q := fun i => decide (Fips204.q ≤ candI I (8 * ((b0 + b) * 7 + g) + i))) fun i hi => by
    rw [List.mem_range] at hi
    unfold candI
    rw [show (8 * ((b0 + b) * 7 + g) + i) / 56 = b0 + b by omega,
      show (8 * ((b0 + b) * 7 + g) + i) % 56 = 8 * g + i by omega]]

/-- The seeds of `B3`'s slots. -/
def I3 (cd : ByteArray) (sl : Nat) : Fips202.SpongeState := seedA cd (sl - 1) 3

/-- The staged heads of blocks 3, 4 of `B3`. -/
def Merged (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ sl, 1 ≤ sl → sl < 4 →
    (∀ w, w < 88 → lane (word m (ACC + 1792 * 3 + 32 * w)) sl = candI (I3 cd sl) (168 + w)) ∧
    (∀ v, v < 11 → flagBit (word m (BASES + 224 * 3 + 32 * v)) sl = FlagOf (I3 cd sl) (21 + v))

theorem W4_perm (cd : ByteArray) (b : Nat) {k : Nat} (_hk : k < 4) :
    Keccak.permute (W4 cd b k) = W4 cd (b + 1) k := by
  unfold W4
  split
  · rw [← permN_succ, Nat.add_assoc]
  · split
    · rw [← permN_succ, Nat.add_assoc]
    · split <;> rw [← permN_succ, Nat.add_assoc]

theorem I3_1 (cd : ByteArray) : I3 cd 1 = seedA cd 0 3 := rfl
theorem I3_2 (cd : ByteArray) : I3 cd 2 = seedA cd 1 3 := rfl
theorem I3_3 (cd : ByteArray) : I3 cd 3 = seedA cd 2 3 := rfl

theorem EB_lo1 (cd : ByteArray) {b : Nat} (hb : b < 2) : EB cd b 1 = permN (3 + b + 1) (I3 cd 1) := by
  unfold EB W2
  rw [if_pos hb, if_neg (by decide), if_pos rfl, I3_1, Nat.add_assoc]

theorem EB_hi (cd : ByteArray) {b : Nat} (hb : 2 < b) :
    EB cd b 0 = permN (0 + b + 1) (I3 cd 2) ∧ EB cd b 1 = permN (0 + b + 1) (I3 cd 3) := by
  constructor
  · unfold EB W4
    rw [if_neg (by omega : ¬ b < 2), if_neg (by omega : ¬ b = 2), if_pos rfl, I3_2,
      show 3 + (b - 2) = 0 + b + 1 by omega]
  · unfold EB W4
    rw [if_neg (by omega : ¬ b < 2), if_neg (by omega : ¬ b = 2), if_neg (by decide : ¬ (1 : Nat) = 0),
      if_pos rfl, I3_3, show 3 + (b - 2) = 0 + b + 1 by omega]

theorem winD_kmove {s : State} (hs : Ctx s) {m : ByteArray} {w : Bool}
    (hks : KS4 m (fun k => Keccak.permute (W3 s.executionEnv.calldata k)))
    (hsv : St4At m SAVE0 (W1 s.executionEnv.calldata 3)) :
    ∃ m1, KS4 m1 (W4 s.executionEnv.calldata 0) ∧ FrameExcept m m1 [(KS, KS + 800)] ∧
      Reach (callState s 3519 [flag w] m) (callState s 3598 [flag w] m1) (28 + Gas.kmove) := by
  have g0 : Reach (callState s 3519 [flag w] m)
      (callState s 18414 [wd 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
        wd 0x3333333333333333333333333333333333333333333333333333333333333333, wd 2, wd 0, wd SAVE0,
        wd 3598, flag w] m) 28 := by
    glam44_rreach [1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254] with [SAVE0]
  obtain ⟨m1, hpost, hf1, hc1⟩ := kmove_call hs (ret := 3598) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (src := SAVE0) (sl := 0) (sr := 2)
    (msk := 0x3333333333333333333333333333333333333333333333333333333333333333)
    (keep := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)
    (Or.inr (by unfold KS SAVE0; norm_num)) (by unfold SAVE0 TOP; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨m1, fun x hx => ?_, hf1, g0.trans hc1⟩
  rw [hpost x hx, hsv x hx, hks x hx,
    kmove_down2 _ _ (fun k _ => cpl_lt (laneOf_lt _ _)) (fun k _ => cpl_lt (laneOf_lt _ _))]
  apply il_congr
  intro k hk
  interval_cases k
  · simp only [show (0 : Nat) < 2 by decide, if_true]; unfold W1 W4; simp
  · simp only [show (1 : Nat) < 2 by decide, if_true]; unfold W1 W4; simp
  · simp only [show ¬ (2 : Nat) < 2 by decide, if_false]
    unfold W3 W2 W4; simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
      if_true]
    rw [← permN_succ]
  · simp only [show ¬ (3 : Nat) < 2 by decide, if_false]
    unfold W3 W2 W4; simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
      show (3 : Nat) ≠ 2 by decide, if_false]
    rw [← permN_succ]

theorem lmerge_post {m m' : ByteArray} {a b dst : Nat}
    (h : ∀ w, w < 88 → word m' (dst + 32 * w) =
      let b' := word m (b + 32 * w) * 2 ^ 128 % 2 ^ 256
      b' ^^^ ((word m (a + 32 * w) ^^^ b') &&& 0xffffffffffffffff0000000000000000)) {w : Nat} (hw : w < 88) :
    lane (word m' (dst + 32 * w)) 1 = lane (word m (a + 32 * w)) 1 ∧
      lane (word m' (dst + 32 * w)) 2 = lane (word m (b + 32 * w)) 0 ∧
      lane (word m' (dst + 32 * w)) 3 = lane (word m (b + 32 * w)) 1 := by
  rw [h w hw]; exact lmerge_lanes _ _

theorem winD_merge {m m1 m2 : ByteArray} {cd : ByteArray} (hB : HBlocks m ABUF FL (EB cd) 5)
    (h1 : ∀ w, w < 11 * 8 → word m1 (ACC + 1792 * 3 + 32 * w) =
      let b' := word m (ABUF + 1792 * 3 + 32 * w) * 2 ^ 128 % 2 ^ 256
      b' ^^^ ((word m (ABUF + 32 * w) ^^^ b') &&& 0xffffffffffffffff0000000000000000))
    (h2 : ∀ w, w < 11 * 1 → word m2 (BASES + 224 * 3 + 32 * w) =
      let b' := word m1 (FL + 224 * 3 + 32 * w) * 2 ^ 128 % 2 ^ 256
      b' ^^^ ((word m1 (FL + 32 * w) ^^^ b') &&& 0xffffffffffffffff0000000000000000))
    (hf2 : FrameExcept m1 m2 [(BASES + 224 * 3, BASES + 224 * 3 + 352 * 1)])
    (hfl : ∀ a, FL ≤ a → a + 32 ≤ FL + 1120 → word m1 a = word m a) :
    Merged m2 cd := by
  intro sl hsl1 hsl4
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · have hw56 : w / 56 < 2 := by omega
    have hw' : w % 56 < 56 := Nat.mod_lt _ (by norm_num)
    have ha : ABUF + 32 * w = ABUF + 1792 * (w / 56) + 32 * (w % 56) := by omega
    have hb : ABUF + 1792 * 3 + 32 * w = ABUF + 1792 * (3 + w / 56) + 32 * (w % 56) := by
      rw [show 32 * w = 1792 * (w / 56) + 32 * (w % 56) by omega]; ring
    have h168 : ∀ b0, (b0 + w / 56) * 56 + w % 56 = b0 * 56 + w := fun b0 => by omega
    rw [word_frame hf2 (lo := ACC + 1792 * 3) (hi := ACC + 1792 * 3 + 2816) (by avoids_tac) (by omega)
      (by omega)]
    obtain ⟨e1, e2, e3⟩ := lmerge_post (m := m) (m' := m1) (a := ABUF) (b := ABUF + 1792 * 3)
      (dst := ACC + 1792 * 3) h1 hw
    interval_cases sl
    · rw [e1, ha, hB.laneI (I := I3 cd 1) (b0 := 3) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num))
        (by omega) (EB_lo1 cd hw56), h168]
    · rw [e2, hb, hB.laneI (I := I3 cd 2) (b0 := 0) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num))
        (by omega) (EB_hi cd (b := 3 + w / 56) (by omega)).1, Nat.zero_add, h168]
    · rw [e3, hb, hB.laneI (I := I3 cd 3) (b0 := 0) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num))
        (by omega) (EB_hi cd (b := 3 + w / 56) (by omega)).2, Nat.zero_add, h168]
  · have hv' : v < 11 * 1 := by omega
    have hv7 : v / 7 < 2 := by omega
    have ha : FL + 32 * v = FL + 224 * (v / 7) + 32 * (v % 7) := by omega
    have hb : FL + 224 * 3 + 32 * v = FL + 224 * (3 + v / 7) + 32 * (v % 7) := by
      rw [show 32 * v = 224 * (v / 7) + 32 * (v % 7) by omega]; ring
    have h21 : ∀ b0, (b0 + v / 7) * 7 + v % 7 = b0 * 7 + v := fun b0 => by omega
    have hfa : FL ≤ FL + 32 * v ∧ FL + 32 * v + 32 ≤ FL + 1120 := by omega
    have hfb : FL ≤ FL + 224 * 3 + 32 * v ∧ FL + 224 * 3 + 32 * v + 32 ≤ FL + 1120 := by
      constructor <;> generalize FL = f <;> omega
    have e := h2 v hv'
    dsimp only at e
    have hlanes := lmerge_lanes (word m1 (FL + 32 * v)) (word m1 (FL + 224 * 3 + 32 * v))
    rw [← e] at hlanes
    obtain ⟨e1, e2, e3⟩ := hlanes
    rw [hfl _ hfa.1 hfa.2] at e1
    rw [hfl _ hfb.1 hfb.2] at e2 e3
    rw [flagBit_eq_lane _ _ hsl4]
    interval_cases sl
    · rw [e1, ← flagBit_eq_lane _ _ (by norm_num), ha,
        hB.flagI (I := I3 cd 1) (b0 := 3) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num)) (by omega)
          (EB_lo1 cd hv7), h21]
    · rw [e2, ← flagBit_eq_lane _ _ (by norm_num), hb,
        hB.flagI (I := I3 cd 2) (b0 := 0) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num)) (by omega)
          (EB_hi cd (b := 3 + v / 7) (by omega)).1, Nat.zero_add, h21]
    · rw [e3, ← flagBit_eq_lane _ _ (by norm_num), hb,
        hB.flagI (I := I3 cd 3) (b0 := 0) (by norm_num) (by omega) (Nat.mod_lt _ (by norm_num)) (by omega)
          (EB_hi cd (b := 3 + v / 7) (by omega)).2, Nat.zero_add, h21]

end MlDsaOptGlam44.Proofs.Ex

namespace MlDsaOptGlam44.Proofs.Ex

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs MlDsaOpt44.Proofs
open MlDsaOptGlam44.Proofs.Infra

/-- Window part D. -/
theorem winD {s : State} (hs : Ctx s) {m : ByteArray} {w : Bool} (hrc : RC4Table m)
    (hks : KS4 m (fun k => Keccak.permute (W3 s.executionEnv.calldata k)))
    (hsv : St4At m SAVE0 (W1 s.executionEnv.calldata 3)) (hB : HBlocks m ABUF FL (EB s.executionEnv.calldata) 3) :
    ∃ m', KS4 m' (W4 s.executionEnv.calldata 2) ∧ HBlocks m' ABUF FL (EB s.executionEnv.calldata) 5 ∧
      Merged m' s.executionEnv.calldata ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * 3, ABUF + 1792 * 3 + 1792),
        (FL + 224 * 3, FL + 224 * 3 + 224), (ABUF + 1792 * 4, ABUF + 1792 * 4 + 1024),
        (FL + 224 * 4, FL + 224 * 4 + 128), (ACC + 1792 * 3, ACC + 1792 * 3 + 352 * 8),
        (BASES + 224 * 3, BASES + 224 * 3 + 352 * 1)] ∧
      Reach (callState s 3519 [flag w] m) (callState s 3720 [flag w] m')
        (28 + Gas.kmove + (15 + Gas.kf4 + 21 + Gas.blk) + (15 + Gas.kf4 + 21 + Gas.blkh) +
          33 + Gas.lmerge 8 + 33 + Gas.lmerge 1) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have htl : [flag w].length ≤ 8 := by simp
  obtain ⟨m1, hks1, hf1, hR1⟩ := winD_kmove hs hks hsv (w := w)
  have hrc1 := hrc.frame hf1 (by avoids_tac)
  -- call 21
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := kb_round hs htl (stk := [flag w]) (m := m1)
    (pc0 := 3598) (r1 := 3606) (r2 := 3620) (c1 := 15) (c2 := 21) (b := 3) (by norm_num) bufOK_abuf
    (by glam44_rreach [1255, 1256, 1257, 1258])
    (fun _ => by glam44_rreach [1259, 1260, 1261, 1262, 1263, 1264] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (W4_sized _ 0) hks1 (hB.frame hf1 (by avoids_tac) (by avoids_tac)) (St := EB s.executionEnv.calldata)
    (fun k hk => by rw [W4_perm _ 0 hk]; unfold EB; rw [if_neg (by decide), if_neg (by decide)])
  have hks2 : KS4 m2 (W4 s.executionEnv.calldata 1) := KS4.congr hks2' fun k hk => W4_perm _ 0 hk
  -- call 22
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kbh_round hs htl (stk := [flag w]) (m := m2)
    (pc0 := 3620) (r1 := 3628) (r2 := 3642) (c1 := 15) (c2 := 21) bufOK_abuf
    (by glam44_rreach [1265, 1266, 1267, 1268])
    (fun _ => by glam44_rreach [1269, 1270, 1271, 1272, 1273, 1274] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (W4_sized _ 1) hks2 hB2 (St := EB s.executionEnv.calldata)
    (fun k hk => by rw [W4_perm _ 1 hk]; unfold EB; rw [if_neg (by decide), if_neg (by decide)])
  have hks3 : KS4 m3 (W4 s.executionEnv.calldata 2) := KS4.congr hks3' fun k hk => W4_perm _ 1 hk
  -- lmerge: blocks 3, 4 of B3
  have gL1 : Reach (callState s 3642 [flag w] m3) (callState s 18541 [wd ABUF, wd (ABUF + 352 * 8), wd 128,
      wd ((ABUF + 1792 * 3 + 2 ^ 256 - ABUF) % 2 ^ 256), wd 0xffffffffffffffff0000000000000000,
      wd ((ACC + 1792 * 3 + 2 ^ 256 - ABUF) % 2 ^ 256), wd 3681, flag w] m3) 33 := by
    glam44_rreach [1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284] with [ABUF, ACC]
  obtain ⟨m4, h4, hf4, hc4⟩ := lmerge_call hs (ret := 3681) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := ACC + 1792 * 3) (a := ABUF) (b := ABUF + 1792 * 3) (ma := 0xffffffffffffffff0000000000000000)
    (sl := 128) (k := 8) (by norm_num) (by unfold ACC TOP; norm_num) (by unfold ABUF TOP; norm_num)
    (by unfold ABUF TOP; norm_num) (Or.inr (Or.inr (by unfold ABUF ACC; norm_num)))
    (Or.inr (by unfold ABUF ACC; norm_num)) (by norm_num) (by norm_num)
  have gL2 : Reach (callState s 3681 [flag w] m4) (callState s 18541 [wd FL, wd (FL + 352 * 1), wd 128,
      wd ((FL + 224 * 3 + 2 ^ 256 - FL) % 2 ^ 256), wd 0xffffffffffffffff0000000000000000,
      wd ((BASES + 224 * 3 + 2 ^ 256 - FL) % 2 ^ 256), wd 3720, flag w] m4) 33 := by
    glam44_rreach [1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294] with [FL, BASES]
  obtain ⟨m5, h5, hf5, hc5⟩ := lmerge_call hs (ret := 3720) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := BASES + 224 * 3) (a := FL) (b := FL + 224 * 3) (ma := 0xffffffffffffffff0000000000000000)
    (sl := 128) (k := 1) (by norm_num) (by unfold BASES TOP; norm_num) (by unfold FL TOP; norm_num)
    (by unfold FL TOP; norm_num) (Or.inr (Or.inr (by unfold FL BASES; norm_num)))
    (Or.inr (by unfold FL BASES; norm_num)) (by norm_num) (by norm_num)
  have hmerge : Merged m5 s.executionEnv.calldata :=
    winD_merge (m := m3) (m1 := m4) hB3 h4 h5 hf5
      (fun a h1 h2 => word_frame hf4 (lo := FL) (hi := FL + 1120) (by avoids_tac) h1 h2)
  refine ⟨m5, KS4.frame (KS4.frame hks3 hf4 (by avoids_tac)) hf5 (by avoids_tac),
    (hB3.frame hf4 (by avoids_tac) (by avoids_tac)).frame hf5 (by avoids_tac) (by avoids_tac), hmerge,
    (hrc3.frame hf4 (by avoids_tac)).frame hf5 (by avoids_tac), ?_, ?_⟩
  · have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hf2) hf3) hf4) hf5
    exact hf.mono (by decide)
  · have hR := ((((((hR1.trans hR2).trans hR3).trans gL1).trans hc4).trans gL2).trans hc5)
    refine hR.mono (le_of_eq ?_)
    generalize Gas.kmove = a; generalize Gas.kf4 = d; generalize Gas.blk = e; generalize Gas.blkh = f
    generalize Gas.lmerge 8 = g; generalize Gas.lmerge 1 = h
    omega

end MlDsaOptGlam44.Proofs.Ex
