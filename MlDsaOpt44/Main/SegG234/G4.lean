import MlDsaOpt44.Main.SegG234.Round
import MlDsaOpt44.Fn.Group
set_option warningAsError true
/-!
# Group 4 of `seg_g234` (`4436 … 4648`)

Slot 0 squeezes `H(c̃)` (two blocks into `CB`), slot 1 the short-message μ
(`mu0`, into `MU`), slots 2 and 3 `A[3][3]`, `A[3][2]`. Then `gfix 12` and the
Kronecker accumulation `pass3k4` (lane 3 of `ACC`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- μ's input `tr ‖ 0 ‖ 0 ‖ M`. -/
def muMsg (cd : ByteArray) : ByteArray := trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)

/-- Slot 1: μ's seed state for short messages. -/
def muSlot (cd : ByteArray) : Fips202.SpongeState :=
  if mlenOf cd ≤ 69 then seedState 136 (muMsg cd) else Fips202.emptyState

/-- Group 4's slots after `ginit`. -/
def I4g (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedState 136 (ctOf cd) else if k = 1 then Fips202.emptyState
  else if k = 2 then seedState 168 (aSeed cd 3 3) else seedState 168 (aSeed cd 3 2)

/-- Group 4's slots after `mu0`. -/
def I4 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := if k = 1 then muSlot cd else I4g cd k

def X4 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := permN b (I4 cd k)

theorem I4_sized (cd : ByteArray) : Sized4 (I4 cd) := fun k _ => by
  unfold I4 I4g muSlot
  by_cases h1 : k = 1
  · rw [if_pos h1]
    by_cases hm : mlenOf cd ≤ 69
    · rw [if_pos hm]; exact seedState_size _ _
    · rw [if_neg hm]; exact emptyState_size
  · rw [if_neg h1]
    by_cases h0 : k = 0
    · rw [if_pos h0]; exact seedState_size _ _
    · rw [if_neg h0, if_neg h1]
      by_cases h2 : k = 2
      · rw [if_pos h2]; exact seedState_size _ _
      · rw [if_neg h2]; exact seedState_size _ _

theorem X4_sized (cd : ByteArray) (b : Nat) : Sized4 (X4 cd b) := fun k hk =>
  permN_size (I4_sized cd k hk) b

/-- Group 4's cost: glue 338 and its calls. -/
def costG4 : Nat :=
  338 + Gas.ginit + Gas.mu0 + 5 * (Gas.kf4 + Gas.blk) + 2 * Gas.cext 17 + Gas.cext 8 + Gas.gfix 2 +
    Gas.pass3k4

/-- `w &&& (2^n − 2^k)` keeps the bits from `k` on. -/
theorem and_high {w n k : Nat} (hw : w < 2 ^ n) (hk : k ≤ n) :
    w &&& (2 ^ n - 2 ^ k) = 2 ^ k * (w / 2 ^ k) := by
  have e : 2 ^ n - 2 ^ k = 2 ^ k * (2 ^ (n - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : j ≥ k
  · rw [show j - k + k = j by omega]
    by_cases hjn : j < n
    · simp [hj, show j - k < n - k by omega]
    · have : w.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this]
  · simp [hj]

/-- The Kronecker word: lane 3 of the masked product. -/
theorem kron_eq {w z : Nat} (hw : w < 2 ^ 256) (hz : z < 2 ^ 256) (ha2 : lane w 2 < 2 ^ 23)
    (ha3 : lane w 3 < 2 ^ 23) (hz2 : lane z 2 < 2 ^ 28) (hz3 : lane z 3 < 2 ^ 28) :
    (w &&& (2 ^ 256 - 2 ^ 128)) * (z / 2 ^ 128) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      2 ^ 192 * (lane w 2 * lane z 3 + lane w 3 * lane z 2) := by
  have hw' : w / 2 ^ 128 = lane w 2 + 2 ^ 64 * lane w 3 := by
    unfold lane; norm_num at hw ⊢; omega
  have hz' : z / 2 ^ 128 = lane z 2 + 2 ^ 64 * lane z 3 := by
    unfold lane; norm_num at hz ⊢; omega
  rw [and_high hw (by norm_num), hw', hz']
  generalize lane w 2 = a2 at *
  generalize lane w 3 = a3 at *
  generalize lane z 2 = z2 at *
  generalize lane z 3 = z3 at *
  have hu : a2 * z2 < 2 ^ 51 := by
    calc a2 * z2 < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' ha2 hz2
      _ = 2 ^ 51 := by norm_num
  have hK : a2 * z3 + a3 * z2 < 2 ^ 52 := by
    have h1 : a2 * z3 < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' ha2 hz3
    have h2 : a3 * z2 < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' ha3 hz2
    norm_num at h1 h2 ⊢; omega
  have e : 2 ^ 128 * (a2 + 2 ^ 64 * a3) * (z2 + 2 ^ 64 * z3) =
      (2 ^ 128 * (a2 * z2) + 2 ^ 192 * (a2 * z3 + a3 * z2)) + 2 ^ 256 * (a3 * z3) := by ring
  rw [e, Nat.add_mul_mod_self_left]
  generalize a2 * z2 = u at *
  generalize a2 * z3 + a3 * z2 = K at *
  have hlt : 2 ^ 128 * u + 2 ^ 192 * K < 2 ^ 256 := by norm_num at hu hK ⊢; omega
  rw [Nat.mod_eq_of_lt hlt, show M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 by unfold M64; norm_num,
    and_high hlt (by norm_num)]
  congr 1
  norm_num at hu hK ⊢
  omega

theorem aD_lt_of {cd : ByteArray} {r s : Nat} (h : (aOf cd r s).isSome = true) {t : Nat} (ht : t < 256) :
    ((aD cd r s)[t]!).toNat < Fips204.q := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  obtain ⟨-, hrange⟩ := rejNTTPoly_range _ a ha
  have := hrange t ht
  omega

theorem g4_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(12 : Nat).testBit sl || (aI (I4 cd sl)).isSome) =
      ((aOf cd 3 3).isSome && (aOf cd 3 2).isSome) := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (12 : Nat).testBit 0 = false by decide, show (12 : Nat).testBit 1 = false by decide,
    show (12 : Nat).testBit 2 = true by decide, show (12 : Nat).testBit 3 = true by decide,
    Bool.not_false, Bool.true_or, Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_true]
  unfold I4 I4g
  simp only [show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 0 by decide,
    show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 2 by decide, if_false, if_true]
  rw [aI_seedState (by rw [aSeed_size hcd]; norm_num), aI_seedState (by rw [aSeed_size hcd]; norm_num)]
  rfl

theorem seg_g4 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrc : RC4Table m) (hrho : Rho1At m s.executionEnv.calldata)
    (htrl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x))
    (hz : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k < 2 ^ 28) (b : Bool) :
    ∃ m', (∀ x, x < 34 → word m' (CB + 32 * x) = le64 (cStream s.executionEnv.calldata) (8 * x)) ∧
      (mlenOf s.executionEnv.calldata ≤ 69 → ∀ x, x < 8 →
        word m' (MU + 32 * x) = le64 (muOf s.executionEnv.calldata) (8 * x)) ∧
      (((aOf s.executionEnv.calldata 3 3).isSome && (aOf s.executionEnv.calldata 3 2).isSome) = true →
        ∀ t, t < 256 → word m' (ACC + 32 * t) = (word m (ACC + 32 * t) + 2 ^ 192 *
          (((aD s.executionEnv.calldata 3 3)[t]!).toNat * lane (word m (ZH + 32 * t)) 3 +
            ((aD s.executionEnv.calldata 3 2)[t]!).toNat * lane (word m (ZH + 32 * t)) 2)) % 2 ^ 256) ∧
      FrameExcept m m' (groupFrame ++ [(CB, CB + 1088), (MU, MU + 256)]) ∧
      Reach (callState s 4436 [flag b] m)
        (callState s 4648 [flag (b && ((aOf s.executionEnv.calldata 3 3).isSome &&
          (aOf s.executionEnv.calldata 3 2).isSome))] m') costG4 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd' : 1344 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  -- ginit
  have g0 : Reach (callState s 4436 [flag b] m)
      (callState s 11084 [wd 0x0ccccc000000cc000111d5, wd 1, wd 12, wd 0, wd 4466, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 34 := by
    opt44_reach [1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 4466) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 12) (cmult := 1) (l4 := 0x0ccccc000000cc000111d5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := hrho.frame hf0 (by avoids_tac)
  have hks1 : KS4 m1 (I4g s.executionEnv.calldata) :=
    ks4_ginit (kmask := 0)
      (L := fun k => if k = 0 then 31 else if k = 1 then 0 else if k = 2 then 3 + 256 * 3 + 0x1F0000
        else 2 + 256 * 3 + 0x1F0000)
      (ρ := fun x => le64 s.executionEnv.calldata (8 * x))
      (c := fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) (S := I4g s.executionEnv.calldata)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split_ifs <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        unfold I4g
        interval_cases k
        · simp only [if_true]
          exact freshLane_ctSeed hcd' (fun _ _ => rfl) (by decide) (by decide) (by simp) hx
        · simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
          exact freshLane_zero (by decide) (by decide) (by simp) x
        · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true]
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide) (by decide)
            (by simp) hx
        · simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
            show (3 : Nat) ≠ 2 by decide, if_false]
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide) (by decide)
            (by simp) hx)
      hg
  -- mu0
  have gM : Reach (callState s 4466 [flag b] m1) (callState s 12607 [wd 1, wd 4476, flag b] m1) 18 := by
    opt44_reach [1424, 1425, 1426, 1427, 1428]
  obtain ⟨m2, hmu, hmu', hf2, hc2⟩ := mu0_call hs (ret := 4476) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1 (sh := 1)
    (by norm_num) hcd
  have hks2 : KS4 m2 (X4 s.executionEnv.calldata 0) := by
    by_cases hm : mlenOf s.executionEnv.calldata ≤ 69
    · have htrl1 : ∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x) :=
        fun x hx => by
          rw [word_frame (FrameExcept.trans hf0 hf1) (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256)
            (by frame_tac) (by omega) (by omega)]
          exact htrl x hx
      have hw := hmu hm _ (trOf_size _) htrl1
      have hk := ks4_xor_slot (sh := 1) (by norm_num) hks1
        (fun x => if x < 17 then le64 (muBlock (trOf s.executionEnv.calldata) s.executionEnv.calldata) (8 * x)
          else 0)
        (fun x _ => by split; exact le64_lt _ _; norm_num)
        (fun x hx => by
          rw [hw x hx]
          split
          · rfl
          · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
        (seedState 136 (muMsg s.executionEnv.calldata))
        (fun x _ => by
          rw [show I4g s.executionEnv.calldata 1 = Fips202.emptyState from rfl, laneOf_emptyState,
            Nat.zero_xor]
          exact laneOf_muSeed _ _)
      refine hk.congr fun k _ => ?_
      unfold X4 I4 muSlot
      by_cases h1 : k = 1
      · subst h1; simp [hm]; rfl
      · simp [h1]; rfl
    · rw [hmu' (by omega)]
      refine hks1.congr fun k _ => ?_
      unfold X4 I4 muSlot
      by_cases h1 : k = 1
      · subst h1; simp [hm]; rfl
      · simp [h1]; rfl
  have hrc2 := ((hrc.frame hf0 (by avoids_tac)).frame hf1 (by avoids_tac)).frame hf2 (by avoids_tac)
  -- squeeze 0, H(c̃) block 0 into CB, μ into MU
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m2) (pc0 := 4476) (r1 := 4484) (r2 := 4498) (c1 := 15) (c2 := 21) (b := 0) (by norm_num)
    (by opt44_reach [1429, 1430, 1431, 1432]) (fun _ => by opt44_reach [1433, 1434, 1435, 1436, 1437, 1438] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X4_sized _ 0) hks2 (Blocks.zero _ _) (St := fun b k => permN (b + 1) (I4 s.executionEnv.calldata k))
    (fun k _ => permN_succ _ _)
  have hks3 : KS4 m3 (X4 s.executionEnv.calldata 1) := hks3'.congr fun k _ => (permN_succ _ _).symm
  have gC1 : Reach (callState s 4498 [flag b] m3) (callState s 12118 [wd 17, wd 0, wd CB, wd 4512, flag b] m3)
      23 := by
    opt44_reach [1439, 1440, 1441, 1442, 1443, 1444, 1445] with [CB]
  obtain ⟨m4, hcb1, hf4, hc4⟩ := cext_call hs (ret := 4512) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 0) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have gC2 : Reach (callState s 4512 [flag b] m4) (callState s 12118 [wd 8, wd 1, wd MU, wd 4527, flag b] m4)
      24 := by
    opt44_reach [1446, 1447, 1448, 1449, 1450, 1451, 1452] with [MU]
  obtain ⟨m5, hmuw, hf5, hc5⟩ := cext_call hs (ret := 4527) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := MU) (sh := 1) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  have hks5 := (hks3.frame hf4 (by avoids_tac)).frame hf5 (by avoids_tac)
  have hB5 := (hB3.frame hf4 (by frame_tac) (by frame_tac)).frame hf5 (by frame_tac) (by frame_tac)
  have hrc5 := (hrc3.frame hf4 (by avoids_tac)).frame hf5 (by avoids_tac)
  -- squeeze 1, H(c̃) block 1 into CB + 544
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m5) (pc0 := 4527) (r1 := 4535) (r2 := 4549) (c1 := 15) (c2 := 21) (b := 1) (by norm_num)
    (by opt44_reach [1453, 1454, 1455, 1456]) (fun _ => by opt44_reach [1457, 1458, 1459, 1460, 1461, 1462] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X4_sized _ 1) hks5 hB5 (St := fun b k => permN (b + 1) (I4 s.executionEnv.calldata k))
    (fun k _ => permN_succ _ _)
  have hks6 : KS4 m6 (X4 s.executionEnv.calldata 2) := hks6'.congr fun k _ => (permN_succ _ _).symm
  have gC3 : Reach (callState s 4549 [flag b] m6)
      (callState s 12118 [wd 17, wd 0, wd (CB + 544), wd 4563, flag b] m6) 23 := by
    opt44_reach [1463, 1464, 1465, 1466, 1467, 1468, 1469] with [CB]
  obtain ⟨m7, hcb2, hf7, hc7⟩ := cext_call hs (ret := 4563) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := CB + 544) (sh := 0) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hks7 := hks6.frame hf7 (by avoids_tac)
  have hB7 := hB6.frame hf7 (by frame_tac) (by frame_tac)
  have hrc7 := hrc6.frame hf7 (by avoids_tac)
  -- squeezes 2, 3, 4
  obtain ⟨m8, hks8', hB8, hrc8, hf8, hR8⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m7) (pc0 := 4563) (r1 := 4571) (r2 := 4585) (c1 := 15) (c2 := 21) (b := 2) (by norm_num)
    (by opt44_reach [1470, 1471, 1472, 1473]) (fun _ => by opt44_reach [1474, 1475, 1476, 1477, 1478, 1479] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc7 (X4_sized _ 2) hks7 hB7 (St := fun b k => permN (b + 1) (I4 s.executionEnv.calldata k))
    (fun k _ => permN_succ _ _)
  have hks8 : KS4 m8 (X4 s.executionEnv.calldata 3) := hks8'.congr fun k _ => (permN_succ _ _).symm
  obtain ⟨m9, hks9', hB9, hrc9, hf9, hR9⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m8) (pc0 := 4585) (r1 := 4593) (r2 := 4607) (c1 := 15) (c2 := 21) (b := 3) (by norm_num)
    (by opt44_reach [1480, 1481, 1482, 1483]) (fun _ => by opt44_reach [1484, 1485, 1486, 1487, 1488, 1489] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc8 (X4_sized _ 3) hks8 hB8 (St := fun b k => permN (b + 1) (I4 s.executionEnv.calldata k))
    (fun k _ => permN_succ _ _)
  have hks9 : KS4 m9 (X4 s.executionEnv.calldata 4) := hks9'.congr fun k _ => (permN_succ _ _).symm
  obtain ⟨m10, hks10', hB10, hrc10, hf10, hR10⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m9) (pc0 := 4607) (r1 := 4615) (r2 := 4629) (c1 := 15) (c2 := 21) (b := 4) (by norm_num)
    (by opt44_reach [1490, 1491, 1492, 1493]) (fun _ => by opt44_reach [1494, 1495, 1496, 1497, 1498, 1499] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc9 (X4_sized _ 4) hks9 hB9 (St := fun b k => permN (b + 1) (I4 s.executionEnv.calldata k))
    (fun k _ => permN_succ _ _)
  have hks10 : KS4 m10 (X4 s.executionEnv.calldata 5) := hks10'.congr fun k _ => (permN_succ _ _).symm
  -- gfix 12
  have hfB := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hf2) hf3) hf4) hf5)
    hf6) hf7) hf8) hf9
  have hfB' := FrameExcept.trans hfB hf10
  have h610 : word m10 HAVE6 = 0 := by
    rw [word_frame hfB' (lo := HAVE6) (hi := HAVE6 + 32) (by frame_tac) le_rfl le_rfl]; exact h60
  have gG : Reach (callState s 4629 [flag b] m10) (callState s 10754 [wd 12, wd 4639, flag b] m10) 18 := by
    opt44_reach [1500, 1501, 1502, 1503, 1504]
  obtain ⟨m11, hlanes, hks11, hf11, hc11⟩ := gfix_call hs (ret := 4639) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m10 hrc10
    (amask := 12) (by norm_num) 2 (by decide) (X4 s.executionEnv.calldata 5) (X4_sized _ 5) hks10
    (I4 s.executionEnv.calldata) h610
    (fun sl hsl _ => hB10.pending hsl (fun _ _ => rfl) h610 rfl)
  rw [g4_flag hcd32] at hc11
  -- pass3k4
  have gK : Reach (callState s 4639 [flag ((aOf s.executionEnv.calldata 3 3).isSome &&
        (aOf s.executionEnv.calldata 3 2).isSome), flag b] m11)
      (callState s 10643 [wd 4648, flag (b && ((aOf s.executionEnv.calldata 3 3).isSome &&
        (aOf s.executionEnv.calldata 3 2).isSome))] m11) 18 := by
    opt44_reach [1505, 1506, 1507, 1508, 1509] with [flag, ite01_land]
  obtain ⟨m12, hacc, hf12, hc12⟩ := pass3k4_call hs (ret := 4648)
    (tail := [flag (b && ((aOf s.executionEnv.calldata 3 3).isSome &&
        (aOf s.executionEnv.calldata 3 2).isSome))])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m11
  have hfA := FrameExcept.trans (FrameExcept.trans hf0 hfB') hf11
  -- CB and MU survive the later calls
  have hcbw : ∀ x, x < 17 → word m4 (CB + 32 * x) = word m12 (CB + 32 * x) := fun x hx => by
    have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf5 hf6) hf7) hf8) hf9) hf10) hf11) hf12
    exact (word_frame hf (a := CB + 32 * x) (lo := CB) (hi := CB + 544) (by frame_tac) (by omega) (by omega)).symm
  have hcbw2 : ∀ x, x < 17 → word m7 (CB + 32 * (17 + x)) = word m12 (CB + 32 * (17 + x)) :=
    fun x hx => by
      have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf8 hf9) hf10)
        hf11) hf12
      exact (word_frame hf (a := CB + 32 * (17 + x)) (lo := CB) (hi := CB + 1088) (by frame_tac)
        (by omega) (by omega)).symm
  have hmuw' : ∀ x, x < 8 → word m5 (MU + 32 * x) = word m12 (MU + 32 * x) := fun x hx => by
    have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf6 hf7) hf8) hf9) hf10) hf11) hf12
    exact (word_frame hf (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by frame_tac) (by omega) (by omega)).symm
  refine ⟨m12, fun x hx => ?_, fun hm x hx => ?_, fun hok t ht => ?_,
    (FrameExcept.trans hfA hf12).mono (by unfold groupFrame; decide), ?_⟩
  · by_cases h17 : x < 17
    · rw [← hcbw x h17, hcb1 x h17, cext_lane hks3 (sh := 0) (x := x) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 0 + x) by omega, le64_cStream hcd' (by norm_num) h17]
      rfl
    · have hx' : x - 17 < 17 := by omega
      rw [show CB + 32 * x = CB + 32 * (17 + (x - 17)) by omega, ← hcbw2 _ hx',
        show CB + 32 * (17 + (x - 17)) = CB + 544 + 32 * (x - 17) by omega, hcb2 _ hx',
        cext_lane hks6 (sh := 0) (x := x - 17) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 1 + (x - 17)) by omega, le64_cStream hcd' (by norm_num) hx']
      rfl
  · rw [← hmuw' x hx, hmuw x hx, cext_lane (hks3.frame hf4 (by avoids_tac)) (sh := 1) (x := x) (by norm_num) (by omega), le64_muOf hm hx]
    unfold X4 I4 muSlot
    simp [hm]
    rfl
  · have hA := hfA
    have hzh : word m11 (ZH + 32 * t) = word m (ZH + 32 * t) :=
      word_frame hfA (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by frame_tac) (by omega) (by omega)
    have hac : word m11 (ACC + 32 * t) = word m (ACC + 32 * t) :=
      word_frame hfA (a := ACC + 32 * t) (lo := ACC) (hi := ACC + 8192) (by frame_tac) (by omega) (by omega)
    simp only [Bool.and_eq_true] at hok
    obtain ⟨a33, h33⟩ := Option.isSome_iff_exists.mp hok.1
    obtain ⟨a32, h32⟩ := Option.isSome_iff_exists.mp hok.2
    have hl2 : lane (word m11 (ABUF + 32 * t)) 2 = ((aD s.executionEnv.calldata 3 3)[t]!).toNat := by
      have := hlanes 2 (by norm_num) (by decide) a33
      have e : aI (I4 s.executionEnv.calldata 2) = aOf s.executionEnv.calldata 3 3 := by
        have hI : I4 s.executionEnv.calldata 2 = seedState 168 (aSeed s.executionEnv.calldata 3 3) := by
          unfold I4 I4g; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
        rw [hI]; exact aI_seedState (by rw [aSeed_size hcd32]; norm_num)
      rw [e] at this
      rw [this h33 t ht]; unfold aD; rw [h33]; rfl
    have hl3 : lane (word m11 (ABUF + 32 * t)) 3 = ((aD s.executionEnv.calldata 3 2)[t]!).toNat := by
      have := hlanes 3 (by norm_num) (by decide) a32
      have e : aI (I4 s.executionEnv.calldata 3) = aOf s.executionEnv.calldata 3 2 := by
        have hI : I4 s.executionEnv.calldata 3 = seedState 168 (aSeed s.executionEnv.calldata 3 2) := by
          unfold I4 I4g; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
        rw [hI]; exact aI_seedState (by rw [aSeed_size hcd32]; norm_num)
      rw [e] at this
      rw [this h32 t ht]; unfold aD; rw [h32]; rfl
    have hq : Fips204.q < 2 ^ 23 := by unfold Fips204.q; norm_num
    rw [hacc t ht, kronWord, kron_eq (word_lt _ _) (word_lt _ _)
        (by rw [hl2]; exact Nat.lt_trans (aD_lt_of hok.1 ht) hq)
        (by rw [hl3]; exact Nat.lt_trans (aD_lt_of hok.2 ht) hq)
        (by rw [hzh]; exact hz 2 (by norm_num) t ht) (by rw [hzh]; exact hz 3 (by norm_num) t ht),
      hl2, hl3, hzh, hac]
  · have hR := (((((((((((((g0.trans hc1).trans gM).trans hc2).trans hR3).trans gC1).trans hc4).trans
      gC2).trans hc5).trans hR6).trans gC3).trans hc7).trans hR8).trans hR9).trans hR10
    exact ((((hR.trans gG).trans hc11).trans gK).trans hc12).mono (by unfold costG4; omega)

end MlDsaOpt44.Proofs
