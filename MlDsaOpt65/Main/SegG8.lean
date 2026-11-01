import MlDsaOpt65.Main.S4.Round
import MlDsaOpt65.Fn.Pass3x
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-! # Segment `4972 … 5190`: mixed ExpandA group 8 (instance 9, the c̃ stream and the μ rider). -/

namespace MlDsaOpt65.Proofs

namespace S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- Slot 2: μ's seed state for short messages. -/
def muSlot (cd : ByteArray) : Fips202.SpongeState :=
  if mlenOf cd ≤ 69 then seedState 136 (muMsg cd) else Fips202.emptyState

/-- Group 8's slots after `ginit`: instance 9 (`A[5][4]`), c̃'s seed, two empty slots. -/
def I8g (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedI cd 9 else if k = 1 then seedState 136 (ctOf cd) else Fips202.emptyState

/-- Group 8's slots after `mu0`. -/
def I8 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := if k = 2 then muSlot cd else I8g cd k

def X8 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := permN b (I8 cd k)

theorem I8_zero (cd : ByteArray) : I8 cd 0 = seedI cd 9 := by
  unfold I8 I8g; rw [if_neg (by decide), if_pos rfl]

theorem I8_sized (cd : ByteArray) : Sized4 (I8 cd) := fun k _ => by
  unfold I8 I8g muSlot seedI seedA
  split_ifs <;> first | exact seedState_size _ _ | exact emptyState_size

theorem X8_sized (cd : ByteArray) (b : Nat) : Sized4 (X8 cd b) := fun k hk =>
  permN_size (I8_sized cd k hk) b

theorem g8_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (I8g s.executionEnv.calldata) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 4972 [flag b] m) (callState s 5002 [flag b] m1) (34 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have hcdZ : Z0 ≤ cd.size := by unfold HDR Z0 at *; omega
  have g0 : Reach (callState s 4972 [flag b] m)
      (callState s 12015 [wd 0x0111110000010100000100, wd 2, wd 1, wd 0, wd 5002, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 34 := by
    opt65_reach [1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 5002) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 1) (cmult := 2) (l4 := 0x0111110000010100000100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by s4_frame)
  have hks : KS4 m1 (I8g cd) :=
    ks4_ginit (kmask := 0)
      (L := fun k => if k = 0 then 4 + 256 * 5 + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := I8g cd)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        interval_cases k
        · show _ = laneOf (seedState 168 (aSeed cd 5 4)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 136 (ctOf cd)) x
          exact freshLane_ctSeed hcdZ (fun _ _ => rfl) (by decide) (by decide) (by norm_num) hx
        · show _ = laneOf Fips202.emptyState x
          exact freshLane_zero (by decide) (by decide) (by norm_num) x
        · show _ = laneOf Fips202.emptyState x
          exact freshLane_zero (by decide) (by decide) (by norm_num) x)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `mu0 [2]` on group 8's state: slot 2 becomes `muSlot`. -/
theorem ks4_mu0 {m1 m2 : ByteArray} {cd : ByteArray} (hks1 : KS4 m1 (I8g cd))
    (htrl : ∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 (trOf cd) (8 * x))
    (hmu : mlenOf cd ≤ 69 → ∀ tr : ByteArray, tr.size = 64 →
        (∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m2 (KS + 32 * x) =
          if x < 17 then word m1 (KS + 32 * x) ^^^
            spread (le64 (MlDsaOpt65.Proofs.muBlock tr cd) (8 * x)) * 2 ^ 2
          else word m1 (KS + 32 * x))
    (hmu' : 69 < mlenOf cd → m2 = m1) : KS4 m2 (X8 cd 0) := by
  by_cases hm : mlenOf cd ≤ 69
  · have hw := hmu hm _ (trOf_size _) htrl
    have hk := ks4_xor_slot (sh := 2) (by norm_num) hks1
      (fun x => if x < 17 then le64 (MlDsaOpt65.Proofs.muBlock (trOf cd) cd) (8 * x) else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (seedState 136 (muMsg cd))
      (fun x _ => by
        rw [show I8g cd 2 = Fips202.emptyState from rfl, laneOf_emptyState, Nat.zero_xor]
        exact laneOf_muSeed _)
    refine ks4_congr hk fun k _ => ?_
    unfold X8 I8 muSlot
    by_cases h2 : k = 2
    · subst h2; simp [hm]; rfl
    · simp [h2]; rfl
  · rw [hmu' (by omega)]
    refine ks4_congr hks1 fun k _ => ?_
    unfold X8 I8 muSlot
    by_cases h2 : k = 2
    · subst h2; simp [hm]; rfl
    · simp [h2]; rfl

set_option maxHeartbeats 1000000 in
theorem seg_g8_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv5 s.executionEnv.calldata m' ∧
      Reach (callState s 4972 [flag b] m)
        (callState s 5190 [flag (b && okI s.executionEnv.calldata 9)] m') Gas.pG8 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcdZ : Z0 ≤ s.executionEnv.calldata.size := by unfold HDR Z0 at *; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g8_ginit hs hcd hI.rho b
  -- mu0 [2]
  have gM : Reach (callState s 5002 [flag b] m1) (callState s 13565 [wd 2, wd 5012, flag b] m1) 18 := by
    opt65_reach [1628, 1629, 1630, 1631, 1632]
  obtain ⟨m2, hmu, hmu', hf2, hc2⟩ := mu0_call hs (ret := 5012) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1 (sh := 2)
    (by norm_num) hcd
  have hks2 : KS4 m2 (X8 s.executionEnv.calldata 0) :=
    ks4_mu0 hks1 (fun x hx => by
      rw [word_frame hf1 (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by s4_frame) (by omega)
        (by omega)]
      exact hI.trl x hx) hmu hmu'
  have hrc2 := rc4_frame (rc4_frame hI.rc4 hf1 (by s4_frame)) hf2 (by s4_frame)
  have h62 : word m2 HAVE6 = 0 := by
    rw [word_frame hf2 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  -- squeeze 0; H(c̃) block 0 into CB; μ into MU
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m2) (pc0 := 5012) (r1 := 5020) (r2 := 5034) (c1 := 15) (c2 := 21) (b := 0) (by norm_num)
    (by opt65_reach [1633, 1634, 1635, 1636])
    (fun _ => by opt65_reach [1637, 1638, 1639, 1640, 1641, 1642] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X8_sized _ 0) hks2 (Blocks.zero _ _)
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks3 : KS4 m3 (X8 s.executionEnv.calldata 1) := ks4_congr hks3' fun k _ => (permN_succ _ _).symm
  have gC1 : Reach (callState s 5034 [flag b] m3)
      (callState s 13076 [wd 17, wd 1, wd CB, wd 5050, flag b] m3) 24 := by
    opt65_reach [1643, 1644, 1645, 1646, 1647, 1648, 1649] with [CB]
  obtain ⟨m4, hcb1, hf4, hc4⟩ := cext_call hs (ret := 5050) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hks4 := ks4_frame hks3 hf4 (by s4_frame)
  have hB4 := hB3.frame hf4 (by s4_frame) (by s4_frame)
  have hrc4 := rc4_frame hrc3 hf4 (by s4_frame)
  have gC2 : Reach (callState s 5050 [flag b] m4)
      (callState s 13076 [wd 8, wd 2, wd MU, wd 5066, flag b] m4) 24 := by
    opt65_reach [1650, 1651, 1652, 1653, 1654, 1655, 1656] with [MU]
  obtain ⟨m5, hmuw, hf5, hc5⟩ := cext_call hs (ret := 5066) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (dst := MU) (sh := 2) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  have hks5 := ks4_frame hks4 hf5 (by s4_frame)
  have hB5 := hB4.frame hf5 (by s4_frame) (by s4_frame)
  have hrc5 := rc4_frame hrc4 hf5 (by s4_frame)
  -- squeeze 1; H(c̃) block 1 into CB + 544
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m5) (pc0 := 5066) (r1 := 5074) (r2 := 5088) (c1 := 15) (c2 := 21) (b := 1) (by norm_num)
    (by opt65_reach [1657, 1658, 1659, 1660])
    (fun _ => by opt65_reach [1661, 1662, 1663, 1664, 1665, 1666] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X8_sized _ 1) hks5 hB5
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks6 : KS4 m6 (X8 s.executionEnv.calldata 2) := ks4_congr hks6' fun k _ => (permN_succ _ _).symm
  have gC3 : Reach (callState s 5088 [flag b] m6)
      (callState s 13076 [wd 17, wd 1, wd (CB + 544), wd 5104, flag b] m6) 24 := by
    opt65_reach [1667, 1668, 1669, 1670, 1671, 1672, 1673] with [CB]
  obtain ⟨m7, hcb2, hf7, hc7⟩ := cext_call hs (ret := 5104) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := CB + 544) (sh := 1) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hks7 := ks4_frame hks6 hf7 (by s4_frame)
  have hB7 := hB6.frame hf7 (by s4_frame) (by s4_frame)
  have hrc7 := rc4_frame hrc6 hf7 (by s4_frame)
  -- squeezes 2, 3, 4
  obtain ⟨m8, hks8', hB8, hrc8, hf8, hR8⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m7) (pc0 := 5104) (r1 := 5112) (r2 := 5126) (c1 := 15) (c2 := 21) (b := 2) (by norm_num)
    (by opt65_reach [1674, 1675, 1676, 1677])
    (fun _ => by opt65_reach [1678, 1679, 1680, 1681, 1682, 1683] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc7 (X8_sized _ 2) hks7 hB7
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks8 : KS4 m8 (X8 s.executionEnv.calldata 3) := ks4_congr hks8' fun k _ => (permN_succ _ _).symm
  obtain ⟨m9, hks9', hB9, hrc9, hf9, hR9⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m8) (pc0 := 5126) (r1 := 5134) (r2 := 5148) (c1 := 15) (c2 := 21) (b := 3) (by norm_num)
    (by opt65_reach [1684, 1685, 1686, 1687])
    (fun _ => by opt65_reach [1688, 1689, 1690, 1691, 1692, 1693] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc8 (X8_sized _ 3) hks8 hB8
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks9 : KS4 m9 (X8 s.executionEnv.calldata 4) := ks4_congr hks9' fun k _ => (permN_succ _ _).symm
  obtain ⟨m10, hks10', hB10, hrc10, hf10, hR10⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m9) (pc0 := 5148) (r1 := 5156) (r2 := 5170) (c1 := 15) (c2 := 21) (b := 4) (by norm_num)
    (by opt65_reach [1694, 1695, 1696, 1697])
    (fun _ => by opt65_reach [1698, 1699, 1700, 1701, 1702, 1703] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc9 (X8_sized _ 4) hks9 hB9
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks10 : KS4 m10 (X8 s.executionEnv.calldata 5) :=
    ks4_congr hks10' fun k _ => (permN_succ _ _).symm
  -- gfix 1
  have hfB : FrameExcept m2 m10 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (CB, CB + 1088),
      (MU, MU + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans (FrameExcept.trans hf3 hf4) hf5) hf6) hf7) hf8) hf9) hf10).mono (by decide)
  have h610 : word m10 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h62
  have gG : Reach (callState s 5170 [flag b] m10) (callState s 11685 [wd 1, wd 5180, flag b] m10) 18 := by
    opt65_reach [1704, 1705, 1706, 1707, 1708]
  obtain ⟨m11, hlanes, -, -, hf11, hc11⟩ := gfix_call hs (ret := 5180) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m10 hrc10
    (amask := 1) (by norm_num) 1 (by decide) (X8 s.executionEnv.calldata 5) (X8_sized _ 5) hks10
    (I8 s.executionEnv.calldata) h610
    (fun sl hsl _ => hB10.pending hsl (fun _ _ => rfl) h610 rfl)
  have hflag : ((List.range 4).all fun sl => !(1 : Nat).testBit sl ||
      (MlDsaOpt65.Proofs.aI (I8 s.executionEnv.calldata sl)).isSome) = okI s.executionEnv.calldata 9 := by
    simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
      show (1 : Nat).testBit 0 = true by decide, show (1 : Nat).testBit 1 = false by decide,
      show (1 : Nat).testBit 2 = false by decide, show (1 : Nat).testBit 3 = false by decide,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true]
    rw [I8_zero]; exact okI_eq hcd32 9
  rw [hflag] at hc11
  -- AND, pass3x8 (instance 9 into lane 1 of ACC + 0x2000)
  have gP : Reach (callState s 5180 [flag (okI s.executionEnv.calldata 9), flag b] m11)
      (callState s 11622 [wd 5189, flag (b && okI s.executionEnv.calldata 9)] m11) 18 := by
    opt65_reach [1709, 1710, 1711, 1712, 1713] with [flag, ite01_land]
  obtain ⟨m12, hacc, hf12, hc12⟩ := pass3x8_call hs (ret := 5189)
    (tail := [flag (b && okI s.executionEnv.calldata 9)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m11
  have gE : Reach (callState s 5189 [flag (b && okI s.executionEnv.calldata 9)] m12)
      (callState s 5190 [flag (b && okI s.executionEnv.calldata 9)] m12) 1 := by
    opt65_reach [1714]
  -- frames
  have hf11' : FrameExcept m m11 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800), (CB, CB + 1088), (MU, MU + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hf2) hfB) hf11).mono (by decide)
  have hfA : FrameExcept m m12 (gbase ++ [(CB, CB + 1088), (MU, MU + 256)]) :=
    (FrameExcept.trans hf11' hf12).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m12 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hwA : ∀ t, t < 256 → word m11 (ACC + 0x2000 + 32 * t) = word m (ACC + 0x2000 + 32 * t) :=
    fun t ht => word_frame hf11' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000) (by s4_frame)
      (Nat.le_add_right _ _) (by omega)
  have hwZ2 : ∀ t, t < 256 → word m11 (ZH + 0x2000 + 32 * t) = word m (ZH + 0x2000 + 32 * t) :=
    fun t ht => word_frame hf11' (a := ZH + 0x2000 + 32 * t) (lo := ZH) (hi := ZH + 0x4000) (by s4_frame) (by omega) (by omega)
  -- ACC + 0x2000
  have hacc1 : AccInst1 m12 s.executionEnv.calldata 10 :=
    accInst1_step (n := 9) (n' := 10) (by norm_num) (by norm_num) hI.acc1 hI.zhat hzh
      (D0 := fun _ => 0)
      (D1 := fun t => ((aD s.executionEnv.calldata 5 4)[t]!).toNat * zhLane m 4 t)
      (fun _ t _ => ⟨Nat.add_zero _, (accSum_succ _ _ 5 t 4).symm⟩)
      (fun hok t ht => by
        have l0 := gfix_lane (I := I8 s.executionEnv.calldata) (amask := 1) (sl := 0) (i := 9) hcd32
          (by norm_num) (by decide) (I8_zero _) hlanes
          (okIUpTo_get hok 9 (by norm_num)) ht
        simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at l0
        rw [hacc t ht, p8_eq, l0, hwA t ht, hwZ2 t ht, ← zhLane_four])
  -- the outputs
  have hzhat : ZHatAt m12 s.executionEnv.calldata :=
    ZHatAt.frame hI.zhat hfA (by unfold gbase; s4_frame)
  have hacc0 : AccCols0 m12 s.executionEnv.calldata 5 :=
    accCols0_frame hI.acc0 (fun t ht => word_frame hfA (lo := ACC) (hi := ACC + 0x2000)
      (by unfold gbase; s4_frame) (by omega) (by omega)) hzh
  have hmu12 : MuAt m12 s.executionEnv.calldata := by
    intro hm x hx
    have hf : FrameExcept m5 m12 (gbase ++ [(CB, CB + 1088)]) :=
      (((((((hf6.trans hf7).trans hf8).trans hf9).trans hf10).trans hf11).trans hf12).mono
        (by unfold gbase; decide))
    rw [word_frame hf (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by unfold gbase; s4_frame) (by omega)
        (by omega), hmuw x hx, cext_lane hks4 (sh := 2) (x := x) (by norm_num) (by omega),
      le64_muOf hm hx]
    unfold X8 I8 muSlot
    simp only [if_true, if_pos hm]
  have hcbw : ∀ x, x < 17 → word m12 (CB + 32 * x) = word m4 (CB + 32 * x) := fun x hx => by
    have hf : FrameExcept m4 m12 (gbase ++ [(CB + 544, CB + 1088), (MU, MU + 256)]) :=
      ((((((((hf5.trans hf6).trans hf7).trans hf8).trans hf9).trans hf10).trans hf11).trans hf12).mono
        (by unfold gbase; decide))
    exact word_frame hf (a := CB + 32 * x) (lo := CB) (hi := CB + 544) (by unfold gbase; s4_frame)
      (by omega) (by omega)
  have hcbw2 : ∀ x, x < 17 → word m12 (CB + 544 + 32 * x) = word m7 (CB + 544 + 32 * x) := fun x hx => by
    have hf : FrameExcept m7 m12 gbase :=
      (((((hf8.trans hf9).trans hf10).trans hf11).trans hf12).mono (by unfold gbase; decide))
    exact word_frame hf (a := CB + 544 + 32 * x) (lo := CB + 544) (hi := CB + 1088)
      (by unfold gbase; s4_frame) (Nat.le_add_right _ _) (by omega)
  have hcb : CbAt m12 s.executionEnv.calldata := by
    intro x hx
    by_cases h17 : x < 17
    · rw [hcbw x h17, hcb1 x h17, cext_lane hks3 (sh := 1) (x := x) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 0 + x) by omega, le64_cStream hcdZ (by norm_num) h17]
      rfl
    · have hx' : x - 17 < 17 := by omega
      rw [show CB + 32 * x = CB + 544 + 32 * (x - 17) by omega, hcbw2 _ hx', hcb2 _ hx',
        cext_lane hks6 (sh := 1) (x := x - 17) (by norm_num) (by omega),
        show 8 * x = 8 * (17 * 1 + (x - 17)) by omega, le64_cStream hcdZ (by norm_num) hx']
      rfl
  refine ⟨m12, ⟨RC1Table.frame hI.rc1 hfA (by unfold gbase; s4_frame),
    TblAt.frame hI.tbl hfA (by unfold gbase; s4_frame), HPAt.frame hI.hp hfA (by unfold gbase; s4_frame),
    s3_accAt hzhat hacc0 (s3_accCols1_of_inst hacc1),
    TrlAt.frame hI.trl hfA (by unfold gbase; s4_frame), hmu12, hcb,
    ⟨ZeroOn.frame (ZeroOn.mono hI.zCw (le_refl _) (by unfold CW ABUF; omega)) hfA
        (by unfold gbase; s4_frame),
      ZeroOn.frame (ZeroOn.mono hI.zIdx (le_refl _) (by unfold IDX ACC; omega)) hfA
        (by unfold gbase; s4_frame),
      ZeroOn.frame (ZeroOn.mono hI.zMisc (by unfold NNEG MISC; omega) (by unfold NNEG MISC; omega))
        hfA (by unfold gbase; s4_frame)⟩⟩, ?_⟩
  have hR := (((((((((((((((((hR1.trans gM).trans hc2).trans hR3).trans gC1).trans hc4).trans gC2).trans
    hc5).trans hR6).trans gC3).trans hc7).trans hR8).trans hR9).trans hR10).trans gG).trans hc11).trans
    gP).trans hc12).trans gE
  exact hR.mono (by unfold Gas.pG8; omega)

end S4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- Group 8: `ginit [0, 1, 2, L4]` (slot 0: `A[5][4]`; slot 1: c̃, `cmult 2`; slot 2: μ),
`mu0 [2]` (absorbs `tr ‖ 0 ‖ 0 ‖ M` from `TRL` for `|M| ≤ 69`), five rounds `kf4` + `blk`, `cext
[CB + 544 b, 1, 17]` after rounds 0 and 1 (the SampleInBall stream `H(c̃)`), `cext [MU, 2, 8]`
after round 0 (μ), `gfix [1]`, `AND`, `pass3x8` (`((X & L0) << 64) · ẑ_4`), the return
`JUMPDEST`. Establishes `Inv5` (`AccAt` from `AccCols0 5` and `AccInst1 10`, see
`S3/Lemmas.lean`: `s3_accCols1_of_inst`, `s3_accAt`; `SibFresh` from the zero facts).
Proof: `S4.seg_g8_proof`. -/
theorem seg_g8 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv5 s.executionEnv.calldata m' ∧
      Reach (callState s 4972 [flag b] m)
        (callState s 5190 [flag (b && okI s.executionEnv.calldata 9)] m') Gas.pG8 :=
  S4.seg_g8_proof hs hcd hI b

end MlDsaOpt65.Proofs
