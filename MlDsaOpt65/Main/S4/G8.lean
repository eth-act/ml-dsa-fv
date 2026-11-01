import MlDsaOpt65.Main.S4.Round
set_option warningAsError true
/-!
# Group 8 (`5029 … 5221`, ML-DSA-65, WP S4)

Slots 0, 1 squeeze `A[4][3]`, `A[5][3]` (slot 2 repeats `A[4][3]`, inactive);
slot 3 is μ's single block for short messages (`mu0`, the first squeeze into
`MU`). Then `gfix 3` and `pass3 [192, ZH, ACC + 0x2000]`.
-/

namespace MlDsaOpt65.Proofs.S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- Slot 3: μ's seed state for short messages. -/
def muSlot (cd : ByteArray) : Fips202.SpongeState :=
  if mlenOf cd ≤ 69 then seedState 136 (muMsg cd) else Fips202.emptyState

/-- Group 8's slots after `ginit`. -/
def I8g (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedA cd 4 3 else if k = 1 then seedA cd 5 3 else if k = 2 then seedA cd 4 3
  else Fips202.emptyState

/-- Group 8's slots after `mu0`. -/
def I8 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := if k = 3 then muSlot cd else I8g cd k

def X8 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := permN b (I8 cd k)

theorem I8_sized (cd : ByteArray) : Sized4 (I8 cd) := fun k _ => by
  unfold I8 I8g muSlot seedA
  split_ifs <;> first | exact seedState_size _ _ | exact emptyState_size

theorem X8_sized (cd : ByteArray) (b : Nat) : Sized4 (X8 cd b) := fun k hk =>
  permN_size (I8_sized cd k hk) b

theorem g8_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (I8g s.executionEnv.calldata) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 5029 [flag b] m) (callState s 5057 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have g0 : Reach (callState s 5029 [flag b] m)
      (callState s 11644 [wd 0x0777770000070200000077, wd 0, wd 7, wd 0, wd 5057, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    opt65_reach [1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 5057) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 7) (cmult := 0) (l4 := 0x0777770000070200000077)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by s4_frame)
  have hks : KS4 m1 (I8g cd) :=
    ks4_ginit (kmask := 0)
      (L := fun k => if k < 3 then 3 + 256 * (if k = 1 then 5 else 4) + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := I8g cd)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split_ifs <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        interval_cases k
        · show _ = laneOf (seedState 168 (aSeed cd 4 3)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 168 (aSeed cd 5 3)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 168 (aSeed cd 4 3)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf Fips202.emptyState x
          exact freshLane_zero (by decide) (by decide) (by norm_num) x)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `mu0` on group 8's state: slot 3 becomes `muSlot`. -/
theorem ks4_mu0 {m1 m2 : ByteArray} {cd : ByteArray} (hks1 : KS4 m1 (I8g cd))
    (htrl : ∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 (trOf cd) (8 * x))
    (hmu : mlenOf cd ≤ 69 → ∀ tr : ByteArray, tr.size = 64 →
        (∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m2 (KS + 32 * x) =
          if x < 17 then word m1 (KS + 32 * x) ^^^
            spread (le64 (MlDsaOpt65.Proofs.muBlock tr cd) (8 * x)) * 2 ^ 3
          else word m1 (KS + 32 * x))
    (hmu' : 69 < mlenOf cd → m2 = m1) : KS4 m2 (X8 cd 0) := by
  by_cases hm : mlenOf cd ≤ 69
  · have hw := hmu hm _ (trOf_size _) htrl
    have hk := ks4_xor_slot (sh := 3) (by norm_num) hks1
      (fun x => if x < 17 then le64 (MlDsaOpt65.Proofs.muBlock (trOf cd) cd) (8 * x) else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (seedState 136 (muMsg cd))
      (fun x _ => by
        rw [show I8g cd 3 = Fips202.emptyState from rfl, laneOf_emptyState, Nat.zero_xor]
        exact laneOf_muSeed _)
    refine ks4_congr hk fun k _ => ?_
    unfold X8 I8 muSlot
    by_cases h3 : k = 3
    · subst h3; simp [hm]; rfl
    · simp [h3]; rfl
  · rw [hmu' (by omega)]
    refine ks4_congr hks1 fun k _ => ?_
    unfold X8 I8 muSlot
    by_cases h3 : k = 3
    · subst h3; simp [hm]; rfl
    · simp [h3]; rfl

set_option maxHeartbeats 1000000 in
theorem seg_g8_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvMu s.executionEnv.calldata m' ∧
      Reach (callState s 5029 [flag b] m)
        (callState s 5221 [flag (b && okCol1 s.executionEnv.calldata 3)] m') Gas.pG8 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g8_ginit hs hcd hI.rho b
  -- mu0
  have gM : Reach (callState s 5057 [flag b] m1) (callState s 13194 [wd 3, wd 5067, flag b] m1) 18 := by
    opt65_reach [1651, 1652, 1653, 1654, 1655]
  obtain ⟨m2, hmu, hmu', hf2, hc2⟩ := mu0_call hs (ret := 5067) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1 (sh := 3)
    (by norm_num) hcd
  have hks2 : KS4 m2 (X8 s.executionEnv.calldata 0) :=
    ks4_mu0 hks1 (fun x hx => by
      rw [word_frame hf1 (a := TRL + 32 * x) (lo := TRL) (hi := TRL + 256) (by s4_frame) (by omega)
        (by omega)]
      exact hI.trl x hx) hmu hmu'
  have hrc2 := rc4_frame (rc4_frame hI.rc4 hf1 (by s4_frame)) hf2 (by s4_frame)
  have h62 : word m2 HAVE6 = 0 := by
    rw [word_frame hf2 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h61
  -- squeeze 0, μ into MU
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m2) (pc0 := 5067) (r1 := 5075) (r2 := 5089) (c1 := 15) (c2 := 21) (b := 0) (by norm_num)
    (by opt65_reach [1656, 1657, 1658, 1659])
    (fun _ => by opt65_reach [1660, 1661, 1662, 1663, 1664, 1665] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X8_sized _ 0) hks2 (Blocks.zero _ _)
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks3 : KS4 m3 (X8 s.executionEnv.calldata 1) := ks4_congr hks3' fun k _ => (permN_succ _ _).symm
  have gC : Reach (callState s 5089 [flag b] m3) (callState s 12705 [wd 8, wd 3, wd MU, wd 5105, flag b] m3)
      24 := by
    opt65_reach [1666, 1667, 1668, 1669, 1670, 1671, 1672] with [MU]
  obtain ⟨m4, hmuw, hf4, hc4⟩ := cext_call hs (ret := 5105) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := MU) (sh := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by unfold KS MU; norm_num)
    (by unfold MU TOP; norm_num)
  have hks4 := ks4_frame hks3 hf4 (by s4_frame)
  have hB4 := hB3.frame hf4 (by s4_frame) (by s4_frame)
  have hrc4 := rc4_frame hrc3 hf4 (by s4_frame)
  -- squeezes 1 … 4
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m4) (pc0 := 5105) (r1 := 5113) (r2 := 5127) (c1 := 15) (c2 := 21) (b := 1) (by norm_num)
    (by opt65_reach [1673, 1674, 1675, 1676])
    (fun _ => by opt65_reach [1677, 1678, 1679, 1680, 1681, 1682] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (X8_sized _ 1) hks4 hB4
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks5 : KS4 m5 (X8 s.executionEnv.calldata 2) := ks4_congr hks5' fun k _ => (permN_succ _ _).symm
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m5) (pc0 := 5127) (r1 := 5135) (r2 := 5149) (c1 := 15) (c2 := 21) (b := 2) (by norm_num)
    (by opt65_reach [1683, 1684, 1685, 1686])
    (fun _ => by opt65_reach [1687, 1688, 1689, 1690, 1691, 1692] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X8_sized _ 2) hks5 hB5
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks6 : KS4 m6 (X8 s.executionEnv.calldata 3) := ks4_congr hks6' fun k _ => (permN_succ _ _).symm
  obtain ⟨m7, hks7', hB7, hrc7, hf7, hR7⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m6) (pc0 := 5149) (r1 := 5157) (r2 := 5171) (c1 := 15) (c2 := 21) (b := 3) (by norm_num)
    (by opt65_reach [1693, 1694, 1695, 1696])
    (fun _ => by opt65_reach [1697, 1698, 1699, 1700, 1701, 1702] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc6 (X8_sized _ 3) hks6 hB6
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks7 : KS4 m7 (X8 s.executionEnv.calldata 4) := ks4_congr hks7' fun k _ => (permN_succ _ _).symm
  obtain ⟨m8, hks8', hB8, hrc8, hf8, hR8⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m7) (pc0 := 5171) (r1 := 5179) (r2 := 5193) (c1 := 15) (c2 := 21) (b := 4) (by norm_num)
    (by opt65_reach [1703, 1704, 1705, 1706])
    (fun _ => by opt65_reach [1707, 1708, 1709, 1710, 1711, 1712] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc7 (X8_sized _ 4) hks7 hB7
    (St := fun b k => permN (b + 1) (I8 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks8 : KS4 m8 (X8 s.executionEnv.calldata 5) := ks4_congr hks8' fun k _ => (permN_succ _ _).symm
  -- gfix 3
  have hfB : FrameExcept m2 m8 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (MU, MU + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
      (FrameExcept.trans hf3 hf4) hf5) hf6) hf7) hf8).mono (by decide)
  have h68 : word m8 HAVE6 = 0 := by
    rw [word_frame hfB (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h62
  have gG : Reach (callState s 5193 [flag b] m8) (callState s 11314 [wd 3, wd 5203, flag b] m8) 18 := by
    opt65_reach [1713, 1714, 1715, 1716, 1717]
  obtain ⟨m9, hlanes, hks9, hkeep9, hf9, hc9⟩ := gfix_call hs (ret := 5203) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m8 hrc8
    (amask := 3) (by norm_num) 2 (by decide) (X8 s.executionEnv.calldata 5) (X8_sized _ 5) hks8
    (I8 s.executionEnv.calldata) h68
    (fun sl hsl _ => hB8.pending hsl (fun _ _ => rfl) h68 rfl)
  rw [gfix3_flag hcd32 (I := I8 s.executionEnv.calldata) (col := 3) rfl rfl] at hc9
  -- pass3 (rows 4, 5 of column 3 into ACC + 0x2000)
  have gP : Reach (callState s 5203 [flag (okCol1 s.executionEnv.calldata 3), flag b] m9)
      (callState s 11032 [wd (64 * 3), wd ZH, wd (ACC + 0x2000), wd 5220,
        flag (b && okCol1 s.executionEnv.calldata 3)] m9) 27 := by
    opt65_reach [1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725] with [flag, ite01_land, ZH, ACC]
  obtain ⟨m10, hacc, hf10, hc10⟩ := pass3_call hs (ret := 5220)
    (tail := [flag (b && okCol1 s.executionEnv.calldata 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m9
    (k := 3) (zh := ZH) (acc := ACC + 0x2000) (by norm_num) (by unfold ZH ACC; norm_num) (by omega)
    (by unfold ACC HP; norm_num)
  have gE : Reach (callState s 5220 [flag (b && okCol1 s.executionEnv.calldata 3)] m10)
      (callState s 5221 [flag (b && okCol1 s.executionEnv.calldata 3)] m10) 1 := by
    opt65_reach [1726]
  -- frames
  have hf9' : FrameExcept m m9 [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32),
      (BK, BK + 800), (MU, MU + 256)] :=
    (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf1 hf2) hfB) hf9).mono (by decide)
  have hfA : FrameExcept m m10 (gbase ++ [(MU, MU + 256)]) :=
    (FrameExcept.trans hf9' hf10).mono (by unfold gbase; decide)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m10 k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hfA (by unfold gbase; s4_frame) hk ht
  have hacc1 : AccCols1 m10 s.executionEnv.calldata 4 :=
    accCols1_step (n := 3) (by norm_num) hI.acc1
      (fun k hk t ht => (hI.zhat k (by omega) t ht).1) hzh
      (A := fun t => word m9 (ABUF + 32 * t))
      (gfix3_lanes hcd32 (I := I8 s.executionEnv.calldata) (col := 3) rfl rfl hlanes hkeep9 hB8)
      (fun t => word_lt _ _)
      (fun t ht => by
        rw [hacc t ht,
          word_frame hf9' (a := ACC + 0x2000 + 32 * t) (lo := ACC + 0x2000) (hi := ACC + 0x4000)
            (by s4_frame) (Nat.le_add_right _ _) (by omega),
          word_frame hf9' (a := ZH + 32 * t) (lo := ZH) (hi := ZH + 8192) (by s4_frame)
            (by omega) (by omega)])
  have hmu10 : MuAt m10 s.executionEnv.calldata := by
    intro hm x hx
    have hf : FrameExcept m4 m10 gbase :=
      (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
        hf5 hf6) hf7) hf8) hf9) hf10).mono (by unfold gbase; decide)
    rw [word_frame hf (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by unfold gbase; s4_frame) (by omega)
        (by omega), hmuw x hx, cext_lane hks3 (sh := 3) (x := x) (by norm_num) (by omega), le64_muOf hm hx]
    unfold X8 I8 muSlot
    simp only [if_true, if_pos hm]
  refine ⟨m10, ⟨invR_next hI.rc4 hI.rc1 hI.tbl hI.zhat hI.hp hI.rho hI.acc0 hI.zMisc hI.zCw hI.zIdx hfA
    (by s4_frame) hacc1 (CbAt.frame hI.cb hfA (by unfold gbase; s4_frame)),
    TrlAt.frame hI.trl hfA (by unfold gbase; s4_frame), hmu10⟩, ?_⟩
  have hR := (((((((((((((hR1.trans gM).trans hc2).trans hR3).trans gC).trans hc4).trans hR5).trans
    hR6).trans hR7).trans hR8).trans gG).trans hc9).trans gP).trans hc10).trans gE
  exact hR.mono (by unfold Gas.pG8; omega)

end MlDsaOpt65.Proofs.S4
