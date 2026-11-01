import MlDsaOpt87.Main.S5.Acc
import MlDsaOpt87.Fn.Pass3k14
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# The Kronecker group 14 of ML-DSA-87 (`5435 … 5593`, WP S5)

Slots 0–3 squeeze `A[7][6]`, `A[7][5]`, `A[7][4]`, `A[7][3]`; `gfix 15`; then
`pass3k14` adds `Σ_{i<4} A[7][3 + i][t] · ẑ_{3+i}[t]` to lane 3 (row 7) of
`ACC + 0x2000`. Both accumulator tables then hold the exact sums over all seven
columns, which gives `AccAt`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Slot `k` of group 14: the seed of `A[7][6 − k]`. -/
def s5I14 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd 7 (6 - k))

/-- Group 14 at the start of squeeze `b`. -/
def s5X14 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := permN b (s5I14 cd k)

theorem s5X14_sized (cd : ByteArray) (b : Nat) : Sized4 (s5X14 cd b) := fun _ _ =>
  permN_size (seedState_size _ _) b

theorem s5_g14_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(15 : Nat).testBit sl || (aI (s5I14 cd sl)).isSome) = okRow7 cd := by
  have e : ∀ c, MlDsaOpt87.Proofs.aI (seedState 168 (aSeed cd 7 c)) = aOf cd 7 c :=
    fun c => GroupP.aI_aSeed hcd 7 c
  unfold s5I14 okRow7
  simp only [e, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (15 : Nat).testBit 0 = true by decide, show (15 : Nat).testBit 1 = true by decide,
    show (15 : Nat).testBit 2 = true by decide, show (15 : Nat).testBit 3 = true by decide,
    Bool.not_true, Bool.false_or, Bool.and_true]
  rw [show (6 : Nat) - 0 = 6 from rfl, show (6 : Nat) - 1 = 5 from rfl, show (6 : Nat) - 2 = 4 from rfl,
    show (6 : Nat) - 3 = 3 from rfl, show (3 : Nat) + 0 = 3 from rfl, show (3 : Nat) + 1 = 4 from rfl,
    show (3 : Nat) + 2 = 5 from rfl, show (3 : Nat) + 3 = 6 from rfl]
  cases (aOf cd 7 3).isSome <;> cases (aOf cd 7 4).isSome <;> cases (aOf cd 7 5).isSome <;>
    cases (aOf cd 7 6).isSome <;> rfl

theorem s5_g14_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (s5X14 s.executionEnv.calldata 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 5435 [flag b] m) (callState s 5463 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have g0 : Reach (callState s 5435 [flag b] m)
      (callState s 12945 [wd 0x0fffff00000fff0000079a, wd 0, wd 15, wd 0, wd 5463, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    opt87_reach [1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 5463) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 15) (cmult := 0) (l4 := 0x0fffff00000fff0000079a)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by avoids_tac)
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have hks : KS4 m1 (s5X14 cd 0) :=
    s5_ks4_ginit (keep := 0) (amult := 15) (cmult := 0) (l4 := 0x0fffff00000fff0000079a) (kmask := 0)
      (L := fun k => (6 - k) + 256 * 7 + 0x1F0000)
      (S := s5X14 cd 0) hrho0 (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun k _ => by omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        have e : s5X14 cd 0 k = seedState 168 (aSeed cd 7 (6 - k)) := rfl
        rw [e]
        exact s5_freshLane_aSeed hcd32 (amult := 15) (k := k) (r := 7) (col := 6 - k)
          (L := fun k => (6 - k) + 256 * 7 + 0x1F0000) (by norm_num) (by omega)
          (by interval_cases k <;> decide) rfl hx)
      hg
  refine ⟨m1, hks, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- Group 14's cost: glue 249 and its calls. -/
theorem s5_g14_cost : 249 + Gas.ginit + 5 * (Gas.kf4 + Gas.blk) + Gas.gfix 4 + Gas.pass3k14 = Gas.pG14 := by
  unfold Gas.pG14; ring

theorem s5_seg_g14 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvTr s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 5435 [flag b] m)
        (callState s 5593 [flag (b && okRow7 s.executionEnv.calldata)] m') Gas.pG14 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := s5_g14_ginit hs hcd hI.rho b
  have hrc1 := RC4Table.frame hI.rc4 hf1 (by avoids_tac)
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := s5_kb_round hs (fb := flag b) (stk := [flag b])
    (m := m1) (pc0 := 5463) (r1 := 5471) (r2 := 5485) (c1 := 15) (c2 := 21) (b := 0) (by norm_num)
    (by opt87_reach [1667, 1668, 1669, 1670])
    (fun _ => by opt87_reach [1671, 1672, 1673, 1674, 1675, 1676] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (s5X14_sized _ 0) hks1 (S5Blocks.zero _ _)
    (St := fun b k => permN (b + 1) (s5I14 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks2 : KS4 m2 (s5X14 s.executionEnv.calldata 1) := s5_KS4_congr hks2' fun k _ => (permN_succ _ _).symm
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := s5_kb_round hs (fb := flag b) (stk := [flag b])
    (m := m2) (pc0 := 5485) (r1 := 5493) (r2 := 5507) (c1 := 15) (c2 := 21) (b := 1) (by norm_num)
    (by opt87_reach [1677, 1678, 1679, 1680])
    (fun _ => by opt87_reach [1681, 1682, 1683, 1684, 1685, 1686] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (s5X14_sized _ 1) hks2 hB2
    (St := fun b k => permN (b + 1) (s5I14 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks3 : KS4 m3 (s5X14 s.executionEnv.calldata 2) := s5_KS4_congr hks3' fun k _ => (permN_succ _ _).symm
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := s5_kb_round hs (fb := flag b) (stk := [flag b])
    (m := m3) (pc0 := 5507) (r1 := 5515) (r2 := 5529) (c1 := 15) (c2 := 21) (b := 2) (by norm_num)
    (by opt87_reach [1687, 1688, 1689, 1690])
    (fun _ => by opt87_reach [1691, 1692, 1693, 1694, 1695, 1696] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (s5X14_sized _ 2) hks3 hB3
    (St := fun b k => permN (b + 1) (s5I14 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks4 : KS4 m4 (s5X14 s.executionEnv.calldata 3) := s5_KS4_congr hks4' fun k _ => (permN_succ _ _).symm
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := s5_kb_round hs (fb := flag b) (stk := [flag b])
    (m := m4) (pc0 := 5529) (r1 := 5537) (r2 := 5551) (c1 := 15) (c2 := 21) (b := 3) (by norm_num)
    (by opt87_reach [1697, 1698, 1699, 1700])
    (fun _ => by opt87_reach [1701, 1702, 1703, 1704, 1705, 1706] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (s5X14_sized _ 3) hks4 hB4
    (St := fun b k => permN (b + 1) (s5I14 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks5 : KS4 m5 (s5X14 s.executionEnv.calldata 4) := s5_KS4_congr hks5' fun k _ => (permN_succ _ _).symm
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := s5_kb_round hs (fb := flag b) (stk := [flag b])
    (m := m5) (pc0 := 5551) (r1 := 5559) (r2 := 5573) (c1 := 15) (c2 := 21) (b := 4) (by norm_num)
    (by opt87_reach [1707, 1708, 1709, 1710])
    (fun _ => by opt87_reach [1711, 1712, 1713, 1714, 1715, 1716] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (s5X14_sized _ 4) hks5 hB5
    (St := fun b k => permN (b + 1) (s5I14 s.executionEnv.calldata k)) (fun k _ => permN_succ _ _)
  have hks6 : KS4 m6 (s5X14 s.executionEnv.calldata 5) := s5_KS4_congr hks6' fun k _ => (permN_succ _ _).symm
  -- gfix 15
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by s5_frame_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 5573 [flag b] m6) (callState s 12615 [wd 15, wd 5583, flag b] m6) 18 := by
    opt87_reach [1717, 1718, 1719, 1720, 1721]
  obtain ⟨m7, hlanes, -, -, hf7, hc7⟩ := gfix_call hs (ret := 5583) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 15) (by norm_num) 4 (by decide) (s5X14 s.executionEnv.calldata 5) (s5X14_sized _ 5) hks6
    (s5I14 s.executionEnv.calldata) h66
    (fun sl hsl _ => hB6.pending hsl (fun _ _ => rfl) h66 rfl)
  rw [s5_g14_flag hcd32] at hc7
  -- pass3k14
  have gK : Reach (callState s 5583 [flag (okRow7 s.executionEnv.calldata), flag b] m7)
      (callState s 12528 [wd 5592, flag (b && okRow7 s.executionEnv.calldata)] m7) 18 := by
    opt87_reach [1722, 1723, 1724, 1725, 1726] with [flag, ite01_land]
  obtain ⟨m8, hacc, hf8, hc8⟩ := pass3k14_call hs (ret := 5592)
    (tail := [flag (b && okRow7 s.executionEnv.calldata)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
  have gE : Reach (callState s 5592 [flag (b && okRow7 s.executionEnv.calldata)] m8)
      (callState s 5593 [flag (b && okRow7 s.executionEnv.calldata)] m8) 1 := by
    opt87_reach [1727]
  -- frames
  have hfA : FrameExcept m m7 GroupP.gsFrame :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7) (by s5_sub)
  have hfG : FrameExcept m m8 (groupFrame 1) :=
    GroupP.FrameExcept.of_avoid (FrameExcept.trans hfA hf8) (by s5_sub)
  have hE := s5_invE_frame hI.toInvE (s5_frame_widen hfG)
  refine ⟨m8, ⟨hE.rc1, hE.tbl, hE.hp, s5_accAt_of hI.zhat fun hok g hg t ht => ?_, hE.c,
    TrlAt.frame hI.trl hfG (by s5_frame_tac)⟩, ?_⟩
  · have hz : ∀ k, k < 7 → zhLane m k t < 2 ^ 28 := fun k hk => (hI.zhat k hk t ht).1
    have hle : ∀ r, accSum s.executionEnv.calldata m r t 7 ≤ 7 * 2 ^ 51 := fun r =>
      s5_accSum_le ht hz 7 le_rfl
    interval_cases g
    · rw [word_frame hfG (a := ACC + 0x2000 * 0 + 32 * t) (lo := ACC) (hi := ACC + 8192)
        (by s5_frame_tac) (by omega) (by omega)]
      exact hI.acc0 (s5_okUpTo_of_okA hok (by norm_num) (by norm_num) 7 le_rfl) t ht
    · -- row group 1: rows 4–6 done, row 7 gains columns 3–6
      have hmid : (okUpTo s.executionEnv.calldata 1 4 3 && okMid s.executionEnv.calldata 7) = true := by
        rw [s5_okUpTo_of_okA hok (by norm_num) (by norm_num) 3 (by norm_num),
          s5_okMid_of_okA hok 7 le_rfl]; rfl
      have hl : ∀ sl, sl < 4 → lane (word m7 (ABUF + 32 * t)) sl =
          ((aD s.executionEnv.calldata 7 (6 - sl))[t]!).toNat := fun sl hsl => by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (s5_okA_get hok (r := 7) (s := 6 - sl) (by norm_num)
          (by omega))
        have := hlanes sl hsl (by interval_cases sl <;> decide) a
          ((GroupP.aI_aSeed hcd32 7 (6 - sl)).trans ha) t ht
        rw [this]; unfold aD; rw [ha]; rfl
      have hl0 : lane (word m7 (ABUF + 32 * t)) 0 = ((aD s.executionEnv.calldata 7 6)[t]!).toNat :=
        hl 0 (by norm_num)
      have hl1 : lane (word m7 (ABUF + 32 * t)) 1 = ((aD s.executionEnv.calldata 7 5)[t]!).toNat :=
        hl 1 (by norm_num)
      have hl2 : lane (word m7 (ABUF + 32 * t)) 2 = ((aD s.executionEnv.calldata 7 4)[t]!).toNat :=
        hl 2 (by norm_num)
      have hl3 : lane (word m7 (ABUF + 32 * t)) 3 = ((aD s.executionEnv.calldata 7 3)[t]!).toNat :=
        hl 3 (by norm_num)
      have hz3 : lane (word m7 (ZH + 32 * t)) 3 = zhLane m 3 t :=
        (s5_zhLane_lo m7 (k := 3) (by norm_num) t).symm.trans (s5_gs_zh hfA (by norm_num) ht)
      have hz4 : lane (word m7 (ZH2 + 32 * t)) 0 = zhLane m 4 t :=
        (s5_zhLane_hi m7 (k := 0) (by norm_num) t).symm.trans (s5_gs_zh hfA (by norm_num) ht)
      have hz5 : lane (word m7 (ZH2 + 32 * t)) 1 = zhLane m 5 t :=
        (s5_zhLane_hi m7 (k := 1) (by norm_num) t).symm.trans (s5_gs_zh hfA (by norm_num) ht)
      have hz6 : lane (word m7 (ZH2 + 32 * t)) 2 = zhLane m 6 t :=
        (s5_zhLane_hi m7 (k := 2) (by norm_num) t).symm.trans (s5_gs_zh hfA (by norm_num) ht)
      have hK : kronWord14 m7 t = 2 ^ 192 *
          (((aD s.executionEnv.calldata 7 6)[t]!).toNat * zhLane m 6 t +
            ((aD s.executionEnv.calldata 7 5)[t]!).toNat * zhLane m 5 t +
            ((aD s.executionEnv.calldata 7 4)[t]!).toNat * zhLane m 4 t +
            ((aD s.executionEnv.calldata 7 3)[t]!).toNat * zhLane m 3 t) := by
        unfold kronWord14
        rw [s5_kron (word_lt _ _) (word_lt _ _)
          (fun k hk => by rw [hl k hk]; exact s5_aD_lt _ _ _ ht)
          (by rw [hz3]; exact hz 3 (by norm_num))
          (fun k hk => by
            interval_cases k
            · rw [hz4]; exact hz 4 (by norm_num)
            · rw [hz5]; exact hz 5 (by norm_num)
            · rw [hz6]; exact hz 6 (by norm_num)),
          hl0, hl1, hl2, hl3, hz3, hz4, hz5, hz6]
      have hv : ∀ j, j < 4 → accSum s.executionEnv.calldata m (4 + j) t (if j < 3 then 7 else 3) +
          (if j = 3 then (((aD s.executionEnv.calldata 7 6)[t]!).toNat * zhLane m 6 t +
            ((aD s.executionEnv.calldata 7 5)[t]!).toNat * zhLane m 5 t +
            ((aD s.executionEnv.calldata 7 4)[t]!).toNat * zhLane m 4 t +
            ((aD s.executionEnv.calldata 7 3)[t]!).toNat * zhLane m 3 t) else 0) =
          accSum s.executionEnv.calldata m (4 * 1 + j) t 7 := fun j hj => by
        by_cases h3 : j < 3
        · rw [if_pos h3, if_neg (by omega), Nat.add_zero]
        · have : j = 3 := by omega
          subst this
          rw [if_neg (by decide), if_pos rfl]
          show accSum _ m 7 t 3 + _ = accSum _ m 7 t 3 + _ + _ + _ + _
          ring
      rw [show ACC + 0x2000 * 1 + 32 * t = ACC + 0x2000 + 32 * t by ring, hacc t ht, s5_gs_acc1 hfA ht,
        hI.acc1 hmid t ht, hK, s5_acc7 _ _ (fun j hj => by rw [hv j hj]; have := hle (4 * 1 + j); omega)]
      exact s5_pack4_congr hv
  · have hR := (((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gK).trans hc8).trans gE
    exact hR.mono (by rw [← s5_g14_cost]; omega)

end MlDsaOpt87.Proofs
