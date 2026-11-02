import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Group
import MlDsaOptGlam44.Main.Ex.Round
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegG2.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `3477 … 3875`: the mixed group

`tr`'s blocks 0 … 4 in slot 0 (`trabs` before each `kf4`), column 2 rows
0 … 2 in slots 1 … 3; `gfix` on slots 1 … 3; the candidates are copied to
`SB`. `tr`'s sponge stays in slot 0 of `KS` for the window. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

namespace Ex

open MlDsaOpt44.Proofs

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    aI (seedA cd r col) = aOf cd r col :=
  aI_seedState (by rw [aSeed_size hcd]; norm_num)

/-- Group 2 at the start of squeeze `b`: the `tr` sponge in slot 0, rows
`0 … 2` of column 2 in slots 1 … 3. -/
def X2 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 0 then absorbPre 136 (padPk cd) b else permN b (seedA cd (k - 1) 2)

theorem X2_sized (cd : ByteArray) (b : Nat) : Sized4 (X2 cd b) := fun k _ => by
  unfold X2; split
  · exact absorbPre_size _ _ b
  · exact permN_size (seedState_size _ _) b

theorem permute_upd_X2 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (upd (X2 cd b) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (b * 136) (X2 cd b 0)) k) = X2 cd (b + 1) k := by
  unfold upd X2
  by_cases h0 : k = 0
  · subst h0; simp only [if_true]
    rw [absorbPre_succ]; rfl
  · rw [if_neg h0, if_neg h0, if_neg h0, permN_succ]

/-- The block states of group 2. -/
def St2 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := X2 cd (b + 1) k

theorem g2_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(14 : Nat).testBit sl ||
      (aI (if sl = 0 then Fips202.emptyState else seedA cd (sl - 1) 2)).isSome) = okCol3 cd 2 := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (14 : Nat).testBit 0 = false by decide, show (14 : Nat).testBit 1 = true by decide,
    show (14 : Nat).testBit 2 = true by decide, show (14 : Nat).testBit 3 = true by decide,
    okCol3, show List.range 3 = [0, 1, 2] from rfl, Nat.reduceSub, if_true, if_false, aI_seedA hcd, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
    show (3 : Nat) ≠ 0 by decide, Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or,
    Bool.true_and, Bool.and_true]

theorem g2_ginit {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (X2 s.executionEnv.calldata 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 2452 [flag b] m) (callState s 2480 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho
  have g0 : Reach (callState s 2452 [flag b] m)
      (callState s 18001 [wd 0x0eeeee00000084000000e0, wd 0, wd 14, wd 0, wd 2480, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    glam44_rreach [949, 950, 951, 952, 953, 954, 955, 956, 957, 958] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 2480) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 14) (cmult := 0) (l4 := 0x0eeeee00000084000000e0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := hrho.frame hf0 (by avoids_tac)
  have hks : KS4 m1 (X2 cd 0) :=
    ks4_ginit (kmask := 0) (L := fun k => if k = 0 then 0 else 2 + 256 * (k - 1) + 0x1F0000)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := X2 cd 0)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        by_cases h0 : k = 0
        · subst h0
          have e : X2 cd 0 0 = Fips202.emptyState := rfl
          rw [e]
          exact freshLane_zero (by decide) (by decide) (by simp) x
        · have e : X2 cd 0 k = seedA cd (k - 1) 2 := by unfold X2; rw [if_neg h0]; rfl
          rw [e]
          exact freshLane_aSeed (by unfold HDR at hcd; omega) (fun _ _ => rfl) (by omega) (by norm_num)
            (by interval_cases k <;> first | omega | decide) (by simp)
            (by simp only [if_neg h0]) hx)
      hg
  refine ⟨m1, hks, by
      rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

end Ex

open Ex in
theorem seg_g2 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG1 s.executionEnv.calldata m) (b : Bool) (hfl : word m FLAG = 1) :
    ∃ m', InvG2 s.executionEnv.calldata m' ∧
      Reach (callState s 2452 [flag b] m)
        (callState s 2850 [flag (b && okCol3 s.executionEnv.calldata 2)] m') Gas.pG2 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd' : 1312 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  have htl : [flag b].length ≤ 8 := by simp
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g2_ginit hs hcd hI.rho b
  have hrc1 := hI.rc4.frame hf1 (by avoids_tac)
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := absorb_round hs hcd' htl (m := m1)
    (pc0 := 2480) (r0 := 2526) (r1 := 2534) (r2 := 2548) (c0 := 27) (c1 := 15) (c2 := 21)
    (b := 0) (j := 0) (off := 0) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach [959, 960, 961, 962, 963, 964, 965, 966, 967])
    (fun _ => by glam44_rreach [968, 969, 970, 971])
    (fun _ => by glam44_rreach [972, 973, 974, 975, 976, 977] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (X2_sized _ 0) hks1 (HBlocks.zero _ _ _ _) (St := St2 s.executionEnv.calldata)
    (fun k hk => (permute_upd_X2 _ 0 hk).symm)
  have hks2 : KS4 m2 (X2 s.executionEnv.calldata 1) := KS4.congr hks2' fun k hk => permute_upd_X2 _ 0 hk
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := absorb_round hs hcd' htl (m := m2)
    (pc0 := 2548) (r0 := 2595) (r1 := 2603) (r2 := 2617) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 1) (j := 1) (off := 136) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach [978, 979, 980, 981, 982, 983, 984, 985, 986])
    (fun _ => by glam44_rreach [987, 988, 989, 990])
    (fun _ => by glam44_rreach [991, 992, 993, 994, 995, 996] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X2_sized _ 1) hks2 hB2 (St := St2 s.executionEnv.calldata)
    (fun k hk => (permute_upd_X2 _ 1 hk).symm)
  have hks3 : KS4 m3 (X2 s.executionEnv.calldata 2) := KS4.congr hks3' fun k hk => permute_upd_X2 _ 1 hk
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := absorb_round hs hcd' htl (m := m3)
    (pc0 := 2617) (r0 := 2665) (r1 := 2673) (r2 := 2687) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 2) (j := 2) (off := 272) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach [997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005])
    (fun _ => by glam44_rreach [1006, 1007, 1008, 1009])
    (fun _ => by glam44_rreach [1010, 1011, 1012, 1013, 1014, 1015] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (X2_sized _ 2) hks3 hB3 (St := St2 s.executionEnv.calldata)
    (fun k hk => (permute_upd_X2 _ 2 hk).symm)
  have hks4 : KS4 m4 (X2 s.executionEnv.calldata 3) := KS4.congr hks4' fun k hk => permute_upd_X2 _ 2 hk
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := absorb_round hs hcd' htl (m := m4)
    (pc0 := 2687) (r0 := 2735) (r1 := 2743) (r2 := 2757) (c0 := 28) (c1 := 15) (c2 := 21)
    (b := 3) (j := 3) (off := 408) (sh := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024])
    (fun _ => by glam44_rreach [1025, 1026, 1027, 1028])
    (fun _ => by glam44_rreach [1029, 1030, 1031, 1032, 1033, 1034] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (X2_sized _ 3) hks4 hB4 (St := St2 s.executionEnv.calldata)
    (fun k hk => (permute_upd_X2 _ 3 hk).symm)
  have hks5 : KS4 m5 (X2 s.executionEnv.calldata 4) := KS4.congr hks5' fun k hk => permute_upd_X2 _ 3 hk
  -- squeeze 4 (blkh)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := absorb_round_h hs hcd' htl (m := m5)
    (pc0 := 2757) (r0 := 2805) (r1 := 2813) (r2 := 2827) (c0 := 28) (c1 := 15) (c2 := 21)
    (j := 4) (off := 544) (sh := 0) (by norm_num) (by norm_num) (by norm_num)
    bufOK_abuf
    (by glam44_rreach [1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043])
    (fun _ => by glam44_rreach [1044, 1045, 1046, 1047])
    (fun _ => by glam44_rreach [1048, 1049, 1050, 1051, 1052, 1053] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X2_sized _ 4) hks5 hB5 (St := St2 s.executionEnv.calldata)
    (fun k hk => (permute_upd_X2 _ 4 hk).symm)
  have hks6 : KS4 m6 (X2 s.executionEnv.calldata 5) := KS4.congr hks6' fun k hk => permute_upd_X2 _ 4 hk
  -- gfix 14
  have hfA := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans
    (FrameExcept.trans hf1 hf2) hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    have hf := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
    rw [word_frame hf (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 2827 [flag b] m6) (callState s 17591 [wd 14, wd 2837, flag b] m6) 18 := by
    glam44_rreach [1054, 1055, 1056, 1057, 1058]
  let I : Nat → Fips202.SpongeState := fun k =>
    if k = 0 then Fips202.emptyState else seedA s.executionEnv.calldata (k - 1) 2
  obtain ⟨m7, hlanes, hks7, hf7, hc7⟩ := gfix_call hs (ret := 2837) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 14) (by norm_num) 3 (by decide) (X2 s.executionEnv.calldata 5) (X2_sized _ 5) hks6 I h66
    (fun sl hsl hbit => by
      have hsl0 : sl ≠ 0 := by
        rintro rfl; exact absurd hbit (by decide)
      have hI : I sl = seedA s.executionEnv.calldata (sl - 1) 2 := by simp only [I, if_neg hsl0]
      refine ⟨hB6.slotHead hsl (fun b' hb' => ?_), ?_⟩
      · show X2 _ (b' + 1) sl = _
        rw [hI]; unfold X2; rw [if_neg hsl0]
      · rw [hI]; unfold X2; rw [if_neg hsl0])
  have hflag := g2_flag (cd := s.executionEnv.calldata) hcd32
  simp only [I] at hc7
  rw [hflag] at hc7
  -- AND, MCOPY ABUF → SB
  have gA : Reach (callState s 2837 [flag (okCol3 s.executionEnv.calldata 2), flag b] m7)
      (callState s 2849 [wd SB, wd ABUF, wd 8192, flag (b && okCol3 s.executionEnv.calldata 2)] m7) 13 := by
    glam44_rreach [1059, 1060, 1061, 1062, 1063] with [flag, ite01_land, ABUF, SB]
  have hmc := reach_mcopy hs ⟨1064, by norm_num⟩ (pc := 2849) (d := SB) (src := ABUF) (n := 8192)
    (rest := [flag (b && okCol3 s.executionEnv.calldata 2)]) (m := m7)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold SB; norm_num)
    (by unfold ABUF; norm_num) (by norm_num) (by norm_num) (by unfold SB; omega) (by unfold ABUF; omega) (by simp)
  have hfB := FrameExcept.trans hfA hf7
  refine ⟨MachineState.writeBytes m7 (MachineState.readPadded m7 ABUF 8192) SB, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- InvX
    have hf := FrameExcept.trans hfB (FrameExcept.mcopy m7 ABUF SB 8192)
    have hz : ZHatAt (MachineState.writeBytes m7 (MachineState.readPadded m7 ABUF 8192) SB)
        s.executionEnv.calldata := fun k hk t ht => by
      rw [word_frame hf (lo := ZH) (hi := ZH + 8192) (by avoids_tac) (by omega) (by omega)]
      exact hI.zhat k hk t ht
    exact ⟨hI.rc4.frame hf (by avoids_tac), hI.rc1.frame hf (by avoids_tac), hI.tbl.frame hf (by avoids_tac),
      hz, hI.rho.frame hf (by avoids_tac), hI.zIdx.frame hf (by avoids_tac), hI.zNeg.frame hf (by avoids_tac)⟩
  · have hf := FrameExcept.trans hfB (FrameExcept.mcopy m7 ABUF SB 8192)
    exact hI.c0.frame hf (by avoids_tac)
  · have hf := FrameExcept.trans hfB (FrameExcept.mcopy m7 ABUF SB 8192)
    exact hI.c1.frame hf (by avoids_tac)
  · intro hok t ht r hr
    rw [word_mcopy _ (by omega) (by omega), show ABUF + (SB + 32 * t - SB) = ABUF + 32 * t by omega]
    have hs3 : (aOf s.executionEnv.calldata r 2).isSome = true := by
      unfold okCol3 at hok
      rw [List.all_eq_true] at hok
      exact hok r (List.mem_range.mpr hr)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs3
    have := hlanes (r + 1) (by omega) (by interval_cases r <;> decide) a
      (by simp only [I, if_neg (by omega : r + 1 ≠ 0), Nat.add_sub_cancel]; rw [aI_seedA hcd32]; exact ha)
      t ht
    rw [this]; unfold aD; rw [ha]; rfl
  · refine ⟨X2 s.executionEnv.calldata 5, X2_sized _ 5, ?_, rfl⟩
    exact KS4.frame hks7 (FrameExcept.mcopy m7 ABUF SB 8192) (by avoids_tac)
  · -- glam: `FLAG`
    rw [word_frame (FrameExcept.trans hfB (FrameExcept.mcopy m7 ABUF SB 8192)) (lo := FLAG) (hi := FLAG + 32)
      (by unfold FLAG; avoids_tac) le_rfl le_rfl]
    exact hfl
  · have hR := ((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
      gA).trans hmc
    refine hR.mono ?_
    unfold Gas.pG2
    generalize Gas.ginit = a; generalize Gas.trabs 5 = c; generalize Gas.kf4 = d
    generalize Gas.blk = e; generalize Gas.blkh = f; generalize Gas.gfix 3 = g
    omega

end MlDsaOptGlam44.Proofs
