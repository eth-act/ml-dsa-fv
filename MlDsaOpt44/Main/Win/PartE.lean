import MlDsaOpt44.Main.Win.PartD
set_option warningAsError true
/-!
# Window part E: `4745 … 4973`

The fix-up of `E = (A33, A32)` (slots 2, 3) and its copy to `SB + 8192`; the
staged `B3` blocks are copied back to `ABUF` / `FL`, two `kmove` calls rebuild
`B3`'s states (`A13`, `A23` from slots 0, 1 to slots 2, 3; `A03` from the image
`SAVE1` into slot 1); the fix-up of `B3`; the fused accumulation `pass3f4`.
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

/-- The seeds of `E`'s slots. -/
def IE (cd : ByteArray) (sl : Nat) : Fips202.SpongeState := if sl = 2 then seedA cd 3 3 else seedA cd 3 2

def okE (cd : ByteArray) : Bool := (aOf cd 3 3).isSome && (aOf cd 3 2).isSome

theorem flag_E {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(12 : Nat).testBit sl || (aI (IE cd sl)).isSome) = okE cd := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (12 : Nat).testBit 0 = false by decide, show (12 : Nat).testBit 1 = false by decide,
    show (12 : Nat).testBit 2 = true by decide, show (12 : Nat).testBit 3 = true by decide,
    IE, okE, if_true, if_false, show (3 : Nat) ≠ 2 by decide, aI_seedA hcd,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_true]

theorem flag_B3 {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(14 : Nat).testBit sl || (aI (I3 cd sl)).isSome) = okCol3 cd 3 := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 3 = [0, 1, 2] from rfl,
    List.all_cons, List.all_nil,
    show (14 : Nat).testBit 0 = false by decide, show (14 : Nat).testBit 1 = true by decide,
    show (14 : Nat).testBit 2 = true by decide, show (14 : Nat).testBit 3 = true by decide,
    I3_1, I3_2, I3_3, okCol3, aI_seedA hcd,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_true]

theorem EB_E (cd : ByteArray) {b : Nat} (hb : b < 5) :
    EB cd b 2 = permN (b + 1) (IE cd 2) ∧ EB cd b 3 = permN (b + 1) (IE cd 3) := by
  unfold IE
  simp only [if_true, show (3 : Nat) ≠ 2 by decide, if_false]
  unfold EB
  by_cases h2 : b < 2
  · rw [if_pos h2, if_pos h2]; unfold W2
    simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_true, if_false]
    refine ⟨?_, ?_⟩ <;> trivial
  · rw [if_neg h2, if_neg h2]
    by_cases h3 : b = 2
    · subst h3; rw [if_pos rfl, if_pos rfl]; unfold W3 W2
      simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
        show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_true, if_false]
      exact ⟨(permN_succ _ _).symm, (permN_succ _ _).symm⟩
    · rw [if_neg h3, if_neg h3]; unfold W4
      simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
        show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_true, if_false]
      rw [show 3 + (b - 2) = b + 1 by omega]
      refine ⟨?_, ?_⟩ <;> trivial

/-- The staged heads of `B3` at `ACC` / `BASES`. -/
theorem stage_lanes {m : ByteArray} {cd : ByteArray}
    (hst : HBlocks m ACC BASES (fun b k => W1 cd (b + 1) k) 3) (hmg : Merged m cd)
    {sl : Nat} (h1 : 1 ≤ sl) (h4 : sl < 4) :
    (∀ t, t < 256 → lane (word m (ACC + 32 * t)) sl = candI (I3 cd sl) t) ∧
    (∀ g, g < 32 → flagBit (word m (BASES + 32 * g)) sl = FlagOf (I3 cd sl) g) := by
  have hW : ∀ b, (fun b k => W1 cd (b + 1) k) b sl = permN (0 + b + 1) (I3 cd sl) := fun b => by
    show W1 cd (b + 1) sl = _
    unfold W1; rw [if_neg (by omega), Nat.zero_add]; rfl
  refine ⟨fun t ht => ?_, fun g hg => ?_⟩
  · by_cases h168 : t < 168
    · have e : ACC + 32 * t = ACC + 1792 * (t / 56) + 32 * (t % 56) := by omega
      rw [e, hst.laneI (b0 := 0) h4 (by omega) (Nat.mod_lt _ (by norm_num)) (by omega) (hW _),
        show (0 + t / 56) * 56 + t % 56 = t by omega]
    · have e : ACC + 32 * t = ACC + 1792 * 3 + 32 * (t - 168) := by omega
      rw [e, (hmg sl h1 h4).1 _ (by omega), show 168 + (t - 168) = t by omega]
  · by_cases h21 : g < 21
    · have e : BASES + 32 * g = BASES + 224 * (g / 7) + 32 * (g % 7) := by omega
      rw [e, hst.flagI (b0 := 0) h4 (by omega) (Nat.mod_lt _ (by norm_num)) (by omega) (hW _),
        show (0 + g / 7) * 7 + g % 7 = g by omega]
    · have e : BASES + 32 * g = BASES + 224 * 3 + 32 * (g - 21) := by omega
      rw [e, (hmg sl h1 h4).2 _ (by omega), show 21 + (g - 21) = g by omega]

/-- Window part E. -/
theorem winE {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {w : Bool} (hrc : RC4Table m) (hks : KS4 m (W4 s.executionEnv.calldata 2))
    (hB : HBlocks m ABUF FL (EB s.executionEnv.calldata) 5) (hmg : Merged m s.executionEnv.calldata)
    (hst : HBlocks m ACC BASES (fun b k => W1 s.executionEnv.calldata (b + 1) k) 3)
    (hsv : St4At m SAVE1 (W2 s.executionEnv.calldata 2))
    (hzh : ZHatAt m s.executionEnv.calldata) (hcw : ColAt m CW s.executionEnv.calldata 0)
    (hhp : ColAt m HP s.executionEnv.calldata 1) (hsb : Col3At m SB s.executionEnv.calldata 2) :
    ∃ m', AccAt m' s.executionEnv.calldata ∧
      FrameExcept m m' [(HAVE6, HAVE6 + 32), (ABUF, FL + 1344), (KB, KB + 800), (BK, BK + 800),
        (SB + 8192, SB + 8192 + 8192), (KS, KS + 800), (ACC, ACC + 8192)] ∧
      Reach (callState s 4745 [flag w] m)
        (callState s 4973 [flag ((w && okE s.executionEnv.calldata) && okCol3 s.executionEnv.calldata 3)] m')
        (1797 + Gas.gfix 2 + 2 * Gas.kmove + Gas.gfix 3 + Gas.pass3f4) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  clear hcd
  generalize hcdv : s.executionEnv.calldata = cd at hcd32 hks hB hmg hst hsv hzh hcw hhp hsb ⊢
  -- E's fix-up
  have g1 : Reach (callState s 4745 [flag w] m) (callState s 10501 [wd 12, wd 4760, flag w]
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 26 := by
    opt44_reach [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g1
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hB0 := hB.frame hf0 (by avoids_tac) (by avoids_tac)
  obtain ⟨m1, hlE, hks1, hf1, hc1⟩ := gfix_call hs (ret := 4760) (tail := [flag w])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (hrc.frame hf0 (by avoids_tac)) (amask := 12) (by norm_num) 2 (by decide)
    (W4 cd 2) (W4_sized _ 2) (KS4.frame hks hf0 (by avoids_tac)) (IE cd) h60
    (fun sl hsl hbit => by
      have h23 : sl = 2 ∨ sl = 3 := by
        interval_cases sl <;> first | (left; rfl) | (right; rfl) | exact absurd hbit (by decide)
      rcases h23 with rfl | rfl
      · refine ⟨hB0.slotHead (by norm_num) fun b hb => (EB_E cd hb).1, ?_⟩
        unfold W4 IE; simp
      · refine ⟨hB0.slotHead (by norm_num) fun b hb => (EB_E cd hb).2, ?_⟩
        unfold W4 IE; simp)
  rw [flag_E hcd32] at hc1
  -- the copies: E to SB + 8192, the staged B3 back to ABUF / FL
  have gA : Reach (callState s 4760 [flag (okE cd), flag w] m1)
      (callState s 4772 [wd (SB + 8192), wd ABUF, wd 8192, flag (w && okE cd)] m1) 13 := by
    opt44_reach [1512, 1513, 1514, 1515, 1516] with [flag, ite01_land, ABUF, SB]
  have hmA := reach_mcopy hs ⟨1517, by norm_num⟩ (pc := 4772) (d := SB + 8192) (src := ABUF) (n := 8192)
    (rest := [flag (w && okE cd)]) (m := m1)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold SB; norm_num)
    (by unfold ABUF; norm_num) (by norm_num) (by norm_num) (by unfold SB; omega) (by unfold ABUF; omega) (by simp)
  generalize hmA' : MachineState.writeBytes m1 (MachineState.readPadded m1 ABUF 8192) (SB + 8192) = mA at hmA
  have hfA : FrameExcept m1 mA [(SB + 8192, SB + 8192 + 8192)] := hmA' ▸ FrameExcept.mcopy _ _ _ _
  have gB : Reach (callState s 4773 [flag (w && okE cd)] mA)
      (callState s 4782 [wd ABUF, wd ACC, wd 8192, flag (w && okE cd)] mA) 9 := by
    opt44_reach [1518, 1519, 1520] with [ABUF, ACC]
  have hmB := reach_mcopy hs ⟨1521, by norm_num⟩ (pc := 4782) (d := ABUF) (src := ACC) (n := 8192)
    (rest := [flag (w && okE cd)]) (m := mA)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold ABUF; norm_num)
    (by unfold ACC; norm_num) (by norm_num) (by norm_num) (by unfold ABUF; omega) (by unfold ACC; omega) (by simp)
  generalize hmB' : MachineState.writeBytes mA (MachineState.readPadded mA ACC 8192) ABUF = mB at hmB
  have hfB : FrameExcept mA mB [(ABUF, ABUF + 8192)] := hmB' ▸ FrameExcept.mcopy _ _ _ _
  have gC : Reach (callState s 4783 [flag (w && okE cd)] mB)
      (callState s 4792 [wd FL, wd BASES, wd 1024, flag (w && okE cd)] mB) 9 := by
    opt44_reach [1522, 1523, 1524] with [FL, BASES]
  have hmC := reach_mcopy hs ⟨1525, by norm_num⟩ (pc := 4792) (d := FL) (src := BASES) (n := 1024)
    (rest := [flag (w && okE cd)]) (m := mB)
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by unfold FL; norm_num)
    (by unfold BASES; norm_num) (by norm_num) (by norm_num) (by unfold FL; omega) (by unfold BASES; omega) (by simp)
  generalize hmC' : MachineState.writeBytes mB (MachineState.readPadded mB BASES 1024) FL = mC at hmC
  have hfC : FrameExcept mB mC [(FL, FL + 1024)] := hmC' ▸ FrameExcept.mcopy _ _ _ _
  -- E's lanes in SB + 8192 (kept to the end)
  have hEw : ∀ t, t < 256 → word mA (SB + 8192 + 32 * t) = word m1 (ABUF + 32 * t) := fun t ht => by
    rw [← hmA', word_mcopy _ (by omega) (by omega), Nat.add_sub_cancel_left]
  -- B3's heads in ABUF / FL
  have hf01 := FrameExcept.trans hf0 hf1
  have hstC : ∀ sl, 1 ≤ sl → sl < 4 → SlotHead mC sl (I3 cd sl) := fun sl h1 h4 => by
    have hst1 := hst.frame hf01 (by avoids_tac) (by avoids_tac)
    have hmg1 : Merged m1 cd := fun sl' a b => by
      obtain ⟨p, q⟩ := hmg sl' a b
      exact ⟨fun w' hw => by
          rw [word_frame hf01 (lo := ACC + 1792 * 3) (hi := ACC + 1792 * 3 + 2816) (by avoids_tac) (by omega)
            (by omega)]; exact p w' hw,
        fun v hv => by
          rw [word_frame hf01 (lo := BASES + 224 * 3) (hi := BASES + 224 * 3 + 352) (by avoids_tac) (by omega)
            (by omega)]; exact q v hv⟩
    obtain ⟨hl, hfl⟩ := stage_lanes hst1 hmg1 h1 h4
    refine ⟨fun t ht => ?_, fun g hg => ?_⟩
    · rw [← hmC', word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; unfold ABUF FL; omega),
        ← hmB', word_mcopy _ (by omega) (by omega), show ACC + (ABUF + 32 * t - ABUF) = ACC + 32 * t by omega,
        ← hmA', word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; unfold ACC SB; omega)]
      exact hl t ht
    · rw [← hmC', word_mcopy _ (by omega) (by omega), show BASES + (FL + 32 * g - FL) = BASES + 32 * g by omega,
        ← hmB', word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; unfold ABUF BASES; omega),
        ← hmA', word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; unfold BASES SB; omega)]
      exact hfl g hg
  have hfABC := FrameExcept.trans (FrameExcept.trans hfA hfB) hfC
  -- kmove: slots 0, 1 → 2, 3
  have gK1 : Reach (callState s 4793 [flag (w && okE cd)] mC)
      (callState s 11324 [wd 0x3333333333333333333333333333333333333333333333333333333333333333,
        wd 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, wd 0, wd 2, wd KS, wd 4870,
        flag (w && okE cd)] mC) 27 := by
    opt44_reach [1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533] with [KS]
  have hks1C := KS4.frame hks1 hfABC (by avoids_tac)
  obtain ⟨mD, hpD, hfD, hcD⟩ := kmove_call hs (ret := 4870) (tail := [flag (w && okE cd)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) mC
    (src := KS) (sl := 2) (sr := 0)
    (msk := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)
    (keep := 0x3333333333333333333333333333333333333333333333333333333333333333)
    (Or.inl rfl) (by unfold KS TOP; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let S5 : Nat → Fips202.SpongeState := fun k => if k < 2 then W4 cd 2 k else W4 cd 2 (k - 2)
  have hksD : KS4 mD S5 := fun x hx => by
    rw [hpD x hx, hks1C x hx, kmove_up2 _ (fun k _ => cpl_lt (laneOf_lt _ _))]
    exact il_congr fun k _ => by simp only [S5]; split <;> rfl
  -- kmove: A03 from SAVE1 into slot 1
  have gK2 : Reach (callState s 4870 [flag (w && okE cd)] mD)
      (callState s 11324 [wd 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd,
        wd 0x2222222222222222222222222222222222222222222222222222222222222222, wd 0, wd 0, wd SAVE1, wd 4949,
        flag (w && okE cd)] mD) 28 := by
    opt44_reach [1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542] with [SAVE1]
  have hsvD : St4At mD SAVE1 (W2 cd 2) :=
    (hsv.frame (FrameExcept.trans hf01 hfABC) (by avoids_tac)).frame hfD (by avoids_tac)
  obtain ⟨mE, hpE, hfE, hcE⟩ := kmove_call hs (ret := 4949) (tail := [flag (w && okE cd)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) mD
    (src := SAVE1) (sl := 0) (sr := 0)
    (msk := 0x2222222222222222222222222222222222222222222222222222222222222222)
    (keep := 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd)
    (Or.inr (by unfold KS SAVE1; norm_num)) (by unfold SAVE1 TOP; norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  let S6 : Nat → Fips202.SpongeState := fun k => if k = 1 then W2 cd 2 1 else S5 k
  have hksE : KS4 mE S6 := fun x hx => by
    rw [hpE x hx, hsvD x hx, hksD x hx,
      kmove_slot1 _ _ (fun k _ => cpl_lt (laneOf_lt _ _)) (fun k _ => cpl_lt (laneOf_lt _ _))]
    exact il_congr fun k _ => by simp only [S6]; split <;> rfl
  have hS6 : Sized4 S6 := fun k hk => by
    simp only [S6, S5]; split
    · exact W2_sized cd 2 1 (by norm_num)
    · split
      · exact W4_sized cd 2 k (by omega)
      · exact W4_sized cd 2 (k - 2) (by omega)
  -- B3's fix-up
  have gG : Reach (callState s 4949 [flag (w && okE cd)] mE) (callState s 10501
      [wd 14, wd 4964, flag (w && okE cd)] (MachineState.writeBytes mE (Data.Bytes.natToBytesPadded 0 32) HAVE6))
      26 := by
    opt44_reach [1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550] with [HAVE6]
  generalize hmF : MachineState.writeBytes mE (Data.Bytes.natToBytesPadded 0 32) HAVE6 = mF at gG
  have hfF : FrameExcept mE mF [(HAVE6, HAVE6 + 32)] := hmF ▸ FrameExcept.mstore mE HAVE6 0
  have h6F : word mF HAVE6 = 0 := hmF ▸ word_mstore mE HAVE6 0 (by norm_num)
  have hfDEF := FrameExcept.trans (FrameExcept.trans hfD hfE) hfF
  obtain ⟨mG, hlB, hksG, hfG, hcG⟩ := gfix_call hs (ret := 4964) (tail := [flag (w && okE cd)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) mF
    ((((hrc.frame hf01 (by avoids_tac)).frame hfABC (by avoids_tac)).frame hfDEF (by avoids_tac)))
    (amask := 14) (by norm_num) 3 (by decide) S6 hS6 (KS4.frame hksE hfF (by avoids_tac)) (I3 cd) h6F
    (fun sl hsl hbit => by
      have h1 : 1 ≤ sl := by
        by_contra h; have : sl = 0 := by omega
        subst this; exact absurd hbit (by decide)
      have hsh : SlotHead mF sl (I3 cd sl) := by
        obtain ⟨p, q⟩ := hstC sl h1 hsl
        exact ⟨fun t ht => by
            rw [word_frame hfDEF (lo := ABUF) (hi := ABUF + 8192) (by avoids_tac) (by omega) (by omega)]
            exact p t ht,
          fun g hg => by
            rw [word_frame hfDEF (lo := FL) (hi := FL + 1024) (by avoids_tac) (by omega) (by omega)]
            exact q g hg⟩
      refine ⟨hsh, ?_⟩
      simp only [S6, S5]
      interval_cases sl
      · unfold W2 I3; simp
      · unfold W4 I3; simp
      · unfold W4 I3; simp)
  rw [flag_B3 hcd32] at hcG
  -- pass3f4
  have gP : Reach (callState s 4964 [flag (okCol3 cd 3), flag (w && okE cd)] mG)
      (callState s 10229 [wd 4973, flag ((w && okE cd) && okCol3 cd 3)] mG) 18 := by
    opt44_reach [1551, 1552, 1553, 1554, 1555] with [flag, ite01_land]
  obtain ⟨mH, hacc, hfH, hcH⟩ := pass3f4_call hs (ret := 4973) (tail := [flag ((w && okE cd) && okCol3 cd 3)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) mG
  -- frames
  have hfAll := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf01 hfABC)
    hfDEF) hfG) hfH
  have hfG' := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf01 hfABC) hfDEF) hfG
  have hfAG : FrameExcept mA mG _ := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hfB hfC) hfDEF) hfG
  refine ⟨mH, ?_, hfAll.mono (by decide), ?_⟩
  · refine accAt_of_acc4 (m := mG) ?_ ?_ ?_ ?_ ?_ ?_ hacc
    · exact fun k hk t ht => by
        rw [word_frame hfG' (lo := ZH) (hi := ZH + 8192) (by avoids_tac) (by omega) (by omega)]
        exact hzh k hk t ht
    · exact hcw.frame hfG' (by avoids_tac)
    · exact hhp.frame hfG' (by avoids_tac)
    · intro hok t ht r hr
      rw [word_frame hfG' (lo := SB) (hi := SB + 8192) (by avoids_tac) (by omega) (by omega)]
      exact hsb hok t ht r hr
    · intro hok t ht r hr
      have hs3 : (aOf cd r 3).isSome = true := by
        unfold okCol3 at hok
        rw [List.all_eq_true] at hok
        exact hok r (List.mem_range.mpr hr)
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs3
      have := hlB (r + 1) (by omega) (by interval_cases r <;> decide) a
        (by
          interval_cases r
          · rw [I3_1, aI_seedA hcd32]; exact ha
          · rw [I3_2, aI_seedA hcd32]; exact ha
          · rw [I3_3, aI_seedA hcd32]; exact ha)
        t ht
      rw [this]; unfold aD; rw [ha]; rfl
    · intro hok t ht
      have hget : ∀ r s', r < 4 → s' < 4 → (aOf cd r s').isSome = true := fun r s' hr hs' => by
        unfold okA at hok
        rw [List.all_eq_true] at hok
        have := hok r (List.mem_range.mpr hr)
        rw [List.all_eq_true] at this
        exact this s' (List.mem_range.mpr hs')
      rw [word_frame hfAG (lo := SB + 8192) (hi := SB + 8192 + 8192) (by avoids_tac) (by omega) (by omega),
        hEw t ht]
      obtain ⟨a33, h33⟩ := Option.isSome_iff_exists.mp (hget 3 3 (by norm_num) (by norm_num))
      obtain ⟨a32, h32⟩ := Option.isSome_iff_exists.mp (hget 3 2 (by norm_num) (by norm_num))
      have e2 := hlE 2 (by norm_num) (by decide) a33
        (by unfold IE; rw [if_pos rfl, aI_seedA hcd32]; exact h33) t ht
      have e3 := hlE 3 (by norm_num) (by decide) a32
        (by unfold IE; rw [if_neg (by decide), aI_seedA hcd32]; exact h32) t ht
      refine ⟨?_, ?_⟩
      · rw [e2]; unfold aD; rw [h33]; rfl
      · rw [e3]; unfold aD; rw [h32]; rfl
  · have hR := (((((((((g1.trans hc1).trans gA).trans hmA).trans gB).trans hmB).trans gC).trans hmC).trans
      ((gK1.trans hcD).trans ((gK2.trans hcE).trans (gG.trans hcG)))).trans gP).trans hcH
    refine hR.mono (le_of_eq ?_)
    generalize Gas.gfix 2 = a; generalize Gas.kmove = c; generalize Gas.gfix 3 = d
    generalize Gas.pass3f4 = e
    omega

end MlDsaOpt44.Proofs.Ex
