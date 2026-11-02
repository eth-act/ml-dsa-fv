import MlDsaOptGlam65.Main.Exp.WinA2
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The window, `KX`'s blocks 0 … 2 and calls 40, 41's slot setup (`4400 … 4601`)

`lmerge` merges `KX = (A44, A54)`'s blocks 0, 1 in place in `ABUF` (lane 0 from
blocks 0, 1, lanes 1 … 3 from blocks 2, 3) and in `FL`; `MCOPY` copies call 39's
block 4 (both slots' third squeeze) to block 2 of `ABUF` and `FL`; `kmove` puts
`tr` (blocks 0 … 13, from `IMGB`) into slot 2, `ginit` starts c̃ in slot 3.
-/

namespace MlDsaOptGlam65.Proofs.Exp

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding Rho1At ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

/-- The seeds of `KX`'s slots. -/
def IKX (cd : ByteArray) (sl : Nat) : Fips202.SpongeState := if sl = 0 then sA cd 4 4 else sA cd 5 4

/-- The flag bit of a block's flag word `g` for one slot state. -/
def flagOf (S : Fips202.SpongeState) (g : Nat) : Nat :=
  if (List.range 8).any (fun i => decide (Fips204.q ≤ cand S (8 * g + i))) then 1 else 0

/-- `KX`'s blocks `0 … n − 1` (lanes 0, 1 of `ABUF`, flag bits of `FL`). -/
def KXH (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  (∀ b, b < n → ∀ i, i < 56 → ∀ sl, sl < 2 →
    lane (word m (ABUF + 1792 * b + 32 * i)) sl = cand (permN (b + 1) (IKX cd sl)) i) ∧
  (∀ b, b < n → ∀ g, g < 7 → ∀ sl, sl < 2 →
    flagBit (word m (FL + 224 * b + 32 * g)) sl = flagOf (permN (b + 1) (IKX cd sl)) g)

theorem flagBit_flagWord (S : Nat → Fips202.SpongeState) (g : Nat) {sl : Nat} (hsl : sl < 4) :
    flagBit (flagWord S g) sl = flagOf (S sl) g := by
  unfold flagBit flagOf; exact Fix.flagWord_bit S g hsl

/-- `KX`'s slot states in the window's slot states. -/
theorem W_KX (cd : ByteArray) {b sl : Nat} (hsl : sl < 2) :
    (b < 2 → sl = 0 → W cd b sl = permN (b + 1) (IKX cd sl)) ∧
    (2 ≤ b → b < 4 → sl = 1 → W cd b sl = permN (b - 1) (IKX cd sl)) ∧
    (4 ≤ b → b < 7 → W cd b sl = permN (b - 1) (IKX cd sl)) := by
  refine ⟨fun hb h0 => ?_, fun h1 h2 h0 => ?_, fun h1 h2 => ?_⟩
  · subst h0; unfold W IKX; simp [hb]
  · subst h0; unfold W IKX; simp [show ¬ b < 2 by omega]
  · unfold W IKX
    rcases (by omega : sl = 0 ∨ sl = 1) with rfl | rfl
    · simp [show ¬ b < 2 by omega, show ¬ b < 4 by omega]
    · simp [show ¬ b < 2 by omega]

theorem KXH.frame {m m' cd : ByteArray} {n : Nat} {rs : List (Nat × Nat)} (h : KXH m cd n)
    (hf : FrameExcept m m' rs) (ha : Avoids rs ABUF (ABUF + 1792 * n)) (hb : Avoids rs FL (FL + 224 * n)) :
    KXH m' cd n :=
  ⟨fun b hb' i hi sl hsl => by
      rw [word_frame hf ha (a := ABUF + 1792 * b + 32 * i) (by omega) (by
        have : b + 1 ≤ n := hb'
        have := Nat.mul_le_mul_left 1792 this
        omega)]
      exact h.1 b hb' i hi sl hsl,
    fun b hb' g hg sl hsl => by
      rw [word_frame hf hb (a := FL + 224 * b + 32 * g) (by omega) (by
        have : b + 1 ≤ n := hb'
        have := Nat.mul_le_mul_left 224 this
        omega)]
      exact h.2 b hb' g hg sl hsl⟩

theorem wfr {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs) (a : Nat)
    (ha : Avoids rs a (a + 32)) : word m' a = word m a :=
  word_frame h ha le_rfl le_rfl

/-- Calls 40's slots: `A44`, `A54` (×3), `tr` (blocks 0 … 13), c̃'s seed. -/
def I5 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k < 2 then W cd 4 k else if k = 2 then T cd 14 else sC cd

theorem keep7 : (0x7777777777777777777777777777777777777777777777777777777777777777 : Nat) =
    il fun k => if (7 : Nat).testBit k then M64 else 0 := by decide +kernel


/-- `4400 … 4601`. -/
def cB1 : Nat := 31 + Gas.lmerge 8 + 31 + Gas.lmerge 1 + 10 + 171 + 9 + 24 + 28 + Gas.kmove + 25 + Gas.ginit

set_option maxHeartbeats 1000000 in
theorem win_B1 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hW : WinMid s.executionEnv.calldata m) (b : Bool) :
    ∃ m', KXH m' s.executionEnv.calldata 3 ∧ KS4 m' (I5 s.executionEnv.calldata) ∧
      FrameExcept m m' [(KS, KS + 800), (ABUF, FL + 1344)] ∧
      Reach (callState s 4400 [flag b] m) (callState s 4601 [flag b] m') cB1 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  -- lmerge: KX's blocks 0, 1 in ABUF
  have g1 : Reach (callState s 4400 [flag b] m)
      (callState s 18226 [wd 0x5000, wd 0x5e00, wd 0, wd 0xe00, wd 0xffffffffffffffff, wd 0, wd 4428, flag b]
        m) 31 := by
    glam65_rreach [1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556]
  obtain ⟨m1, hw1, hf1, hc1⟩ := lmerge_call hs (ret := 4428) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m
    (dst := ABUF) (a := ABUF) (b := ABUF + 3584) (ma := M64) (sl := 0) (k := 8) (by norm_num)
    (by unfold ABUF TOP; norm_num) (by unfold ABUF TOP; norm_num) (by unfold ABUF TOP; norm_num)
    (Or.inl rfl) (Or.inl (by norm_num)) (by unfold M64; norm_num) (by norm_num)
  rw [show (ABUF + 3584 + 2 ^ 256 - ABUF) % 2 ^ 256 = 0xe00 by unfold ABUF; norm_num,
    show (ABUF + 2 ^ 256 - ABUF) % 2 ^ 256 = 0 by unfold ABUF; norm_num,
    show ABUF + 448 * 8 = 0x5e00 by unfold ABUF; norm_num, show ABUF = 0x5000 from rfl,
    show M64 = 0xffffffffffffffff from rfl] at hc1
  -- lmerge: KX's flag words of blocks 0, 1
  have g2 : Reach (callState s 4428 [flag b] m1)
      (callState s 18226 [wd 0x7a00, wd 0x7bc0, wd 0, wd 0x1c0, wd 0xffffffffffffffff, wd 0, wd 4456, flag b]
        m1) 31 := by
    glam65_rreach [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566]
  obtain ⟨m2, hw2, hf2, hc2⟩ := lmerge_call hs (ret := 4456) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (dst := FL) (a := FL) (b := FL + 448) (ma := M64) (sl := 0) (k := 1) (by norm_num)
    (by unfold FL TOP; norm_num) (by unfold FL TOP; norm_num) (by unfold FL TOP; norm_num)
    (Or.inl rfl) (Or.inl (by norm_num)) (by unfold M64; norm_num) (by norm_num)
  rw [show (FL + 448 + 2 ^ 256 - FL) % 2 ^ 256 = 0x1c0 by unfold FL; norm_num,
    show (FL + 2 ^ 256 - FL) % 2 ^ 256 = 0 by unfold FL; norm_num,
    show FL + 448 * 1 = 0x7bc0 by unfold FL; norm_num, show FL = 0x7a00 from rfl,
    show M64 = 0xffffffffffffffff from rfl] at hc2
  -- block 4 to block 2
  have g3 : Reach (callState s 4456 [flag b] m2)
      (callState s 4466 [wd 0x5e00, wd 0x6c00, wd 0x700, flag b] m2) 10 := by
    glam65_rreach [1567, 1568, 1569, 1570]
  have hmc3 := reach_mcopy hs ⟨1571, by norm_num⟩ (pc := 4466) (d := 0x5e00) (src := 0x6c00) (n := 0x700)
    (rest := [flag b]) (m := m2) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by simp)
  generalize hm3 : MachineState.writeBytes m2 (MachineState.readPadded m2 0x6c00 0x700) 0x5e00 = m3 at hmc3
  have hf3 : FrameExcept m2 m3 [(0x5e00, 0x5e00 + 0x700)] := hm3 ▸ FrameExcept.mcopy m2 0x6c00 0x5e00 0x700
  have g4 : Reach (callState s 4467 [flag b] m3)
      (callState s 4475 [wd 0x7bc0, wd 0x7d80, wd 0xe0, flag b] m3) 9 := by
    glam65_rreach [1572, 1573, 1574]
  have hmc4 := reach_mcopy hs ⟨1575, by norm_num⟩ (pc := 4475) (d := 0x7bc0) (src := 0x7d80) (n := 0xe0)
    (rest := [flag b]) (m := m3) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by simp)
  generalize hm4 : MachineState.writeBytes m3 (MachineState.readPadded m3 0x7d80 0xe0) 0x7bc0 = m4 at hmc4
  have hf4 : FrameExcept m3 m4 [(0x7bc0, 0x7bc0 + 0xe0)] := hm4 ▸ FrameExcept.mcopy m3 0x7d80 0x7bc0 0xe0
  -- KX's blocks 0 … 2
  have hKX : KXH m4 s.executionEnv.calldata 3 := by
    refine ⟨fun b' hb' i hi sl hsl => ?_, fun b' hb' g hg sl hsl => ?_⟩
    · by_cases h2 : b' < 2
      · rw [wfr hf4 (ABUF + 1792 * b' + 32 * i) (by w_frame), wfr hf3 (ABUF + 1792 * b' + 32 * i) (by w_frame),
          wfr hf2 (ABUF + 1792 * b' + 32 * i) (by w_frame),
          show ABUF + 1792 * b' + 32 * i = ABUF + 32 * (56 * b' + i) by ring, hw1 _ (by omega),
          lmerge_lane0 (word_lt _ _) sl]
        rcases (by omega : sl = 0 ∨ sl = 1) with rfl | rfl
        · rw [if_pos rfl, show ABUF + 32 * (56 * b' + i) = ABUF + 1792 * b' + 32 * i by ring,
            hW.lanes b' (by omega) i hi 0 (by omega), (W_KX _ (by omega)).1 h2 rfl]
        · rw [if_neg (by omega), show ABUF + 3584 + 32 * (56 * b' + i) = ABUF + 1792 * (b' + 2) + 32 * i by ring,
            hW.lanes (b' + 2) (by omega) i hi 1 (by omega), (W_KX _ (by omega)).2.1 (by omega) (by omega) rfl,
            show b' + 2 - 1 = b' + 1 by omega]
      · obtain rfl : b' = 2 := by omega
        rw [wfr hf4 (ABUF + 1792 * 2 + 32 * i) (by w_frame), ← hm3,
          word_mcopy _ (by unfold ABUF; omega) (by unfold ABUF; omega),
          show 0x6c00 + (ABUF + 1792 * 2 + 32 * i - 0x5e00) = ABUF + 1792 * 4 + 32 * i by unfold ABUF; omega,
          wfr hf2 (ABUF + 1792 * 4 + 32 * i) (by w_frame), wfr hf1 (ABUF + 1792 * 4 + 32 * i) (by w_frame),
          hW.lanes 4 (by omega) i hi sl hsl, (W_KX _ hsl).2.2 (by omega) (by omega)]
    · rw [MlDsaOpt44.Proofs.Ex.flagBit_eq_lane _ _ (by omega)]
      by_cases h2 : b' < 2
      · rw [wfr hf4 (FL + 224 * b' + 32 * g) (by w_frame), wfr hf3 (FL + 224 * b' + 32 * g) (by w_frame),
          show FL + 224 * b' + 32 * g = FL + 32 * (7 * b' + g) by ring, hw2 _ (by omega),
          lmerge_lane0 (word_lt _ _) sl]
        rcases (by omega : sl = 0 ∨ sl = 1) with rfl | rfl
        · rw [if_pos rfl, wfr hf1 (FL + 32 * (7 * b' + g)) (by w_frame),
            show FL + 32 * (7 * b' + g) = FL + 224 * b' + 32 * g by ring,
            hW.flags b' (by omega) g hg, ← MlDsaOpt44.Proofs.Ex.flagBit_eq_lane _ _ (by omega), flagBit_flagWord _ _ (by omega),
            (W_KX _ (by omega)).1 h2 rfl]
        · rw [if_neg (by omega), wfr hf1 (FL + 448 + 32 * (7 * b' + g)) (by w_frame),
            show FL + 448 + 32 * (7 * b' + g) = FL + 224 * (b' + 2) + 32 * g by ring,
            hW.flags (b' + 2) (by omega) g hg, ← MlDsaOpt44.Proofs.Ex.flagBit_eq_lane _ _ (by omega), flagBit_flagWord _ _ (by omega),
            (W_KX _ (by omega)).2.1 (by omega) (by omega) rfl, show b' + 2 - 1 = b' + 1 by omega]
      · obtain rfl : b' = 2 := by omega
        rw [← hm4, word_mcopy _ (by unfold FL; omega) (by unfold FL; omega),
          show 0x7d80 + (FL + 224 * 2 + 32 * g - 0x7bc0) = FL + 224 * 4 + 32 * g by unfold FL; omega,
          wfr hf3 (FL + 224 * 4 + 32 * g) (by w_frame), wfr hf2 (FL + 224 * 4 + 32 * g) (by w_frame),
          wfr hf1 (FL + 224 * 4 + 32 * g) (by w_frame),
          hW.flags 4 (by omega) g hg, ← MlDsaOpt44.Proofs.Ex.flagBit_eq_lane _ _ (by omega), flagBit_flagWord _ _ (by omega),
          (W_KX _ hsl).2.2 (by omega) (by omega)]
  have hfA := ((hf1.trans hf2).trans hf3).trans hf4
  -- kmove: tr from IMGB into slot 2
  have g5 : Reach (callState s 4476 [flag b] m4)
      (callState s 18099 [wd 0x3333333333333333333333333333333333333333333333333333333333333333,
        wd 0x4444444444444444444444444444444444444444444444444444444444444444,
        wd 0, wd 2, wd 0x14d20, wd 4556, flag b] m4) 28 := by
    glam65_rreach [1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]
  obtain ⟨m5, hw5, hf5, hc5⟩ := kmove_call hs (ret := 4556) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (src := 0x14d20) (sl := 2) (sr := 0) (msk := 0x4444444444444444444444444444444444444444444444444444444444444444)
    (keep := 0x3333333333333333333333333333333333333333333333333333333333333333) (Or.inr (by unfold KS; norm_num))
    (by unfold TOP; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have himgB := hW.imgB.frame hfA (by w_frame)
  have hks4 := KS4.frame hW.ks hfA (by w_frame)
  have hrho5 := (hW.g5.rho.frame hfA (by w_frame)).frame hf5 (by w_frame)
  -- ginit: c̃ in slot 3
  have g6 : Reach (callState s 4556 [flag b] m5)
      (callState s 17659 [wd 0, wd 8, wd 0,
        wd 0x7777777777777777777777777777777777777777777777777777777777777777, wd 4601, flag b] m5) 25 := by
    glam65_rreach [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591]
  obtain ⟨m6, hks6, hf6, hR6⟩ := wginit hs hrho5
    (S := fun k => if k < 2 then W s.executionEnv.calldata 4 k else if k = 2 then W s.executionEnv.calldata 3 0
      else Fips202.emptyState)
    (I := I5 s.executionEnv.calldata) (kmask := 7) (amult := 0) (cmult := 8) (l4 := 0) (L := fun _ => 0)
    (by norm_num) (by norm_num) keep7
    (fun x hx => by
      have h1 := hw5 x hx
      simp only [KS, Nat.zero_add] at h1 ⊢
      rw [h1, ks4_il himgB hx, show 32 * x = KS + 32 * x by unfold KS; omega, hks4 x hx,
        kmove_02 _ _ (fun k _ => cpl_lt (laneOf_lt _ _)) (fun k _ => cpl_lt (laneOf_lt _ _)), keep7,
        and_keep (fun k _ => by split_ifs <;> first | exact cpl_lt (laneOf_lt _ _) | norm_num)]
      apply il_congr; intro k hk
      have b0 : Nat.testBit 7 0 = true := by decide
      have b1 : Nat.testBit 7 1 = true := by decide
      have b2 : Nat.testBit 7 2 = true := by decide
      have b3 : Nat.testBit 7 3 = false := by decide
      interval_cases k <;> simp [b0, b1, b2, b3])
    (by decide +kernel) (fun k _ => by norm_num)
    (fun k hk hb => ⟨Nat.zero_testBit k, by interval_cases k <;> first | rfl | exact absurd hb (by decide), rfl⟩)
    (fun k hk hb => by
      unfold I5
      interval_cases k <;> first | exact absurd hb (by decide) | simp
      unfold W T; simp)
    (fun k hk hb x hx => by
      obtain rfl : k = 3 := by interval_cases k <;> first | rfl | exact absurd hb (by decide)
      show _ = laneOf (seedState 136 (ctOf s.executionEnv.calldata)) x
      exact S4.freshLane_ctSeed (by unfold Z0; omega) (fun _ _ => rfl) (by decide) (by decide) rfl hx)
    g6 (by simp only [isValidJumpDest_lit]) (by norm_num)
  refine ⟨m6, hKX.frame (hf5.trans hf6) (by w_frame) (by w_frame), hks6,
    ((hfA.trans hf5).trans hf6).mono (by decide), ?_⟩
  have hR := ((((((((g1.trans hc1).trans g2).trans hc2).trans g3).trans hmc3).trans g4).trans hmc4).trans
    g5 |>.trans hc5).trans hR6
  refine hR.mono (le_of_eq ?_)
  unfold cB1
  generalize Gas.lmerge 8 = a1; generalize Gas.lmerge 1 = a2; generalize Gas.kmove = a3
  generalize Gas.ginit = a4
  omega

end MlDsaOptGlam65.Proofs.Exp
