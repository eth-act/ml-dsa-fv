import MlDsaOptGlam44.Main.Alt.MuSlot
import MlDsaOptGlam44.Main.Win.PartE
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The long-message schedule's last group (`4865 … 5071`)

`HAVE6 := 0`, `ginit [0, 12, 1, L4]` (slot 0 c̃'s seed, slot 1 empty, slots 2, 3
`A[3][3]`, `A[3][2]`), `mub0 [1]` (μ's block 0 into slot 1; with `|M| > 69` it
returns to the out-of-line `mulong` region at 6788), then five rounds `kf4` +
`blk` / `blkh`, `cext [17, 0, CB]` of c̃'s stream after rounds 0 and 1, and
`mub (136 k)` after round `k − 1` (`mub_step`: absorb block `k`, or extract μ
into `MU` when `k = nbMu`), and `gfix 12`, returning to 5071.
-/

namespace MlDsaOptGlam44.Proofs.Alt

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs
open MlDsaOptGlam44.Proofs.Ex
open MlDsaOptGlam44.Proofs.Infra

/-- μ is in `MU` once its last block was squeezed (after `mub n`). -/
def MuW (m cd : ByteArray) (n : Nat) : Prop :=
  nbMu cd ≤ n → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)

theorem MuW.frame {m m' cd : ByteArray} {n : Nat} {rs : List (Nat × Nat)} (h : MuW m cd n)
    (hf : FrameExcept m m' rs) (ha : Avoids rs MU (MU + 256)) : MuW m' cd n := fun hn x hx => by
  rw [word_frame hf ha (a := MU + 32 * x) (by omega) (by omega)]; exact h hn x hx

/-- `cext [17, 0, dst]` after round `j < 2`: block `j` of `H(c̃)`. -/
theorem cb_lane {cd : ByteArray} (hcdN : 3732 ≤ cd.size) {m m' : ByteArray} {j dst : Nat} (hj : j < 2)
    (hks : KS4 m (St cd j))
    (hw : ∀ x, x < 17 → word m' (dst + 32 * x) = cpl x (compress (word m (KS + 32 * x) / 2 ^ 0 &&& spread M64))) :
    ∀ x, x < 17 → word m' (dst + 32 * x) = le64 (cStream cd) (8 * (17 * j + x)) := fun x hx => by
  rw [hw x hx, cext_lane hks (by norm_num) (by omega), St_ne1 cd j (by decide),
    show IK cd 0 = seedState 136 (ctOf cd) from rfl, le64_cStream (le_trans (by decide) hcdN) hj hx]

theorem cb_of {cd m4 m7 m : ByteArray} {rs1 rs2 : List (Nat × Nat)}
    (hA : ∀ x, x < 17 → word m4 (CB + 32 * x) = le64 (cStream cd) (8 * (17 * 0 + x)))
    (hB : ∀ x, x < 17 → word m7 (CB + 544 + 32 * x) = le64 (cStream cd) (8 * (17 * 1 + x)))
    (hf1 : FrameExcept m4 m rs1) (ha1 : Avoids rs1 CB (CB + 544))
    (hf2 : FrameExcept m7 m rs2) (ha2 : Avoids rs2 (CB + 544) (CB + 1088)) :
    ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x) := by
  intro x hx
  by_cases h17 : x < 17
  · rw [word_frame hf1 ha1 (a := CB + 32 * x) (by omega) (by omega), hA x h17]
    congr 2; omega
  · rw [show CB + 32 * x = CB + 544 + 32 * (x - 17) by omega,
      word_frame hf2 ha2 (a := CB + 544 + 32 * (x - 17)) (by omega) (by omega), hB _ (by omega)]
    congr 2; omega

/-- `mub (136 (b + 1))` on slot 1 after round `b`. -/
theorem mub_step {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {ret : Nat}
    {tail : List UInt256} (hr : RetOK Stack.mub ret tail) {m : ByteArray} {b : Nat} (hb : b < 5)
    (hks : KS4 m (St s.executionEnv.calldata b)) (hmu : MuW m s.executionEnv.calldata b) :
    ∃ m', KS4 m' (Sb s.executionEnv.calldata (b + 1)) ∧ MuW m' s.executionEnv.calldata (b + 1) ∧
      FrameExcept m m' [(KS, KS + 800), (MU, MU + 256)] ∧
      Call s Entry.mub [wd (136 * (b + 1)), wd 1] ret tail m [] m' Gas.mub := by
  obtain ⟨m', habs, hext, hkeep, heq, hf, hc⟩ := mub_call hs hr m (sh := 1) (k := b + 1) (by norm_num)
    (by omega) (by omega) hcd
  generalize hcdv : s.executionEnv.calldata = cd at *
  have hN : nbMu cd = (66 + mlenOf cd) / 136 + 1 := rfl
  refine ⟨m', ?_, ?_, hf, hc⟩
  · by_cases hA : b + 1 < nbMu cd ∧ b + 1 < 5
    · have hw := habs (trOf cd) (trOf_size _) hA.2 (by omega)
      have h := ks4_xor_slot (sh := 1) (by norm_num) hks
        (fun x => if x < 17 then le64 (muPaddedG (trOf cd) cd) (136 * (b + 1) + 8 * x) else 0)
        (fun x _ => by split; exact le64_lt _ _; norm_num)
        (fun x hx => by
          rw [hw x hx]
          split
          · rfl
          · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
        (Fips202.xorBlock 136 (padMu cd) (136 * (b + 1)) (St cd b 1))
        (fun x _ => laneOf_absorb cd _ (St_sized cd b 1 (by norm_num)) b x)
      exact KS4.congr h fun k _ => (Sb_succ_abs cd hA k).symm
    · have hk : KS4 m' (St cd b) := by
        by_cases hP : 66 + mlenOf cd < 136 * (b + 1)
        · intro x hx; rw [hkeep hP x hx]; exact hks x hx
        · rw [heq (Or.inl ⟨by omega, by omega⟩)]; exact hks
      exact KS4.congr hk fun k _ => (Sb_succ_keep cd hA k).symm
  · intro hn x hx
    by_cases hb' : nbMu cd ≤ b
    · rw [heq (Or.inr (by omega))]; exact hmu hb' x hx
    · rw [hext (by omega) (by omega) x hx, cext_lane hks (by norm_num) (by omega),
        le64_muOf_St cd (by omega) (by omega) hx]

/-- `HAVE6 := 0`, `ginit [0, 12, 1, L4]`, `mub0 [1]` (long μ: returns to 6788). -/
theorem gK_head {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hlong : ¬ mlenOf s.executionEnv.calldata ≤ 69) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata)
    (htrl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x)) (b : Bool) :
    ∃ m2, KS4 m2 (Sb s.executionEnv.calldata 0) ∧ word m2 HAVE6 = 0 ∧
      FrameExcept m m2 [(HAVE6, HAVE6 + 32), (KS, KS + 800), (KS, KS + 800)] ∧
      Reach (callState s 4865 [flag b] m) (callState s 6788 [flag b] m2) (33 + Gas.ginit + 21 + Gas.mub0) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 3732 ≤ s.executionEnv.calldata.size := hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  have g0 : Reach (callState s 4865 [flag b] m)
      (callState s 18001 [wd 0x0ccccc000000cc000111d5, wd 1, wd 12, wd 0, wd 4894, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 33 := by
    glam44_rreach [1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 4894) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 12) (cmult := 1) (l4 := 0x0ccccc000000cc000111d5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := hrho.frame hf0 (by alt_frame)
  have hks1 : KS4 m1 (IK s.executionEnv.calldata) :=
    ks4_ginit (kmask := 0)
      (L := fun k => if k = 0 then 31 else if k = 2 then 3 + 256 * 3 + 0x1F0000
        else if k = 3 then 2 + 256 * 3 + 0x1F0000 else 0)
      (ρ := fun x => le64 s.executionEnv.calldata (8 * x))
      (c := fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) (S := IK s.executionEnv.calldata)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split_ifs <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        interval_cases k
        · show _ = laneOf (seedState 136 (ctOf s.executionEnv.calldata)) x
          exact freshLane_ctSeed (le_trans (by decide) hcdN) (fun _ _ => rfl) (by decide) (by decide)
            (by simp) hx
        · show _ = laneOf Fips202.emptyState x
          exact freshLane_zero (by decide) (by decide) (by simp) x
        · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 3 3)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by simp) hx
        · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 3 2)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by simp) hx)
      hg
  have g1 : Reach (callState s 4894 [flag b] m1)
      (callState s 19730 [wd 1, wd 4907, wd 6788, flag b] m1) 21 := by
    glam44_rreach [1612, 1613, 1614, 1615, 1616, 1617]
  obtain ⟨m2, hpost, hf2, hc2⟩ := mub0_call hs (rl := 6788) (rs := 4907) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num))
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (sh := 1) (by norm_num) hcdN
  rw [if_neg hlong] at hc2
  have htrl1 : ∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x) :=
    fun x hx => by
      rw [word_frame (hf0.trans hf1) (lo := TRL) (hi := TRL + 256) (by alt_frame) (by omega) (by omega)]
      exact htrl x hx
  have hw := hpost (trOf s.executionEnv.calldata) (trOf_size _) htrl1
  have hks2 : KS4 m2 (Sb s.executionEnv.calldata 0) := by
    have h := ks4_xor_slot (sh := 1) (by norm_num) hks1
      (fun x => if x < 17 then le64 (mu0Bytes (trOf s.executionEnv.calldata) s.executionEnv.calldata) (8 * x)
        else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (muT s.executionEnv.calldata 0) (fun x _ => by
        rw [laneOf_muT0, show IK s.executionEnv.calldata 1 = Fips202.emptyState from rfl]
        by_cases h : x < 17
        · simp only [h, if_true]; rw [le64_mu0Bytes hcdN h]
        · simp only [h, if_false])
    exact KS4.congr h fun k _ => by unfold Sb; rfl
  refine ⟨m2, hks2, ?_, (hf0.trans hf1).trans hf2, ((g0.trans hc1).trans g1).trans hc2⟩
  rw [word_frame (hf1.trans hf2) (lo := HAVE6) (hi := HAVE6 + 32) (by alt_frame) le_rfl le_rfl]
  exact h60

/-- Glue, rounds, `cext`s and `mub`s of the `mulong` region (6788 → `gfix [12]`). -/
def cLong : Nat :=
  15 + Gas.kf4 + 21 + Gas.blk + (23 + Gas.cext 17) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blk) +
    (23 + Gas.cext 17) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blk) + (21 + Gas.mub) +
    (15 + Gas.kf4 + 21 + Gas.blk) + (21 + Gas.mub) + (15 + Gas.kf4 + 21 + Gas.blkh) + (21 + Gas.mub) + 18

/-- At `gfix`'s entry. -/
structure KMid (cd m0 m : ByteArray) : Prop where
  ks : KS4 m (St cd 4)
  hb : HBlocks m ABUF FL (St cd) 5
  rc : RC4Table m
  h6 : word m HAVE6 = 0
  cb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 (cStream cd) (8 * x)
  mu : MuW m cd 5
  fr : FrameExcept m0 m [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (CB, CB + 1088), (MU, MU + 256)]

set_option maxHeartbeats 1000000 in
theorem gK_long {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} {b : Bool} (hrc : RC4Table m)
    (hks : KS4 m (Sb s.executionEnv.calldata 0)) (h6 : word m HAVE6 = 0) :
    ∃ m', KMid s.executionEnv.calldata m m' ∧
      Reach (callState s 6788 [flag b] m) (callState s 17591 [wd 12, wd 5071, flag b] m') cLong := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 3732 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have htl : [flag b].length ≤ 8 := by simp
  have hret : ∀ r : Nat, Decode.isValidJumpDest optBytecode r = true → r < 2 ^ 16 →
      RetOK Stack.mub r [flag b] := fun r hj hr => retOK_main (by decide) (by simp) hj hr
  -- round 0
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs htl (stk := [flag b]) (m := m)
    (pc0 := 6788) (r1 := 6796) (r2 := 6810) (c1 := 15) (c2 := 21) (b := 0) (by norm_num) bufOK_abuf
    (by glam44_rreach [2491, 2492, 2493, 2494])
    (fun _ => by glam44_rreach [2495, 2496, 2497, 2498, 2499, 2500] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc (Sb_sized _ 0) hks (HBlocks.zero _ _ _ _) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks3 : KS4 m3 (St s.executionEnv.calldata 0) := KS4.congr hks3' fun _ _ => rfl
  -- H(c̃) block 0
  have gC1 : Reach (callState s 6810 [flag b] m3)
      (callState s 19241 [wd 17, wd 0, wd CB, wd 6824, flag b] m3) 23 := by
    glam44_rreach [2501, 2502, 2503, 2504, 2505, 2506, 2507] with [CB]
  obtain ⟨m4, hcb1, hf4, hc4⟩ := cext_call hs (ret := 6824) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (dst := CB) (sh := 0) (n := 17) (by norm_num) (by norm_num) (by norm_num) (by unfold KS CB; norm_num)
    (by unfold CB TOP; norm_num)
  have hcbA := cb_lane hcdN (by norm_num) hks3 hcb1
  have hks4 := KS4.frame hks3 hf4 (by alt_frame)
  have hrc4 := RC4Table.frame hrc3 hf4 (by alt_frame)
  have hB4 := hB3.frame hf4 (by alt_frame) (by alt_frame)
  -- mub 136
  have gM1 : Reach (callState s 6824 [flag b] m4)
      (callState s 20094 [wd (136 * (0 + 1)), wd 1, wd 6836, flag b] m4) 21 := by
    glam44_rreach [2508, 2509, 2510, 2511, 2512, 2513]
  obtain ⟨m5, hks5, hmu5, hf5, hc5⟩ := mub_step hs hcdN (hret 6836 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 0) (by norm_num) hks4 (fun h => absurd h (by unfold nbMu; omega))
  have hrc5 := RC4Table.frame hrc4 hf5 (by alt_frame)
  have hB5 := hB4.frame hf5 (by alt_frame) (by alt_frame)
  -- round 1
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kb_round hs htl (stk := [flag b]) (m := m5)
    (pc0 := 6836) (r1 := 6844) (r2 := 6858) (c1 := 15) (c2 := 21) (b := 1) (by norm_num) bufOK_abuf
    (by glam44_rreach [2514, 2515, 2516, 2517])
    (fun _ => by glam44_rreach [2518, 2519, 2520, 2521, 2522, 2523] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (Sb_sized _ 1) hks5 hB5 (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks6 : KS4 m6 (St s.executionEnv.calldata 1) := KS4.congr hks6' fun _ _ => rfl
  have hmu6 := hmu5.frame hf6 (by alt_frame)
  -- H(c̃) block 1
  have gC3 : Reach (callState s 6858 [flag b] m6)
      (callState s 19241 [wd 17, wd 0, wd (CB + 544), wd 6872, flag b] m6) 23 := by
    glam44_rreach [2524, 2525, 2526, 2527, 2528, 2529, 2530] with [CB]
  obtain ⟨m7, hcb2, hf7, hc7⟩ := cext_call hs (ret := 6872) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6
    (dst := CB + 544) (sh := 0) (n := 17) (by norm_num) (by norm_num) (by norm_num)
    (by unfold KS CB; norm_num) (by unfold CB TOP; norm_num)
  have hcbB := cb_lane hcdN (by norm_num) hks6 hcb2
  have hks7 := KS4.frame hks6 hf7 (by alt_frame)
  have hrc7 := RC4Table.frame hrc6 hf7 (by alt_frame)
  have hB7 := hB6.frame hf7 (by alt_frame) (by alt_frame)
  have hmu7 := hmu6.frame hf7 (by alt_frame)
  -- mub 272
  have gM2 : Reach (callState s 6872 [flag b] m7)
      (callState s 20094 [wd (136 * (1 + 1)), wd 1, wd 6885, flag b] m7) 21 := by
    glam44_rreach [2531, 2532, 2533, 2534, 2535, 2536]
  obtain ⟨m8, hks8, hmu8, hf8, hc8⟩ := mub_step hs hcdN (hret 6885 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 1) (by norm_num) hks7 hmu7
  -- round 2
  obtain ⟨m9, hks9', hB9, hrc9, hf9, hR9⟩ := kb_round hs htl (stk := [flag b]) (m := m8)
    (pc0 := 6885) (r1 := 6893) (r2 := 6907) (c1 := 15) (c2 := 21) (b := 2) (by norm_num) bufOK_abuf
    (by glam44_rreach [2537, 2538, 2539, 2540])
    (fun _ => by glam44_rreach [2541, 2542, 2543, 2544, 2545, 2546] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc7 hf8 (by alt_frame)) (Sb_sized _ 2) hks8 (hB7.frame hf8 (by alt_frame) (by alt_frame))
    (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks9 : KS4 m9 (St s.executionEnv.calldata 2) := KS4.congr hks9' fun _ _ => rfl
  -- mub 408
  have gM3 : Reach (callState s 6907 [flag b] m9)
      (callState s 20094 [wd (136 * (2 + 1)), wd 1, wd 6920, flag b] m9) 21 := by
    glam44_rreach [2547, 2548, 2549, 2550, 2551, 2552]
  obtain ⟨m10, hks10, hmu10, hf10, hc10⟩ := mub_step hs hcdN (hret 6920 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 2) (by norm_num) hks9 (hmu8.frame hf9 (by alt_frame))
  -- round 3
  obtain ⟨m11, hks11', hB11, hrc11, hf11, hR11⟩ := kb_round hs htl (stk := [flag b]) (m := m10)
    (pc0 := 6920) (r1 := 6928) (r2 := 6942) (c1 := 15) (c2 := 21) (b := 3) (by norm_num) bufOK_abuf
    (by glam44_rreach [2553, 2554, 2555, 2556])
    (fun _ => by glam44_rreach [2557, 2558, 2559, 2560, 2561, 2562] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc9 hf10 (by alt_frame)) (Sb_sized _ 3) hks10
    (hB9.frame hf10 (by alt_frame) (by alt_frame)) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks11 : KS4 m11 (St s.executionEnv.calldata 3) := KS4.congr hks11' fun _ _ => rfl
  -- mub 544
  have gM4 : Reach (callState s 6942 [flag b] m11)
      (callState s 20094 [wd (136 * (3 + 1)), wd 1, wd 6955, flag b] m11) 21 := by
    glam44_rreach [2563, 2564, 2565, 2566, 2567, 2568]
  obtain ⟨m12, hks12, hmu12, hf12, hc12⟩ := mub_step hs hcdN (hret 6955 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 3) (by norm_num) hks11 (hmu10.frame hf11 (by alt_frame))
  -- round 4
  obtain ⟨m13, hks13', hB13, hrc13, hf13, hR13⟩ := kbh_round hs htl (stk := [flag b]) (m := m12)
    (pc0 := 6955) (r1 := 6963) (r2 := 6977) (c1 := 15) (c2 := 21) bufOK_abuf
    (by glam44_rreach [2569, 2570, 2571, 2572])
    (fun _ => by glam44_rreach [2573, 2574, 2575, 2576, 2577, 2578] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    (RC4Table.frame hrc11 hf12 (by alt_frame)) (Sb_sized _ 4) hks12
    (hB11.frame hf12 (by alt_frame) (by alt_frame)) (St := St s.executionEnv.calldata) (fun _ _ => rfl)
  have hks13 : KS4 m13 (St s.executionEnv.calldata 4) := KS4.congr hks13' fun _ _ => rfl
  -- mub 680
  have gM5 : Reach (callState s 6977 [flag b] m13)
      (callState s 20094 [wd (136 * (4 + 1)), wd 1, wd 6990, flag b] m13) 21 := by
    glam44_rreach [2579, 2580, 2581, 2582, 2583, 2584]
  obtain ⟨m14, hks14, hmu14, hf14, hc14⟩ := mub_step hs hcdN (hret 6990 (by simp only [isValidJumpDest_lit])
    (by norm_num)) (b := 4) (by norm_num) hks13 (hmu12.frame hf13 (by alt_frame))
  have gG : Reach (callState s 6990 [flag b] m14) (callState s 17591 [wd 12, wd 5071, flag b] m14) 18 := by
    glam44_rreach [2585, 2586, 2587, 2588, 2589]
  -- frames
  have hfA := (((((((((((hf3.trans hf4).trans hf5).trans hf6).trans hf7).trans hf8).trans hf9).trans
    hf10).trans hf11).trans hf12).trans hf13).trans hf14)
  refine ⟨m14, ⟨KS4.congr hks14 fun k _ => Sb_succ_keep _ (by omega) k,
    hB13.frame hf14 (by alt_frame) (by alt_frame), RC4Table.frame hrc13 hf14 (by alt_frame), ?_, ?_, hmu14,
    hfA.mono (by decide)⟩, ?_⟩
  · rw [word_frame hfA (lo := HAVE6) (hi := HAVE6 + 32) (by alt_frame) le_rfl le_rfl]; exact h6
  · exact cb_of hcbA hcbB (((((((((hf5.trans hf6).trans hf7).trans hf8).trans hf9).trans hf10).trans
      hf11).trans hf12).trans hf13).trans hf14) (by alt_frame)
      (((((((hf8.trans hf9).trans hf10).trans hf11).trans hf12).trans hf13).trans hf14)) (by alt_frame)
  · have hR := (((((((((((((((((hR3.trans gC1).trans hc4).trans gM1).trans hc5).trans hR6).trans gC3).trans
      hc7).trans gM2).trans hc8).trans hR9).trans gM3).trans hc10).trans hR11).trans gM4).trans hc12).trans
      hR13).trans gM5).trans hc14
    refine (hR.trans gG).mono (le_of_eq ?_)
    unfold cLong
    generalize Gas.kf4 = a1; generalize Gas.blk = a2; generalize Gas.blkh = a3
    generalize Gas.cext 17 = a4; generalize Gas.mub = a5
    omega

/-- The last group's cost (4865 → 5071). -/
def costK : Nat := 33 + Gas.ginit + 21 + Gas.mub0 + cLong + Gas.gfix 2

theorem IK_two (cd : ByteArray) : IK cd 2 = seedA cd 3 3 := by
  unfold IK; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem IK_three (cd : ByteArray) : IK cd 3 = seedA cd 3 2 := by
  unfold IK; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem IE_IK (cd : ByteArray) {sl : Nat} (h : sl = 2 ∨ sl = 3) : IE cd sl = IK cd sl := by
  rcases h with rfl | rfl
  · rw [IK_two]; unfold IE; rw [if_pos rfl]
  · rw [IK_three]; unfold IE; rw [if_neg (by decide)]

/-- The last group of the long-message schedule, `4865 … 5071` (to `gfix 12`'s return). -/
theorem grpK {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hlong : ¬ mlenOf s.executionEnv.calldata ≤ 69) {m : ByteArray} {b : Bool} (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata)
    (htrl : ∀ x, x < 8 → word m (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x)) :
    ∃ m', (okE s.executionEnv.calldata = true → ∀ t, t < 256 →
        lane (word m' (ABUF + 32 * t)) 2 = ((aD s.executionEnv.calldata 3 3)[t]!).toNat ∧
        lane (word m' (ABUF + 32 * t)) 3 = ((aD s.executionEnv.calldata 3 2)[t]!).toNat) ∧
      (mlenOf s.executionEnv.calldata ≤ 613 →
        ∀ x, x < 8 → word m' (MU + 32 * x) = le64 (muOf s.executionEnv.calldata) (8 * x)) ∧
      (613 < mlenOf s.executionEnv.calldata → ∃ S : Nat → Fips202.SpongeState, Sized4 S ∧ KS4 m' S ∧
        S 1 = absorbPre 136 (padMu s.executionEnv.calldata) 5) ∧
      (∀ x, x < 34 → word m' (CB + 32 * x) = le64 (cStream s.executionEnv.calldata) (8 * x)) ∧
      FrameExcept m m' [(HAVE6, HAVE6 + 32), (KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344),
        (CB, CB + 1088), (MU, MU + 256), (BK, BK + 800)] ∧
      Reach (callState s 4865 [flag b] m)
        (callState s 5071 [flag (okE s.executionEnv.calldata), flag b] m') costK := by
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by have : 3732 ≤ _ := hcd; omega
  obtain ⟨m2, hks2, h62, hf2, hR2⟩ := gK_head hs hcd hlong hrho htrl b
  obtain ⟨m10, hM, hR10⟩ := gK_long hs hcd (b := b) (RC4Table.frame hrc hf2 (by alt_frame)) hks2 h62
  obtain ⟨m11, hlanes, hks11, hf11, hc11⟩ := gfix_call hs (ret := 5071) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m10 hM.rc
    (amask := 12) (by norm_num) 2 (by decide) (St s.executionEnv.calldata 4) (St_sized _ 4) hM.ks
    (IE s.executionEnv.calldata) hM.h6
    (fun sl hsl hbit => by
      have h23 : sl = 2 ∨ sl = 3 := by
        interval_cases sl
        · exact absurd hbit (by decide)
        · exact absurd hbit (by decide)
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [IE_IK _ h23]
      exact ⟨hM.hb.slotHead hsl fun b' _ => St_ne1 _ b' (by omega), St_ne1 _ 4 (by omega)⟩)
  rw [flag_E hcd32] at hc11
  have hfm := hM.fr.trans hf11
  refine ⟨m11, fun hok t ht => ?_, fun h613 x hx => ?_, fun h613 => ?_, fun x hx => ?_,
    (hf2.trans hfm).mono (by decide), (hR2.trans hR10).trans hc11⟩
  · have h33 : (aOf s.executionEnv.calldata 3 3).isSome = true := by
      unfold okE at hok; simp only [Bool.and_eq_true] at hok; exact hok.1
    have h32 : (aOf s.executionEnv.calldata 3 2).isSome = true := by
      unfold okE at hok; simp only [Bool.and_eq_true] at hok; exact hok.2
    obtain ⟨a3, ha3⟩ := Option.isSome_iff_exists.mp h33
    obtain ⟨a2, ha2⟩ := Option.isSome_iff_exists.mp h32
    refine ⟨?_, ?_⟩
    · rw [hlanes 2 (by norm_num) (by decide) a3 (by rw [IE_IK _ (Or.inl rfl), IK_two, aI_seedA hcd32]; exact ha3) t ht]
      unfold aD; rw [ha3]; rfl
    · rw [hlanes 3 (by norm_num) (by decide) a2 (by rw [IE_IK _ (Or.inr rfl), IK_three, aI_seedA hcd32]; exact ha2) t ht]
      unfold aD; rw [ha2]; rfl
  · rw [word_frame hf11 (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by alt_frame) (by omega) (by omega)]
    exact hM.mu (by unfold nbMu; omega) x hx
  · refine ⟨St s.executionEnv.calldata 4, St_sized _ 4, hks11, ?_⟩
    rw [St_one, muT_absorb _ (by unfold nbMu; omega) (by norm_num)]
  · rw [word_frame hf11 (a := CB + 32 * x) (lo := CB) (hi := CB + 1088) (by alt_frame) (by omega) (by omega)]
    exact hM.cb x hx

end MlDsaOptGlam44.Proofs.Alt
