import MlDsaOpt44.Fn.Fix
import MlDsaOpt44.Fn.Sponge
import MlDsaOpt44.Fn.Group.Defs
import MlDsaOpt44.Fn.Group.Squeeze
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `group`: one pure ExpandA SIMD group (WP C)

`HAVE6 := 0`, `ginit` with lane 4 computed in the prologue (`gL4n`), five
`kf4` with `blk` (`blkh` for block 4, `squeezes`, `squeeze_last`), `gfix 15`
(`SlotHead` from `slotHead_of_blocks`); the seed states are
`seedState 168 (aSeed cd k col)` (`ginit_group`, `aI_seedState`).
`group_call_aux` is `group_call` of `Fn/Group.lean` (`gsFrame = groupFrame`).
-/

namespace MlDsaOpt44.Proofs.GroupP

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- Lane-4 word built by `group`'s prologue for `rb = 0`, `amask = 15`. -/
def gL4n (col : Nat) : Nat :=
  ((col % 2 + col / 2 % 2 * 16 + col / 4 % 2 * 256 + 0x0111110000000000000000) * 15) |||
    0x200000000 ||| 0x4000000000 ||| 0x8800000000

theorem gL4n_eq {col : Nat} (hcol : col < 4) :
    gL4n col = il fun k => col + 256 * k + 0x1F * 65536 := by
  interval_cases col <;> decide +kernel

theorem gL4n_lt {col : Nat} (hcol : col < 4) : gL4n col < 2 ^ 256 := by
  interval_cases col <;> decide +kernel

theorem g_b0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (hcol : col < 4) (M : ByteArray) :
    Reach (callState s 13723 (gB col ret tail) M)
      (callState s 10911 (wd (gL4n col) :: wd 0 :: wd 15 :: wd 0 :: wd 13826 :: gB col ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  interval_cases col <;>
  opt44_reach [6168, 6169, 6170, 6171, 6172, 6173, 6174, 6175, 6176, 6177, 6178, 6179, 6180, 6181,
    6182, 6183, 6184, 6185, 6186, 6187, 6188, 6189, 6190, 6191, 6192, 6193, 6194, 6195, 6196, 6197,
    6198, 6199, 6200, 6201, 6202, 6203, 6204, 6205, 6206, 6207, 6208, 6209, 6210, 6211, 6212, 6213,
    6214, 6215, 6216, 6217, 6218, 6219, 6220, 6221, 6222, 6223, 6224] with [HAVE6, gL4n]

theorem g_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (13826 + 22 * b) (gB col ret tail) M)
      (callState s 22529 (wd (13834 + 22 * b) :: gB col ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt44_reach [6225, 6226, 6227, 6228]
  · opt44_reach [6235, 6236, 6237, 6238]
  · opt44_reach [6245, 6246, 6247, 6248]
  · opt44_reach [6255, 6256, 6257, 6258]
  · opt44_reach [6265, 6266, 6267, 6268]

theorem g_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 4 → ∀ M, Reach (callState s (13834 + 22 * b) (gB col ret tail) M)
      (callState s 9025 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (13848 + 22 * b) ::
        gB col ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt44_reach [6229, 6230, 6231, 6232, 6233, 6234] with [FL, ABUF]
  · opt44_reach [6239, 6240, 6241, 6242, 6243, 6244] with [FL, ABUF]
  · opt44_reach [6249, 6250, 6251, 6252, 6253, 6254] with [FL, ABUF]
  · opt44_reach [6259, 6260, 6261, 6262, 6263, 6264] with [FL, ABUF]

theorem g_L4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (M : ByteArray) : Reach (callState s (13834 + 22 * 4) (gB col ret tail) M)
      (callState s 10203 (wd (FL + 224 * 4) :: wd (ABUF + 1792 * 4) :: wd 13936 ::
        gB col ret tail) M) 21 := by
  opt44_reach [6269, 6270, 6271, 6272, 6273, 6274] with [FL, ABUF]

theorem g_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (M : ByteArray) :
    Reach (callState s 13936 (gB col ret tail) M)
      (callState s 10501 (wd 15 :: wd 13945 :: gB col ret tail) M) 18 := by
  opt44_reach [6275, 6276, 6277, 6278, 6279]

theorem g_E {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 13945 (ok :: gB col ret tail) M) (callState s ret (ok :: tail) M) 27 := by
  have := hr.depth
  have e : Stack.group = 256 := by decide
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [6280, 6281, 6282, 6283, 6284, 6285, 6286, 6287, 6288] with [hj]

theorem pack4_lane {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] at hx ⊢
  omega

theorem pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

/-- Seed state of slot `k` of the group of column `col`. -/
def gI (cd : ByteArray) (col k : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd k col)

theorem aI_gI {cd : ByteArray} (h32 : 32 ≤ cd.size) (col r : Nat) : aI (gI cd col r) = aOf cd r col := by
  unfold gI; rw [aI_seedState (by rw [aSeed_size h32]; norm_num)]; rfl

theorem testBit15 {r : Nat} (hr : r < 4) : Nat.testBit 15 r = true := by
  interval_cases r <;> decide

theorem gfix_flag {cd : ByteArray} (h32 : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !Nat.testBit 15 sl || (aI (gI cd col sl)).isSome) =
      (List.range 4).all fun r => (aOf cd r col).isSome := by
  simp only [aI_gI h32]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.all_cons, List.all_nil, testBit15 (show 0 < 4 by norm_num), testBit15 (show 1 < 4 by norm_num),
    testBit15 (show 2 < 4 by norm_num), testBit15 (show 3 < 4 by norm_num), Bool.not_true, Bool.false_or]

end MlDsaOpt44.Proofs.GroupP

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.GroupP

/-- **group** (`group_call` of `Fn/Group.lean`; `GroupP.gsFrame` is `groupFrame`). -/
theorem group_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {col : Nat} (hcol : col < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome) = true →
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => ((aD s.executionEnv.calldata r col)[t]!).toNat)) ∧
      FrameExcept m m' gsFrame ∧
      Call s Entry.group [wd 15, wd col, wd 0] ret tail m
        [flag ((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome)] m'
        Gas.group := by
  have htail : tail.length ≤ 768 := by
    have := hr.depth
    have e : Stack.group = 256 := by decide
    omega
  have hret := hr.small
  have h32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  -- prologue: `HAVE6 := 0`, lane 4, `ginit`
  have hb0 := g_b0 hs (tail := tail) (by omega) hcol m (ret := ret)
  have hf1 := FrameExcept.mstore m HAVE6 0
  have h61 : word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) HAVE6 = 0 :=
    word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m2, hks2, hf2, hc2⟩ := ginit_call hs (hr.callee (B' := Stack.ginit) (ret' := 13826)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num))
    (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) (keep := 0) (amult := 15) (cmult := 0)
    (l4 := gL4n col) (by norm_num) (by norm_num) (by norm_num) (gL4n_lt hcol)
  have hI : Sized4 (gI s.executionEnv.calldata col) := sized4_seedState 168 _
  have hinv0 : SqInv m m2 (gI s.executionEnv.calldata col) 0 := by
    refine ⟨fun x hx => ?_, rc4_frame hf2 (fun i hi => by grp_avoids)
      (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
      ?_, FrameExcept.of_avoid (hf1.trans hf2) (by grp_sub), fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩
    · rw [hks2 x hx, gL4n_eq hcol]
      exact ginit_group (fun y hy => by
        rw [FrameExcept.word hf1 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact hrho y hy)
        h32 hcol hx
    · rw [FrameExcept.word hf2 (by grp_avoids)]; exact h61
  -- five squeezes
  obtain ⟨m6, hinv6, hR6⟩ := squeezes hs hr (col := col) hI hinv0
    (g_K hs (by omega)) (g_L hs (by omega))
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    4 le_rfl
  obtain ⟨m7, ⟨hks7, hrc7, h67, hfr7, hblk7⟩, hR7⟩ := squeeze_last hs hr (col := col) hI hinv6
    (g_K hs (by omega) 4 (by omega) m6) (g_L4 hs (by omega))
    (by simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (by simp only [isValidJumpDest_lit])
  -- `gfix 15`
  obtain ⟨m8, hpost8, -, hf8, hc8⟩ := gfix_call hs (hr.callee (B' := Stack.gfix) (ret' := 13945)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m7 hrc7 (amask := 15) (by norm_num) 4 (by decide)
    (fun k => permN 5 (gI s.executionEnv.calldata col k)) (fun k hk => permN_size (hI k hk) 5) hks7
    (gI s.executionEnv.calldata col) h67
    (fun sl hsl _ => ⟨slotHead_of_blocks (St := fun b k => permN (b + 1) (gI s.executionEnv.calldata col k))
      hsl (fun _ _ => rfl) (fun b hb => (hblk7 b hb).1) (fun b hb => (hblk7 b hb).2), rfl⟩)
  rw [gfix_flag h32 col] at hc8
  refine ⟨m8, fun hall t ht => ?_, FrameExcept.of_avoid (hfr7.trans hf8) (by grp_sub), ?_⟩
  · rw [← pack4_lane (word_lt m8 (ABUF + 32 * t))]
    apply pack4_congr
    intro r hr4
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall r (List.mem_range.mpr hr4))
    have hD : aD s.executionEnv.calldata r col = a := by unfold aD; rw [ha]; rfl
    rw [hD]
    exact hpost8 r hr4 (testBit15 hr4) a (by rw [aI_gI h32]; exact ha) t ht
  · rw [call_iff, Entry.group]
    have h := (((((hb0.trans (call_iff.mp hc2)).trans hR6).trans hR7).trans
      (g_G hs (tail := tail) (by omega) m7)).trans (call_iff.mp hc8)).trans (g_E hs hr m8)
    refine (h.mono ?_).of_eq rfl rfl
    unfold Gas.group
    generalize Gas.ginit = a; generalize Gas.kf4 = b; generalize Gas.blk = c
    generalize Gas.blkh = d; generalize Gas.gfix 4 = e
    omega

end MlDsaOpt44.Proofs
