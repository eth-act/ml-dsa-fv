import MlDsaOpt44.Fn.Sponge
import MlDsaOpt44.Fn.Group.Squeeze
import MlDsaOpt44.Fn.Group.Pass3
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `group`: one pure ExpandA SIMD group (WP6)

`ginit` with lane 4 computed in the prologue (`gL4n`), five `kf4` + `blk`
(`squeezes`), `gfix 15`, `pass3`; the seed states are
`seedState 168 (aSeed cd k col)` (`ginit_group`, `aI_seedState`).
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
    Reach (callState s 13659 (gB col ret tail) M)
      (callState s 11084 (wd (gL4n col) :: wd 0 :: wd 15 :: wd 0 :: wd 13762 :: gB col ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  interval_cases col <;>
  opt44_reach [6040, 6041, 6042, 6043, 6044, 6045, 6046, 6047, 6048, 6049, 6050, 6051, 6052, 6053,
    6054, 6055, 6056, 6057, 6058, 6059, 6060, 6061, 6062, 6063, 6064, 6065, 6066, 6067, 6068, 6069,
    6070, 6071, 6072, 6073, 6074, 6075, 6076, 6077, 6078, 6079, 6080, 6081, 6082, 6083, 6084, 6085,
    6086, 6087, 6088, 6089, 6090, 6091, 6092, 6093, 6094, 6095, 6096] with [HAVE6, gL4n]

theorem g_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (13762 + 22 * b) (gB col ret tail) M)
      (callState s 21570 (wd (13770 + 22 * b) :: gB col ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · opt44_reach [6097, 6098, 6099, 6100]
  · opt44_reach [6107, 6108, 6109, 6110]
  · opt44_reach [6117, 6118, 6119, 6120]
  · opt44_reach [6127, 6128, 6129, 6130]
  · opt44_reach [6137, 6138, 6139, 6140]

theorem g_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (13770 + 22 * b) (gB col ret tail) M)
      (callState s 8887 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (13784 + 22 * b) ::
        gB col ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · opt44_reach [6101, 6102, 6103, 6104, 6105, 6106] with [FL, ABUF]
  · opt44_reach [6111, 6112, 6113, 6114, 6115, 6116] with [FL, ABUF]
  · opt44_reach [6121, 6122, 6123, 6124, 6125, 6126] with [FL, ABUF]
  · opt44_reach [6131, 6132, 6133, 6134, 6135, 6136] with [FL, ABUF]
  · opt44_reach [6141, 6142, 6143, 6144, 6145, 6146] with [FL, ABUF]

theorem g_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (M : ByteArray) :
    Reach (callState s 13872 (gB col ret tail) M)
      (callState s 10754 (wd 15 :: wd 13881 :: gB col ret tail) M) 18 := by
  opt44_reach [6147, 6148, 6149, 6150, 6151]

theorem g_P {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} {ok : UInt256} (hcol : col < 4) (M : ByteArray) :
    Reach (callState s 13881 (ok :: gB col ret tail) M)
      (callState s 10062 (wd (64 * col) :: wd ZH :: wd ACC :: wd 13915 :: ok :: gB col ret tail) M) 66 := by
  opt44_reach [6152, 6153, 6154, 6155, 6156, 6157, 6158, 6159, 6160, 6161, 6162, 6163, 6164, 6165,
    6166, 6167, 6168, 6169, 6170, 6171, 6172] with [ZH, ACC]
  rw [Nat.and_comm, show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hcol, Nat.div_eq_of_lt hcol, Nat.mul_comm]
  simp

theorem g_E {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 13915 (ok :: gB col ret tail) M) (callState s 13923 (wd ret :: ok :: tail) M) 19 := by
  opt44_reach [6173, 6174, 6175, 6176, 6177, 6178, 6179, 6180]

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

theorem group_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 s.executionEnv.calldata (8 * x)) ∧
      word m (RHO1 + 32 * (4 + x)) = spread (le64 s.executionEnv.calldata (CTOFF + 8 * x)))
    {col : Nat} (hcol : col < 4) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome) = true →
        ∀ t, t < 256 → word m' (ACC + 32 * t) =
          (word m (ACC + 32 * t) +
            pack4 (fun r => ((aD s.executionEnv.calldata r col)[t]!).toNat) *
              lane (word m (ZH + 32 * t)) col) % 2 ^ 256) ∧
      FrameExcept m m' (gsFrame ++ [(ACC, ACC + 8192)]) ∧
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
  obtain ⟨m2, hks2, hf2, hc2⟩ := ginit_call hs (hr.callee (B' := Stack.ginit) (ret' := 13762)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide) (by simp only [isValidJumpDest_lit]) (by norm_num))
    (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) (keep := 0) (amult := 15) (cmult := 0)
    (l4 := gL4n col) (by norm_num) (by norm_num) (by norm_num) (gL4n_lt hcol)
  have hI : Sized4 (gI s.executionEnv.calldata col) := sized4_seedState 168 _
  have hinv0 : SqInv m m2 (gI s.executionEnv.calldata col) 0 := by
    refine ⟨fun x hx => ?_, rc4_frame hf2 (fun i hi => by grp_avoids) (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
      ?_, FrameExcept.of_avoid (hf1.trans hf2) (by grp_sub), fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩
    · rw [hks2 x hx, gL4n_eq hcol]
      exact ginit_group (fun y hy => by
        rw [FrameExcept.word hf1 (by grp_avoids), FrameExcept.word hf1 (by grp_avoids)]; exact hrho y hy)
        h32 hcol hx
    · rw [FrameExcept.word hf2 (by grp_avoids)]; exact h61
  -- five squeezes
  obtain ⟨m7, ⟨hks7, hrc7, h67, hfr7, hblk7⟩, hR7⟩ := squeezes hs hr (col := col) hI hinv0
    (g_K hs (by omega)) (g_L hs (by omega))
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    5 le_rfl
  have hp := pending_of_blocks' (m := m7) (I := gI s.executionEnv.calldata col)
    (fun b hb => (hblk7 b hb).1) (fun b hb => (hblk7 b hb).2) h67
  -- `gfix 15`
  obtain ⟨m8, hpost8, -, hf8, hc8⟩ := gfix_call hs (hr.callee (B' := Stack.gfix) (ret' := 13881)
    (extra := [wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m7 hrc7 (amask := 15) (by norm_num) 4 (by decide)
    (fun k => permN 5 (gI s.executionEnv.calldata col k)) (fun k hk => permN_size (hI k hk) 5) hks7
    (gI s.executionEnv.calldata col) h67 (fun sl hsl _ => hp sl hsl)
  rw [gfix_flag h32 col] at hc8
  -- `pass3`
  obtain ⟨m9, hpost9, hf9, hc9⟩ := pass3_reach hs (hr.callee (B' := Stack.pass3) (ret' := 13915)
    (extra := [flag ((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome),
      wd 15, wd col, wd 0, wd ret]) (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m8 hcol
  have hfr8 : FrameExcept m m8 gsFrame := FrameExcept.of_avoid (hfr7.trans hf8) (by grp_sub)
  refine ⟨m9, fun hall t ht => ?_, FrameExcept.of_avoid (hfr8.trans hf9) (by grp_sub), ?_⟩
  · rw [hpost9 t ht, FrameExcept.word hfr8 (a := ACC + 32 * t) (by grp_avoids),
      FrameExcept.word hfr8 (a := ZH + 32 * t) (by grp_avoids),
      ← pack4_lane (word_lt m8 (ABUF + 32 * t))]
    congr 3
    apply pack4_congr
    intro r hr4
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall r (List.mem_range.mpr hr4))
    have hD : aD s.executionEnv.calldata r col = a := by unfold aD; rw [ha]; rfl
    rw [hD]
    exact hpost8 r hr4 (testBit15 hr4) a (by rw [aI_gI h32]; exact ha) t ht
  · rw [call_iff, Entry.group]
    have hfin := reach_ret hs 6181 m9 (pc := 13923) (tail := flag ((List.range 4).all fun r =>
        (aOf s.executionEnv.calldata r col).isSome) :: tail)
      (by decide +kernel) (by simp only [finVal_lit, instrAt_lit]) (by simp only [finVal_lit, pcAt_lit])
      (by norm_num) hr.jumpdest hret (by simp only [List.length_cons]; omega)
    have h := (((((((hb0.trans hc2).trans hR7).trans (g_G hs (tail := tail) (by omega) m7)).trans hc8).trans
      (g_P hs (tail := tail) (by omega) hcol m8)).trans hc9).trans (g_E hs (tail := tail) (by omega) m9)).trans hfin
    refine (h.mono ?_).of_eq rfl rfl
    unfold Gas.group
    omega

end MlDsaOpt44.Proofs.GroupP
