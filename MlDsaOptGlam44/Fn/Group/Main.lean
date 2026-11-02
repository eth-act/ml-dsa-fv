import MlDsaOptGlam44.Fn.Fix
import MlDsaOptGlam44.Fn.Sponge
import MlDsaOpt44.Fn.Group.Defs
import MlDsaOptGlam44.Fn.Group.Squeeze
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Group/Main.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
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

namespace MlDsaOptGlam44.Proofs.GroupP

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

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
    Reach (callState s 20814 (gB col ret tail) M)
      (callState s 18001 (wd (gL4n col) :: wd 0 :: wd 15 :: wd 0 :: wd 20917 :: gB col ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  interval_cases col <;>
  glam44_rreach [8955, 8956, 8957, 8958, 8959, 8960, 8961, 8962, 8963, 8964, 8965, 8966, 8967, 8968,
    8969, 8970, 8971, 8972, 8973, 8974, 8975, 8976, 8977, 8978, 8979, 8980, 8981, 8982, 8983, 8984,
    8985, 8986, 8987, 8988, 8989, 8990, 8991, 8992, 8993, 8994, 8995, 8996, 8997, 8998, 8999, 9000,
    9001, 9002, 9003, 9004, 9005, 9006, 9007, 9008, 9009, 9010, 9011] with [HAVE6, gL4n]

theorem g_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (20917 + 22 * b) (gB col ret tail) M)
      (callState s 42887 (wd (20925 + 22 * b) :: gB col ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · glam44_rreach [9012, 9013, 9014, 9015]
  · glam44_rreach [9022, 9023, 9024, 9025]
  · glam44_rreach [9032, 9033, 9034, 9035]
  · glam44_rreach [9042, 9043, 9044, 9045]
  · glam44_rreach [9052, 9053, 9054, 9055]

theorem g_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} : ∀ b, b < 4 → ∀ M, Reach (callState s (20925 + 22 * b) (gB col ret tail) M)
      (callState s 10481 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (20939 + 22 * b) ::
        gB col ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · glam44_rreach [9016, 9017, 9018, 9019, 9020, 9021] with [FL, ABUF]
  · glam44_rreach [9026, 9027, 9028, 9029, 9030, 9031] with [FL, ABUF]
  · glam44_rreach [9036, 9037, 9038, 9039, 9040, 9041] with [FL, ABUF]
  · glam44_rreach [9046, 9047, 9048, 9049, 9050, 9051] with [FL, ABUF]

theorem g_L4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (M : ByteArray) : Reach (callState s (20925 + 22 * 4) (gB col ret tail) M)
      (callState s 10487 (wd (FL + 224 * 4) :: wd (ABUF + 1792 * 4) :: wd 21027 ::
        gB col ret tail) M) 21 := by
  glam44_rreach [9056, 9057, 9058, 9059, 9060, 9061] with [FL, ABUF]

theorem g_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {col ret : Nat} (M : ByteArray) :
    Reach (callState s 21027 (gB col ret tail) M)
      (callState s 17591 (wd 15 :: wd 21036 :: gB col ret tail) M) 18 := by
  glam44_rreach [9062, 9063, 9064, 9065, 9066]

theorem g_E {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {col : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 21036 (ok :: gB col ret tail) M) (callState s ret (ok :: tail) M) 27 := by
  have := hr.depth
  have e : Stack.group = 266 := by decide
  have hret := hr.small
  have hj := hr.jumpdest
  glam44_rreach [9067, 9068, 9069, 9070, 9071, 9072, 9073, 9074, 9075] with [hj]

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

end MlDsaOptGlam44.Proofs.GroupP

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra
open MlDsaOptGlam44.Proofs.GroupP

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
  have htail : tail.length ≤ 758 := by
    have := hr.depth
    have e : Stack.group = 266 := by decide
    omega
  have hret := hr.small
  have h32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  -- prologue: `HAVE6 := 0`, lane 4, `ginit`
  have hb0 := g_b0 hs (tail := tail) (by omega) hcol m (ret := ret)
  have hf1 := FrameExcept.mstore m HAVE6 0
  have h61 : word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) HAVE6 = 0 :=
    word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m2, hks2, hf2, hc2⟩ := ginit_call hs (hr.callee (B' := Stack.ginit) (ret' := 20917)
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
  obtain ⟨m8, hpost8, -, hf8, hc8⟩ := gfix_call hs (hr.callee (B' := Stack.gfix) (ret' := 21036)
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

end MlDsaOptGlam44.Proofs
