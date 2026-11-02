import MlDsaOptGlam65.Fn.Fix
import MlDsaOptGlam65.Fn.Ginit.Call
import MlDsaOpt65.Fn.Group.Seed
import MlDsaOpt65.Fn.Group.Defs
import MlDsaOptGlam65.Fn.GroupV4.Squeeze
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/GroupV4/Main.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Group/Main.lean` by `scripts/proofgen_port.py 65` --path Fn/Group/=Fn/GroupV4/; hand adjustments are marked `-- port:`. -/
-- port: `amask`, `col < 8`, `rb < 2` symbolic (prologue and seeds from `Fn/Group/Seed.lean`,
-- `g1_b0` of the v3 port); inactive lanes kept by `gfix` (raw candidates below `2^23`).
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `group` (ML-DSA-65, v4): one pure ExpandA SIMD group

`HAVE6 := 0`, `ginit` with lane 4 computed in the prologue (`gL4`), five
`kf4` with `blk` (`blkh` for block 4), `gfix amask` (`SlotHead` from
`slotHead_of_blocks`; inactive lanes keep their raw candidates).
`group_call_aux` is `group_call` of `Fn/Group.lean`.
-/

namespace MlDsaOptGlam65.Proofs.GroupV4

open MlDsaOpt65.Proofs

open MlDsaOptGlam65.Proofs.GroupV4
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs.Infra

theorem g_b0 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (ha : amask < 16) (hcol : col < 8) (hrb : rb < 2) (M : ByteArray) :
    Reach (callState s 20575 (gB amask col rb ret tail) M)
      (callState s 17659 (wd (GroupP.gL4 amask col rb) :: wd 0 :: wd 15 :: wd 0 :: wd 20678 ::
        gB amask col rb ret tail)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 179 := by
  have hsz := hs.sized; simp only [memWords] at hsz
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have ha' : amask % 2 ^ 256 = amask := Nat.mod_eq_of_lt (by omega)
  have hc' : col % 2 ^ 256 = col := Nat.mod_eq_of_lt (by omega)
  have hr' : rb % 2 ^ 256 = rb := Nat.mod_eq_of_lt (by omega)
  glam65_rreach [8948, 8949, 8950, 8951, 8952, 8953, 8954, 8955, 8956, 8957, 8958, 8959, 8960, 8961,
    8962, 8963, 8964, 8965, 8966, 8967, 8968, 8969, 8970, 8971, 8972, 8973, 8974, 8975, 8976, 8977,
    8978, 8979, 8980, 8981, 8982, 8983, 8984, 8985, 8986, 8987, 8988, 8989, 8990, 8991, 8992, 8993,
    8994, 8995, 8996, 8997, 8998, 8999, 9000, 9001, 9002, 9003, 9004] with [HAVE6, GroupP.gL4]

theorem g_K {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 5 → ∀ M, Reach (callState s (20678 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 41842 (wd (20686 + 22 * b) :: gB amask col rb ret tail) M) 15 := by
  intro b hb M
  interval_cases b
  · glam65_rreach [9005, 9006, 9007, 9008]
  · glam65_rreach [9015, 9016, 9017, 9018]
  · glam65_rreach [9025, 9026, 9027, 9028]
  · glam65_rreach [9035, 9036, 9037, 9038]
  · glam65_rreach [9045, 9046, 9047, 9048]

theorem g_L {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} : ∀ b, b < 4 → ∀ M, Reach (callState s (20686 + 22 * b) (gB amask col rb ret tail) M)
      (callState s 10187 (wd (FL + 224 * b) :: wd (ABUF + 1792 * b) :: wd (20700 + 22 * b) ::
        gB amask col rb ret tail) M) 21 := by
  intro b hb M
  interval_cases b
  · glam65_rreach [9009, 9010, 9011, 9012, 9013, 9014] with [FL, ABUF]
  · glam65_rreach [9019, 9020, 9021, 9022, 9023, 9024] with [FL, ABUF]
  · glam65_rreach [9029, 9030, 9031, 9032, 9033, 9034] with [FL, ABUF]
  · glam65_rreach [9039, 9040, 9041, 9042, 9043, 9044] with [FL, ABUF]

theorem g_L4 {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) : Reach (callState s (20686 + 22 * 4) (gB amask col rb ret tail) M)
      (callState s 10193 (wd (FL + 224 * 4) :: wd (ABUF + 1792 * 4) :: wd 20788 ::
        gB amask col rb ret tail) M) 21 := by
  glam65_rreach [9049, 9050, 9051, 9052, 9053, 9054] with [FL, ABUF]

theorem g_G {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 900)
    {amask col rb ret : Nat} (M : ByteArray) :
    Reach (callState s 20788 (gB amask col rb ret tail) M)
      (callState s 17249 (wd amask :: wd 20797 :: gB amask col rb ret tail) M) 18 := by
  glam65_rreach [9055, 9056, 9057, 9058, 9059]

theorem g_E {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) {amask col rb : Nat} {ok : UInt256} (M : ByteArray) :
    Reach (callState s 20797 (ok :: gB amask col rb ret tail) M) (callState s ret (ok :: tail) M) 27 := by
  have := hr.depth
  have e : Stack.group = 266 := by decide
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [9060, 9061, 9062, 9063, 9064, 9065, 9066, 9067, 9068] with [hj]

theorem pack4_lane {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] at hx ⊢
  omega

theorem pack4_congr {v w : Nat → Nat} (h : ∀ r, r < 4 → v r = w r) : pack4 v = pack4 w := by
  unfold pack4
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

/-- Seed state of slot `k` of `group [amask, col, rb]`. -/
def gI (cd : ByteArray) (amask col rb k : Nat) : Fips202.SpongeState :=
  seedState 168 (aSeed cd (GroupP.gRow amask rb k) col)

/-- Raw candidate left in an inactive slot. -/
def gJunk (cd : ByteArray) (amask col rb r t : Nat) : Nat :=
  cand (permN (t / 56 + 1) (gI cd amask col rb r)) (t % 56)

theorem g_popcnt {amask : Nat} (ha : amask < 16) : popcnt amask ≤ 4 := by
  interval_cases amask <;> decide

theorem aI_gI {cd : ByteArray} (h32 : 32 ≤ cd.size) {amask col rb r : Nat}
    (hact : amask.testBit r = true) :
    MlDsaOpt44.Proofs.aI (gI cd amask col rb r) = aOf cd (4 * rb + r) col := by
  have h : MlDsaOpt44.Proofs.aI (seedState 168 (aSeed cd (4 * rb + r) col)) = aOf cd (4 * rb + r) col :=
    GroupP.aI_aSeed h32 (4 * rb + r) col
  have e : gI cd amask col rb r = seedState 168 (aSeed cd (4 * rb + r) col) := by
    unfold gI GroupP.gRow; rw [if_pos hact]
  rw [e]
  exact h

theorem g_slot {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb r : Nat) :
    (!amask.testBit r || (MlDsaOpt44.Proofs.aI (gI cd amask col rb r)).isSome) =
      (!amask.testBit r || (aOf cd (4 * rb + r) col).isSome) := by
  cases hact : amask.testBit r
  · simp only [Bool.not_false, Bool.true_or]
  · rw [aI_gI h32 hact]

theorem g_flag {cd : ByteArray} (h32 : 32 ≤ cd.size) (amask col rb : Nat) :
    ((List.range 4).all fun sl => !amask.testBit sl ||
        (MlDsaOpt44.Proofs.aI (gI cd amask col rb sl)).isSome) = gOk cd amask col rb := by
  unfold gOk
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.all_cons, List.all_nil, g_slot h32]

end MlDsaOptGlam65.Proofs.GroupV4

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs.Infra
open MlDsaOptGlam65.Proofs.GroupV4

/-- **group** (`group_call` of `Fn/Group.lean`; `gsFrame` is `groupFrame rb`). -/
theorem group_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (hamask : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => if amask.testBit r then
            ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t)) ∧
      FrameExcept m m' gsFrame ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group := by
  have htail : tail.length ≤ 758 := by
    have := hr.depth
    have e : Stack.group = 266 := by decide
    omega
  have hret := hr.small
  have h32 : 32 ≤ s.executionEnv.calldata.size := by unfold HDR at hcd; omega
  clear hcd
  -- prologue: `HAVE6 := 0`, lane 4, `ginit`
  have hb0 := g_b0 hs (tail := tail) (by omega) hamask hcol hrb m (ret := ret)
  have hf1 := FrameExcept.mstore m HAVE6 0
  have h61 : word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) HAVE6 = 0 :=
    word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m2, hks2, hf2, hc2⟩ := MlDsaOptGlam65.Proofs.ginit_call hs (hr.callee (B' := Stack.ginit)
    (ret' := 20678) (extra := [wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide) (by simp only [isValidJumpDest_lit])
    (by norm_num))
    (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6) (keep := 0) (amult := 15)
    (cmult := 0) (l4 := GroupP.gL4 amask col rb) (by norm_num) (by norm_num) (by norm_num)
    (GroupP.gL4_lt hamask hcol hrb)
  have hI : Sized4 (gI s.executionEnv.calldata amask col rb) := sized4_seedState 168 _
  have hinv0 : SqInv m m2 (gI s.executionEnv.calldata amask col rb) 0 := by
    refine ⟨fun x hx => ?_, rc4_frame hf2 (fun i hi => by grp_avoids)
      (rc4_frame hf1 (fun i hi => by grp_avoids) hrc),
      ?_, FrameExcept.of_avoid (hf1.trans hf2) (by grp_sub), fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩
    · rw [hks2 x hx, GroupP.gL4_eq hamask hcol hrb]
      exact GroupP.ginit_group (fun y hy => by
        rw [FrameExcept.word hf1 (by grp_avoids)]; exact hrho.1 y hy)
        h32 (by omega) (fun k hk => Nat.lt_trans (GroupP.gRow_lt (amask := amask) hrb hk) (by norm_num)) hx
    · rw [FrameExcept.word hf2 (by grp_avoids)]; exact h61
  -- five squeezes
  obtain ⟨m6, hinv6, hR6⟩ := squeezes hs hr (amask := amask) (col := col) (rb := rb) hI hinv0
    (g_K hs (by omega)) (g_L hs (by omega))
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (fun b hb => by interval_cases b <;> simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    4 le_rfl
  obtain ⟨m7, ⟨hks7, hrc7, h67, hfr7, hblk7⟩, hR7⟩ := squeeze_last hs hr (amask := amask) (col := col)
    (rb := rb) hI hinv6 (g_K hs (by omega) 4 (by omega) m6) (g_L4 hs (by omega))
    (by simp only [Nat.reduceMul, Nat.reduceAdd, isValidJumpDest_lit])
    (by simp only [isValidJumpDest_lit])
  -- `gfix amask`
  obtain ⟨m8, hpost8, -, hkeep8, -, hf8, hc8⟩ := MlDsaOptGlam65.Proofs.gfix_call hs (hr.callee (B' := Stack.gfix)
    (ret' := 20797) (extra := [wd amask, wd col, wd rb, wd ret])
    (by simp only [List.length_cons, List.length_nil]; decide)
    (by simp only [isValidJumpDest_lit]) (by norm_num)) m7 hrc7 hamask 4 (g_popcnt hamask)
    (fun k => permN 5 (gI s.executionEnv.calldata amask col rb k)) (fun k hk => permN_size (hI k hk) 5) hks7
    (gI s.executionEnv.calldata amask col rb) h67
    (fun sl hsl _ => ⟨slotHead_of_blocks
      (St := fun b k => permN (b + 1) (gI s.executionEnv.calldata amask col rb k))
      hsl (fun _ _ => rfl) (fun b hb => (hblk7 b hb).1) (fun b hb => (hblk7 b hb).2), rfl⟩)
  rw [g_flag h32] at hc8
  refine ⟨m8, fun hall => ⟨gJunk s.executionEnv.calldata amask col rb,
    fun r t => cand_lt _ _, fun t ht => ?_⟩, FrameExcept.of_avoid (hfr7.trans hf8) (by grp_sub), ?_⟩
  · rw [← pack4_lane (word_lt m8 (ABUF + 32 * t))]
    apply pack4_congr
    intro r hr4
    by_cases hact : amask.testBit r = true
    · rw [if_pos hact]
      have hsome : (aOf s.executionEnv.calldata (4 * rb + r) col).isSome = true := by
        have h := List.all_eq_true.mp hall r (List.mem_range.mpr hr4)
        rw [hact] at h
        simpa using h
      obtain ⟨a, ha'⟩ := Option.isSome_iff_exists.mp hsome
      have hD : aD s.executionEnv.calldata (4 * rb + r) col = a := by unfold aD; rw [ha']; rfl
      rw [hD]
      exact hpost8 r hr4 hact a (by rw [aI_gI h32 hact]; exact ha') t ht
    · rw [if_neg hact, hkeep8 r hr4 (by simpa using hact) t ht]
      have hb : t / 56 < 5 := by omega
      rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
        (hblk7 _ hb).1 _ (Nat.mod_lt _ (by norm_num)) (by omega), lane_pack4_cand _ _ hr4]
      rfl
  · rw [call_iff, Entry.group]
    have h := (((((hb0.trans (call_iff.mp hc2)).trans hR6).trans hR7).trans
      (g_G hs (tail := tail) (by omega) m7)).trans (call_iff.mp hc8)).trans (g_E hs hr m8)
    refine (h.mono ?_).of_eq rfl rfl
    unfold Gas.group
    generalize Gas.ginit = a; generalize Gas.kf4 = b; generalize Gas.blk = c
    generalize Gas.blkh = d; generalize Gas.gfix 4 = e
    omega

end MlDsaOptGlam65.Proofs
