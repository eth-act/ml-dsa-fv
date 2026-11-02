import MlDsaOptGlam65.Main.Exp.Bound
import MlDsaOpt65.Fn.Group.Seed
import MlDsaOpt44.Math
set_option warningAsError true
/-!
# The inline groups of calls 15–34 (glam ML-DSA-65): slot states and group-level steps

Groups 3, 4 (`G34.lean`): slot `k` squeezes `A[r][3 − k]` of row `r = 4, 5`
(`XR`), `gfix 15`. Groups 5, 6 (`G56.lean`): slot 0 absorbs blocks
`j0 … j0 + 4` of the padded public key (`tr`), slots `1 … 3` squeeze rows
`0 … 2` of column `col = 3, 4` (`XT`), `gfix 14`. `ginit_row` / `ginit_tr`
(the `HAVE6` store and `ginit`), `gfix_row` / `gfix_tr` (`SlotHead` from the
five block heads), and the copies of the fixed-up lanes into the side buffers.
The four groups themselves are generated (`G/gen.py`, `G/Grp{3,4,5,6}.lean`).
-/

namespace MlDsaOptGlam65.Proofs.Exp.G

open MlDsaOpt65.Proofs
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Rho1At Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muBlock muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam65.Proofs.Ex
open MlDsaOptGlam65.Proofs.Infra

/-- Close `Avoids rs lo hi` for literal layout ranges (with `SB`). -/
macro "expg_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, ZH2, BASES, IDX, ACC, HP, FIN, RHO1, CB, TRL, MU, BK, TT, SP, TOP, KZ, SB]
  omega))

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    aI (seedA cd r col) = aOf cd r col :=
  GroupP.aI_aSeed hcd r col

/-! ## Row groups (3, 4) -/

/-- A row group before squeeze `b`: slot `k` squeezes `A[r][3 − k]`. -/
def XR (cd : ByteArray) (r b k : Nat) : Fips202.SpongeState := permN b (seedA cd r (3 - k))

theorem XR_sized (cd : ByteArray) (r b : Nat) : Sized4 (XR cd r b) := fun _ _ =>
  permN_size (seedState_size _ _) b

theorem permute_XR (cd : ByteArray) (r b k : Nat) : Keccak.permute (XR cd r b k) = XR cd r (b + 1) k := by
  unfold XR; rw [permN_succ]

theorem XR_zero (cd : ByteArray) (r k : Nat) : XR cd r 0 k = seedState 168 (aSeed cd r (3 - k)) := by
  unfold XR permN seedA; rfl

/-! ## `tr` groups (5, 6) -/

/-- A `tr` group before squeeze `b`: slot 0 `tr`'s sponge after the blocks
`< j0 + b` of the padded public key, slot `k ≥ 1` squeezes `A[k − 1][col]`. -/
def XT (cd : ByteArray) (col j0 b k : Nat) : Fips202.SpongeState :=
  if k = 0 then absorbPre 136 (Fips202.pad 136 0x1F (pkOf cd)) (j0 + b) else permN b (seedA cd (k - 1) col)

theorem XT_sized (cd : ByteArray) (col j0 b : Nat) : Sized4 (XT cd col j0 b) := fun k _ => by
  unfold XT; split
  · exact absorbPre_size _ _ _
  · exact permN_size (seedState_size _ _) b

theorem permute_upd_XT (cd : ByteArray) (col j0 b : Nat) {k : Nat} (_hk : k < 4) :
    Keccak.permute (upd (XT cd col j0 b) 0
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) ((j0 + b) * 136) (XT cd col j0 b 0)) k) =
      XT cd col j0 (b + 1) k := by
  unfold upd XT
  by_cases h0 : k = 0
  · subst h0
    simp only [if_true]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h0, if_neg h0, if_neg h0, permN_succ]

theorem XT_zero_pos {cd : ByteArray} {col j0 k : Nat} (hk : k ≠ 0) :
    XT cd col j0 0 k = seedState 168 (aSeed cd (k - 1) col) := by
  unfold XT permN seedA; rw [if_neg hk]; rfl

/-! ## `ginit` -/

/-- The `HAVE6` store and `ginit [keep, amult, 0, l4]`, for any slot states `I`
made from the kept slots `kmask` of `S` and fresh slots. -/
theorem ginit_gen {s : State} (hs : Ctx s) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S I : Nat → Fips202.SpongeState}
    {keep kmask amult l4 : Nat} {L : Nat → Nat} (ha : amult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hl4 : l4 = il L) (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true → amult.testBit k = false ∧ L k = 0)
    (hkept : ∀ k, k < 4 → kmask.testBit k = true → I k = S k)
    (hfresh : ∀ k, k < 4 → kmask.testBit k = false → ∀ x, x < 25 →
      S4.freshLane amult 0 (fun x => le64 s.executionEnv.calldata (8 * x))
        (fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) L k x = laneOf (I k) x)
    {pc0 r c0 : Nat} {b : Bool}
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 17659 [wd l4, wd 0, wd amult, wd keep, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 I ∧ word m1 HAVE6 = 0 ∧ FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hkeep' : keep < 2 ^ 256 := by rw [hkeep]; exact il_lt _
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0 (keep := keep) (amult := amult) (cmult := 0) (l4 := l4)
    hkeep' (by omega) (by norm_num) hl4'
  have hrho0 := Rho1At.frame hrho hf0 (by expg_frame)
  have hks1 : KS4 m1 I :=
    S4.ks4_ginit (kmask := kmask) (L := L) (ρ := fun x => le64 s.executionEnv.calldata (8 * x))
      (c := fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) (S := S)
      ha (by norm_num) hkeep hl4
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x hx => by
        rw [word_frame hf0 (a := KS + 32 * x) (lo := KS) (hi := KS + 800) (by expg_frame) (by omega)
          (by omega)]
        exact hand x hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) hL
      (fun k hk hb => ⟨(hdisj k hk hb).1, Nat.zero_testBit k, (hdisj k hk hb).2⟩)
      hkept hfresh hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by expg_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `ginit [0, 15, 0, l4]` of row group `r`: slot `k` the seed of `A[r][3 − k]`. -/
theorem ginit_row {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {row l4 pc0 r c0 : Nat} {b : Bool} (hrow : row < 256)
    (hl4 : l4 = il fun k => (3 - k) + 256 * row + 0x1F0000)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 17659 [wd l4, wd 0, wd 15, wd 0, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XR s.executionEnv.calldata row 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) :=
  ginit_gen hs hrho (S := XR s.executionEnv.calldata row 0) (I := XR s.executionEnv.calldata row 0) (kmask := 0)
    (amult := 15) (L := fun k => (3 - k) + 256 * row + 0x1F0000) (by norm_num)
    (il_eq_zero fun k _ => by simp).symm
    (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm) hl4
    (fun k _ => by omega) (fun k _ h => by simp at h) (fun k _ h => by simp at h)
    (fun k hk _ x hx => by
      rw [XR_zero]
      have h15 : (15 : Nat).testBit k = true := by interval_cases k <;> decide
      exact S4.freshLane_aSeed (L := fun k => (3 - k) + 256 * row + 0x1F0000) hcd (fun _ _ => rfl)
        hrow (by omega) h15 (Nat.zero_testBit k) rfl hx)
    g0 hj hr

/-- `ginit [keep, 14, 0, l4]` of a `tr` group: slot 0 kept (`kmask = 1`) or
fresh (`kmask = 0`, then `j0 = 0`), slot `k ≥ 1` the seed of `A[k − 1][col]`. -/
theorem ginit_tr {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} {keep kmask j0 col : Nat}
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hk : ∀ k, 1 ≤ k → k < 4 → kmask.testBit k = false)
    (h0 : kmask.testBit 0 = true → S 0 = absorbPre 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) j0)
    (h0' : kmask.testBit 0 = false → j0 = 0) (hcol : col < 256)
    {l4 pc0 r c0 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k = 0 then 0 else col + 256 * (k - 1) + 0x1F0000)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 17659 [wd l4, wd 0, wd 14, wd keep, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata col j0 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  have hbit0 : ∀ k, k < 4 → kmask.testBit k = true → k = 0 := fun k hk' hb' => by
    by_contra hne
    rw [hk k (by omega) hk'] at hb'
    exact absurd hb' (by decide)
  exact ginit_gen hs hrho (S := S) (I := XT s.executionEnv.calldata col j0 0) (kmask := kmask) (by norm_num) hkeep hand hl4
    (fun k _ => by split <;> omega)
    (fun k hk' hb' => by obtain rfl := hbit0 k hk' hb'; exact ⟨by decide, by simp⟩)
    (fun k hk' hb' => by
      obtain rfl := hbit0 k hk' hb'
      unfold XT
      rw [if_pos rfl, h0 hb', Nat.add_zero])
    (fun k hk' hb' x hx => by
      by_cases h0k : k = 0
      · subst h0k
        unfold XT
        rw [if_pos rfl, h0' hb', Nat.add_zero, absorbPre_zero]
        exact S4.freshLane_zero (by decide) (by decide) (by simp) x
      · rw [XT_zero_pos h0k]
        exact S4.freshLane_aSeed hcd (fun _ _ => rfl) (by omega) hcol
          (by interval_cases k <;> first | omega | decide) (by simp) (by simp only [if_neg h0k]) hx)
    g0 hj hr

/-- `ginit`'s keep mask of group 6: slot 0 (`tr`). -/
theorem keep1 : (0x1111111111111111111111111111111111111111111111111111111111111111 : Nat) =
    il fun k => if (1 : Nat).testBit k then M64 else 0 := by decide +kernel

/-! ## `gfix` -/

theorem okRow_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (r : Nat) :
    ((List.range 4).all fun sl => !(15 : Nat).testBit sl || (aI (seedA cd r (3 - sl))).isSome) =
      okRow cd r := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (15 : Nat).testBit 0 = true by decide, show (15 : Nat).testBit 1 = true by decide,
    show (15 : Nat).testBit 2 = true by decide, show (15 : Nat).testBit 3 = true by decide,
    Bool.not_true, Bool.false_or, aI_seedA hcd, okRow]

/-- `gfix 15` after the five squeezes of row group `r`. -/
theorem gfix_row {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {row pc r c : Nat} {fb : UInt256}
    (gG : Reach (callState s pc [fb] m) (callState s 17249 [wd 15, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XR s.executionEnv.calldata row 5))
    (hB : HBlocks m ABUF FL (fun b k => XR s.executionEnv.calldata row (b + 1) k) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', RowBuf m' ABUF s.executionEnv.calldata row ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okRow s.executionEnv.calldata row), fb] m') (c + Gas.gfix 4) := by
  obtain ⟨m', hlanes, -, -, -, hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 15) (by norm_num) 4 (by decide)
    (XR s.executionEnv.calldata row 5) (XR_sized _ row 5) hks
    (fun k => seedA s.executionEnv.calldata row (3 - k)) h6
    (fun sl hsl _ => ⟨hB.slotHead hsl (fun _ _ => rfl), rfl⟩)
  rw [okRow_flag hcd] at hc
  refine ⟨m', fun hok t ht k hk => ?_, hf, gG.trans hc⟩
  have hsk : (aOf s.executionEnv.calldata row (3 - k)).isSome = true := by
    unfold okRow at hok
    rw [List.all_eq_true] at hok
    exact hok k (List.mem_range.mpr hk)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsk
  rw [hlanes k hk (by interval_cases k <;> decide) a (by rw [aI_seedA hcd]; exact ha) t ht]
  unfold aD; rw [ha]; rfl

theorem okCol3_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !(14 : Nat).testBit sl ||
      (aI (if sl = 0 then Fips202.emptyState else seedA cd (sl - 1) col)).isSome) = okCol3 cd col := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (14 : Nat).testBit 0 = false by decide, show (14 : Nat).testBit 1 = true by decide,
    show (14 : Nat).testBit 2 = true by decide, show (14 : Nat).testBit 3 = true by decide,
    okCol3, show List.range 3 = [0, 1, 2] from rfl, Nat.reduceSub, if_true, if_false, aI_seedA hcd,
    show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and, Bool.and_true]

/-- `gfix 14` after the five squeezes of a `tr` group. -/
theorem gfix_tr {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {col j0 pc r c : Nat} {fb : UInt256}
    (gG : Reach (callState s pc [fb] m) (callState s 17249 [wd 14, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XT s.executionEnv.calldata col j0 5))
    (hB : HBlocks m ABUF FL (fun b k => XT s.executionEnv.calldata col j0 (b + 1) k) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', Col3Hi m' ABUF s.executionEnv.calldata col ∧ KS4 m' (XT s.executionEnv.calldata col j0 5) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okCol3 s.executionEnv.calldata col), fb] m') (c + Gas.gfix 3) := by
  let I : Nat → Fips202.SpongeState := fun k =>
    if k = 0 then Fips202.emptyState else seedA s.executionEnv.calldata (k - 1) col
  obtain ⟨m', hlanes, hks', -, -, hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 14) (by norm_num) 3 (by decide)
    (XT s.executionEnv.calldata col j0 5) (XT_sized _ col j0 5) hks I h6
    (fun sl hsl hbit => by
      have hsl0 : sl ≠ 0 := by
        rintro rfl; exact absurd hbit (by decide)
      have hI : I sl = seedA s.executionEnv.calldata (sl - 1) col := by simp only [I, if_neg hsl0]
      refine ⟨hB.slotHead hsl (fun b' _ => ?_), ?_⟩
      · show XT _ col j0 (b' + 1) sl = _
        rw [hI]; unfold XT; rw [if_neg hsl0]
      · rw [hI]; unfold XT; rw [if_neg hsl0])
  simp only [I] at hc
  rw [okCol3_flag hcd] at hc
  refine ⟨m', fun hok t ht rr hrr => ?_, hks', hf, gG.trans hc⟩
  have hs3 : (aOf s.executionEnv.calldata rr col).isSome = true := by
    unfold okCol3 at hok
    rw [List.all_eq_true] at hok
    exact hok rr (List.mem_range.mpr hrr)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs3
  have := hlanes (rr + 1) (by omega) (by interval_cases rr <;> decide) a
    (by simp only [I, if_neg (by omega : rr + 1 ≠ 0), Nat.add_sub_cancel]; rw [aI_seedA hcd]; exact ha)
    t ht
  rw [this]; unfold aD; rw [ha]; rfl

/-! ## Copies to the side buffers -/

theorem rowBuf_mcopy {m cd : ByteArray} {dst r : Nat} (h : RowBuf m ABUF cd r) :
    RowBuf (MachineState.writeBytes m (MachineState.readPadded m ABUF 8192) dst) dst cd r :=
  fun hok t ht k hk => by
    rw [word_mcopy _ (Nat.le_add_right _ _) (by omega), Nat.add_sub_cancel_left]
    exact h hok t ht k hk

theorem col3Hi_mcopy {m cd : ByteArray} {dst col : Nat} (h : Col3Hi m ABUF cd col) :
    Col3Hi (MachineState.writeBytes m (MachineState.readPadded m ABUF 8192) dst) dst cd col :=
  fun hok t ht r hr => by
    rw [word_mcopy _ (Nat.le_add_right _ _) (by omega), Nat.add_sub_cancel_left]
    exact h hok t ht r hr

end MlDsaOptGlam65.Proofs.Exp.G
