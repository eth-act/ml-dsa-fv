import MlDsaOptGlam44.Main.SegG2
import MlDsaOptGlam44.Main.Alt.Inv
set_option warningAsError true
/-!
# The long-message schedule's `tr`-rider groups: slot states and group-level steps

Groups A and B of the long-message schedule (`alt`, `|M| ≥ 342`): slots 0 … 2
squeeze rows 0 … 2 of column `col` (2, then 3), slot 3 absorbs blocks
`j0 … j0 + 4` of the padded public key (`XT`). `ginit_tr` (`ginit` at 18001),
`gfix_trio` (`gfix 7`, `SlotHead`), `ks4_trabs_last` / `pad_words` for the
short last block of `pk`, `Col3Lo` from the lanes.
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

/-- Close `Avoids rs lo hi` for literal layout ranges. -/
macro "alt_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, BASES, IDX, ACC, HP, FIN, RHO1, CB, TRL, MU, BK, TOP, KZ, SB, LIM, SC, SAVE0, SAVE1,
    FLAG]
  omega))

/-- Slots of a `tr`-rider group before squeeze `b`: rows 0 … 2 of column `col`, `tr`. -/
def XT (cd : ByteArray) (col j0 b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedA cd k col) else absorbPre 136 (padPk cd) (j0 + b)

theorem XT_sized (cd : ByteArray) (col j0 b : Nat) : Sized4 (XT cd col j0 b) := fun k _ => by
  unfold XT; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ _

theorem permute_upd_XT (cd : ByteArray) (col j0 b : Nat) {k : Nat} (_hk : k < 4) :
    Keccak.permute (upd (XT cd col j0 b) 3
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) ((j0 + b) * 136) (XT cd col j0 b 3)) k) =
      XT cd col j0 (b + 1) k := by
  unfold upd XT
  by_cases h3 : k = 3
  · subst h3
    simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]; rfl
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), ← permN_succ]

/-- `ginit [keep, 7, 0, l4]` of a `tr`-rider group (`HAVE6` stored before it). -/
theorem ginit_tr {s : State} (hs : Ctx s) (hcd : 3732 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} {keep kmask j0 col : Nat}
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hk : ∀ k, k < 3 → kmask.testBit k = false)
    (h3 : kmask.testBit 3 = true → S 3 = absorbPre 136 (padPk s.executionEnv.calldata) j0)
    (h3' : kmask.testBit 3 = false → j0 = 0) (hcol : col < 4)
    {pc0 r c0 l4 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k < 3 then col + 256 * k + 0x1F0000 else 0)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 18001 [wd l4, wd 0, wd 7, wd keep, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata col j0 0) ∧
      word m1 HAVE6 = 0 ∧ FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho h3
  have hcd32 : 32 ≤ cd.size := by omega
  clear hcd
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hkeep' : keep < 2 ^ 256 := by rw [hkeep]; exact il_lt _
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0 (keep := keep) (amult := 7) (cmult := 0) (l4 := l4)
    hkeep' (by norm_num) (by norm_num) hl4'
  have hrho0 := hrho.frame hf0 (by alt_frame)
  have hbit3 : ∀ k, k < 4 → kmask.testBit k = true → k = 3 := fun k hk' hb' => by
    by_contra hne
    rw [hk k (by omega)] at hb'
    exact absurd hb' (by decide)
  have hks1 : KS4 m1 (XT cd col j0 0) :=
    ks4_ginit (kmask := kmask) (L := fun k => if k < 3 then col + 256 * k + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := S)
      (by norm_num) (by norm_num) hkeep hl4
      (fun x hx => (hrho0 x hx).1) (fun x hx => (hrho0 x hx).2)
      (fun x hx => by
        rw [word_frame hf0 (a := KS + 32 * x) (lo := KS) (hi := KS + 800) (by alt_frame) (by omega)
          (by omega)]
        exact hand x hx)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k hk' hb' => by
        obtain rfl := hbit3 k hk' hb'
        exact ⟨by decide, by decide, by simp⟩)
      (fun k hk' hb' => by
        obtain rfl := hbit3 k hk' hb'
        unfold XT
        rw [if_neg (by decide), h3 hb', Nat.add_zero])
      (fun k hk' hb' x hx => by
        by_cases h3k : k < 3
        · unfold XT
          rw [if_pos h3k]
          show _ = laneOf (seedState 168 (aSeed cd k col)) x
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by omega) (by omega)
            (by interval_cases k <;> decide) (by simp) (by rw [if_pos h3k]) hx
        · obtain rfl : k = 3 := by omega
          unfold XT
          rw [if_neg (by decide), h3' hb', Nat.add_zero, absorbPre_zero]
          exact freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by alt_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `ginit`'s keep mask of the second group: slot 3. -/
theorem keep8 : (0x8888888888888888888888888888888888888888888888888888888888888888 : Nat) =
    il fun k => if (8 : Nat).testBit k then M64 else 0 := by decide +kernel

theorem gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl ||
      (aI (if sl < 3 then seedA cd sl col else Fips202.emptyState)).isSome) = okCol3 cd col := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 3 = [0, 1, 2] from rfl,
    List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, aI_seedA hcd, okCol3,
    show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide, show (2 : Nat) < 3 by decide, if_true]

/-- `gfix 7` after the five squeezes of a `tr`-rider group. -/
theorem gfix_trio {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {col j0 pc r c : Nat} {fb : UInt256}
    (gG : Reach (callState s pc [fb] m) (callState s 17591 [wd 7, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XT s.executionEnv.calldata col j0 5))
    (hB : HBlocks m ABUF FL (fun b k => XT s.executionEnv.calldata col j0 (b + 1) k) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', Col3Lo m' ABUF s.executionEnv.calldata col ∧
      KS4 m' (XT s.executionEnv.calldata col j0 5) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okCol3 s.executionEnv.calldata col), fb] m') (c + Gas.gfix 3) := by
  obtain ⟨m', hlanes, hks', hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 7) (by norm_num) 3 (by decide)
    (XT s.executionEnv.calldata col j0 5) (XT_sized _ col j0 5) hks
    (fun k => if k < 3 then seedA s.executionEnv.calldata k col else Fips202.emptyState) h6
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        obtain rfl : sl = 3 := by omega
        exact absurd hbit (by decide)
      refine ⟨hB.slotHead hsl (fun b' _ => ?_), ?_⟩
      · show XT _ col j0 (b' + 1) sl = _
        unfold XT; rw [if_pos hsl3, if_pos hsl3]
      · unfold XT; rw [if_pos hsl3, if_pos hsl3])
  rw [gfix7_flag hcd] at hc
  refine ⟨m', fun hok t ht k hk => ?_, hks', hf, gG.trans hc⟩
  have hs3 : (aOf s.executionEnv.calldata k col).isSome = true := by
    unfold okCol3 at hok
    rw [List.all_eq_true] at hok
    exact hok k (List.mem_range.mpr hk)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs3
  rw [hlanes k (by omega) (by interval_cases k <;> decide) a (by rw [if_pos hk, aI_seedA hcd]; exact ha) t ht]
  unfold aD; rw [ha]; rfl

theorem col3Lo_mcopy {m cd : ByteArray} {dst col : Nat} (h : Col3Lo m ABUF cd col) :
    Col3Lo (MachineState.writeBytes m (MachineState.readPadded m ABUF 8192) dst) dst cd col :=
  fun hok t ht => by
    rw [word_mcopy _ (Nat.le_add_right _ _) (by rw [Nat.add_assoc]; exact Nat.add_le_add_left (by omega) _),
      Nat.add_sub_cancel_left]
    exact h hok t ht

theorem Col3Lo.frame {m m' cd : ByteArray} {rs : List (Nat × Nat)} {dst col : Nat}
    (h : Col3Lo m dst cd col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    Col3Lo m' dst cd col := fun hok t ht => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht

/-- The last block of the padded public key (`trabs` with three groups, then the
two padding xors), absorbed into slot 3. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 1312 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' (upd S 3 (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (9 * 136) (S 3))) := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  have hsx : ∀ a b, spread a * 2 ^ 3 ^^^ spread b * 2 ^ 3 = spread (a ^^^ b) * 2 ^ 3 := fun a b => by
    rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
      spread_mul_two_pow _ (by norm_num), il_xor]
    exact il_congr fun k _ => by split <;> simp
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) ^^^ ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt' _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, hsx]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 9 * 136 + 8 * x = 1224 + 8 * x by omega,
      le64_padPk_last hcd h17]
    congr 1
    by_cases h11 : x < 11
    · rw [if_pos h11, if_pos (by omega), trLane_eq cd lm_top3, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
    · rw [if_neg h11]
      by_cases hx11 : x = 11
      · subst hx11; rw [trLane_eq cd lm_top3]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx11, if_neg hx16, Nat.xor_zero]
          rw [if_neg (by omega)]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

/-- The two padding xors of the last `pk` block (lanes 11 and 16, slot 3). -/
theorem pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 559240) % 2 ^ 256) 32) 352)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 352 ^^^ 559240) % 2 ^ 256) 32) 352) 512 ^^^
        57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h11 : x = 11
  · subst h11
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h11, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

end MlDsaOptGlam44.Proofs.Alt
