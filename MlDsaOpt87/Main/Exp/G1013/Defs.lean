import MlDsaOpt87.Main.Exp.G1013.Round
import MlDsaOpt87.Main.Exp.Bound
set_option warningAsError true
/-!
# Mixed groups 10 … 13 (ML-DSA-87, v4): slot states and the group-level steps

Slots 0 … 2 of group `10 + g` squeeze rows 4 … 6 of column `col = 3 + g`, slot 3
absorbs blocks `j0 = 5 g, …, j0 + 4` of the padded public key (`XT`).
`ginit_tr` (v4 `ginit`, `Exp.ks4_ginit`), `gfix_trio` (`SlotHead`),
`pad_words` / the short last block of group 13, and `Col3At` from the lanes.
-/

namespace MlDsaOpt87.Proofs.G1013

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Close `Avoids rs lo hi` for literal layout ranges (87). -/
macro "g1013_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, MlDsaOpt87.Proofs.BASES, MlDsaOpt87.Proofs.IDX,
    MlDsaOpt87.Proofs.ACC, MlDsaOpt87.Proofs.HP, MlDsaOpt87.Proofs.FIN, MlDsaOpt87.Proofs.RHO1,
    MlDsaOpt87.Proofs.CB, MlDsaOpt87.Proofs.TRL, MlDsaOpt87.Proofs.MU, MlDsaOpt87.Proofs.BK,
    MlDsaOpt87.Proofs.TOP, MlDsaOpt87.Proofs.KZ]
  omega))

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    aI (seedA cd r col) = aOf cd r col :=
  GroupP.aI_aSeed hcd r col

/-- Slots of group `10 + g` before squeeze `b`: rows 4 … 6 of column `col`, `tr`. -/
def XT (cd : ByteArray) (col j0 b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedA cd (4 + k) col) else absorbPre 136 (padPk cd) (j0 + b)

theorem XT_sized (cd : ByteArray) (col j0 b : Nat) : Sized4 (XT cd col j0 b) := fun k _ => by
  unfold XT; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ _

theorem permute_upd_XT (cd : ByteArray) (col j0 b : Nat) {k : Nat} (_hk : k < 4) :
    Keccak.permute (upd (XT cd col j0 b) 3
      (Fips202.xorBlock 136 (padPk cd) ((j0 + b) * 136) (XT cd col j0 b 3)) k) =
      XT cd col j0 (b + 1) k := by
  unfold upd XT
  by_cases h3 : k = 3
  · subst h3
    simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), ← permN_succ]

/-- `ginit [keep, 7, 0, l4]` of groups 10 … 13 (v4: `ginit` at 13376, the `HAVE6`
store before it). -/
theorem ginit_tr {s : State} (hs : Ctx s) (hcd : 7219 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} {keep kmask j0 col : Nat}
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hk : ∀ k, k < 3 → kmask.testBit k = false)
    (h3 : kmask.testBit 3 = true → S 3 = absorbPre 136 (padPk s.executionEnv.calldata) j0)
    (h3' : kmask.testBit 3 = false → j0 = 0) (hcol : col < 7)
    {pc0 r c0 l4 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k < 3 then col + 256 * (4 + k) + 0x1F0000 else 0)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 13376 [wd l4, wd 0, wd 7, wd keep, wd r, flag b]
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
  have hrho0 := Rho1At.frame hrho hf0 (by g1013_frame)
  have hbit3 : ∀ k, k < 4 → kmask.testBit k = true → k = 3 := fun k hk' hb' => by
    by_contra hne
    rw [hk k (by omega)] at hb'
    exact absurd hb' (by decide)
  have hks1 : KS4 m1 (XT cd col j0 0) :=
    Exp.ks4_ginit (kmask := kmask)
      (L := fun k => if k < 3 then col + 256 * (4 + k) + 0x1F0000 else 0) (S := S) hrho0
      (by norm_num) hkeep hl4
      (fun x hx => by
        rw [word_frame hf0 (a := KS + 32 * x) (lo := KS) (hi := KS + 800) (by g1013_frame) (by omega)
          (by omega)]
        exact hand x hx)
      (fun k _ => by split <;> omega)
      (fun k hk' hb' => by
        obtain rfl := hbit3 k hk' hb'
        exact ⟨by decide, by simp⟩)
      (fun k hk' hb' => by
        obtain rfl := hbit3 k hk' hb'
        unfold XT
        rw [if_neg (by decide), h3 hb', Nat.add_zero])
      (fun k hk' hb' x hx => by
        by_cases h3k : k < 3
        · unfold XT
          rw [if_pos h3k]
          show _ = laneOf (seedState 168 (aSeed cd (4 + k) col)) x
          exact Exp.freshLane_aSeed' hcd32 (by omega) (by omega)
            (by interval_cases k <;> decide) (by rw [if_pos h3k]) hx
        · obtain rfl : k = 3 := by omega
          unfold XT
          rw [if_neg (by decide), h3' hb', Nat.add_zero, absorbPre_zero]
          exact Exp.freshLane_zero' (by decide) (by simp) x)
      hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by g1013_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `ginit`'s keep mask of groups 11 … 13: slot 3. -/
theorem keep8 : (0x8888888888888888888888888888888888888888888888888888888888888888 : Nat) =
    il fun k => if (8 : Nat).testBit k then M64 else 0 := by decide +kernel

theorem gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl ||
      (aI (if sl < 3 then seedA cd (4 + sl) col else Fips202.emptyState)).isSome) = okCol cd 1 col 3 := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 3 = [0, 1, 2] from rfl,
    List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, aI_seedA hcd, okCol,
    show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide, show (2 : Nat) < 3 by decide, if_true,
    Nat.reduceMul, Nat.reduceAdd]

/-- `gfix 7` after the five squeezes of a group. -/
theorem gfix_trio {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {col j0 pc r c : Nat} {fb : UInt256} (hcol : col < 7)
    (gG : Reach (callState s pc [fb] m) (callState s 12966 [wd 7, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XT s.executionEnv.calldata col j0 5))
    (hB : HBlocks m ABUF FL (fun b k => XT s.executionEnv.calldata col j0 (b + 1) k) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', (okA s.executionEnv.calldata = true → ∀ t, t < 256 → ∀ k, k < 3 →
        lane (word m' (ABUF + 32 * t)) k = ((aD s.executionEnv.calldata (4 + k) col)[t]!).toNat) ∧
      KS4 m' (XT s.executionEnv.calldata col j0 5) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okCol s.executionEnv.calldata 1 col 3), fb] m') (c + Gas.gfix 3) := by
  obtain ⟨m', hlanes, hks', -, hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 7) (by norm_num) 3 (by decide)
    (XT s.executionEnv.calldata col j0 5) (XT_sized _ col j0 5) hks
    (fun k => if k < 3 then seedA s.executionEnv.calldata (4 + k) col else Fips202.emptyState) h6
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
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Exp.okA_get hok (r := 4 + k) (s := col) (by omega)
    hcol)
  rw [hlanes k (by omega) (by interval_cases k <;> decide) a (by rw [if_pos hk, aI_seedA hcd]; exact ha) t ht]
  unfold aD; rw [ha]; rfl

/-- The two padding xors of the last `pk` block (lanes 1 and 16, slot 3). -/
theorem pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 32 ^^^ 559240) % 2 ^ 256) 32) 32)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 32 ^^^ 559240) % 2 ^ 256) 32) 32) 512 ^^^
        57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h1 : x = 1
  · subst h1
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h1, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

/-- Group 13's last block in `upd` form. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 2592 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 1 then
        trLane cd 2584 0xffffffffffffffff000000000000000000000000000000000000000000000000 1 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 1 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' (upd S 3 (Fips202.xorBlock 136 (padPk cd) (19 * 136) (S 3))) :=
  s5_ks4_trabs_last hcd hS hks hw

end MlDsaOpt87.Proofs.G1013
