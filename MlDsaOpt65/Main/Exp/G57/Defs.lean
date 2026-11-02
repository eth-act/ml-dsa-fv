import MlDsaOpt65.Main.Exp.Round
import MlDsaOpt65.Main.Exp.Bound
import MlDsaOpt65.Main.Exp.Acc
import MlDsaOpt65.Fn.Group.Seed
set_option warningAsError true
/-!
# Mixed groups 5 … 7 (ML-DSA-65, v4): slot states and the group-level steps

Slots 0 … 2 of group `5 + g` squeeze the row-group-1 instances `i0 = 3 g, i0 + 1,
i0 + 2` (`seedI`), slot 3 absorbs blocks `j0 = 5 g, …, j0 + 4` of the padded
public key (`XT`). `ginit_tr` (restored from the v3 `S4/Round.lean`, v4 `ginit`),
`gfix_trio` (v4: `SlotHead`), `ks4_trabs_last` / `pad_words` for group 7's short
last block, and the copy of the fixed-up lanes into a side buffer (`MixBuf`).
-/

namespace MlDsaOpt65.Proofs.G57

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Ex
open MlDsaOpt65.Proofs.Infra

/-- Close `Avoids rs lo hi` for literal layout ranges (65). -/
macro "g57_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, MlDsaOpt65.Proofs.ZH2, MlDsaOpt65.Proofs.BASES, MlDsaOpt65.Proofs.IDX,
    MlDsaOpt65.Proofs.ACC, MlDsaOpt65.Proofs.HP, MlDsaOpt65.Proofs.FIN, MlDsaOpt65.Proofs.RHO1,
    MlDsaOpt65.Proofs.CB, MlDsaOpt65.Proofs.TRL, MlDsaOpt65.Proofs.MU, MlDsaOpt65.Proofs.BK,
    MlDsaOpt65.Proofs.TOP, MlDsaOpt65.Proofs.KZ]
  omega))

/-- The padded public key. -/
abbrev padPk65 (cd : ByteArray) : ByteArray := Fips202.pad 136 0x1F (pkOf cd)

/-- The seed state of row-group-1 instance `i` (`A[4 + i % 2][i / 2]`). -/
def seedI (cd : ByteArray) (i : Nat) : Fips202.SpongeState :=
  seedState 168 (aSeed cd (4 + i % 2) (i / 2))

theorem aI_seedI {cd : ByteArray} (hcd : 32 ≤ cd.size) (i : Nat) :
    aI (seedI cd i) = aOf cd (4 + i % 2) (i / 2) :=
  GroupP.aI_aSeed hcd _ _

/-- Slots of group `5 + g` before squeeze `b`. -/
def XT (cd : ByteArray) (i0 j0 b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedI cd (i0 + k)) else absorbPre 136 (padPk65 cd) (j0 + b)

theorem XT_sized (cd : ByteArray) (i0 j0 b : Nat) : Sized4 (XT cd i0 j0 b) := fun k _ => by
  unfold XT; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ _

theorem permute_upd_XT (cd : ByteArray) (i0 j0 b : Nat) {k : Nat} (_hk : k < 4) :
    Keccak.permute (upd (XT cd i0 j0 b) 3
      (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) ((j0 + b) * 136) (XT cd i0 j0 b 3)) k) =
      XT cd i0 j0 (b + 1) k := by
  unfold upd XT
  by_cases h3 : k = 3
  · subst h3
    simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), ← permN_succ]

/-- `ginit [keep, 7, 0, l4]` of groups 5 … 7 (v4: `ginit` at 11987, the `HAVE6`
store before it). -/
theorem ginit_tr {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} {keep kmask j0 i0 : Nat}
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hk : ∀ k, k < 3 → kmask.testBit k = false)
    (h3 : kmask.testBit 3 = true → S 3 = absorbPre 136 (padPk65 s.executionEnv.calldata) j0)
    (h3' : kmask.testBit 3 = false → j0 = 0) (hi0 : i0 < 8)
    {pc0 r c0 l4 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k < 3 then (i0 + k) / 2 + 256 * (4 + (i0 + k) % 2) + 0x1F0000 else 0)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 11987 [wd l4, wd 0, wd 7, wd keep, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata i0 j0 0) ∧
      word m1 HAVE6 = 0 ∧ FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho h3
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  clear hcd
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hkeep' : keep < 2 ^ 256 := by rw [hkeep]; exact il_lt _
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0 (keep := keep) (amult := 7) (cmult := 0) (l4 := l4)
    hkeep' (by norm_num) (by norm_num) hl4'
  have hrho0 := Rho1At.frame hrho hf0 (by g57_frame)
  have hbit3 : ∀ k, k < 4 → kmask.testBit k = true → k = 3 := fun k hk' hb' => by
    by_contra hne
    rw [hk k (by omega)] at hb'
    exact absurd hb' (by decide)
  have hks1 : KS4 m1 (XT cd i0 j0 0) :=
    S4.ks4_ginit (kmask := kmask)
      (L := fun k => if k < 3 then (i0 + k) / 2 + 256 * (4 + (i0 + k) % 2) + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := S)
      (by norm_num) (by norm_num) hkeep hl4
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x hx => by
        rw [word_frame hf0 (a := KS + 32 * x) (lo := KS) (hi := KS + 800) (by g57_frame) (by omega)
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
          show _ = laneOf (seedState 168 (aSeed cd (4 + (i0 + k) % 2) ((i0 + k) / 2))) x
          exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by omega) (by omega)
            (by interval_cases k <;> decide) (by simp) (by rw [if_pos h3k]) hx
        · obtain rfl : k = 3 := by omega
          unfold XT
          rw [if_neg (by decide), h3' hb', Nat.add_zero, absorbPre_zero]
          exact S4.freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by g57_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

theorem lmL_top2 : ∀ k, k < 4 →
    lane 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 k = 0 ∨
      lane 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 k = M64 := by
  decide

/-- `ginit`'s keep mask of groups 6, 7: slot 3. -/
theorem keep8 : (0x8888888888888888888888888888888888888888888888888888888888888888 : Nat) =
    il fun k => if (8 : Nat).testBit k then M64 else 0 := by decide +kernel

theorem gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (i0 : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl || (aI (seedI cd (i0 + sl))).isSome) =
      (okI cd i0 && okI cd (i0 + 1) && okI cd (i0 + 2)) := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, aI_seedI hcd, okI,
    Nat.add_zero, Bool.and_assoc]

/-- `gfix 7` after the five squeezes of a three-instance `tr`-rider group. -/
theorem gfix_trio {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {i0 j0 pc r c : Nat} {fb : UInt256}
    (gG : Reach (callState s pc [fb] m) (callState s 11577 [wd 7, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XT s.executionEnv.calldata i0 j0 5))
    (hB : HBlocks m ABUF FL (fun b k => XT s.executionEnv.calldata i0 j0 (b + 1) k) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', (∀ k, k < 3 → okI s.executionEnv.calldata (i0 + k) = true → ∀ t, t < 256 →
        lane (word m' (ABUF + 32 * t)) k =
          ((aD s.executionEnv.calldata (4 + (i0 + k) % 2) ((i0 + k) / 2))[t]!).toNat) ∧
      KS4 m' (XT s.executionEnv.calldata i0 j0 5) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okI s.executionEnv.calldata i0 && okI s.executionEnv.calldata (i0 + 1) &&
          okI s.executionEnv.calldata (i0 + 2)), fb] m') (c + Gas.gfix 3) := by
  obtain ⟨m', hlanes, hks', -, hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 7) (by norm_num) 3 (by decide)
    (XT s.executionEnv.calldata i0 j0 5) (XT_sized _ i0 j0 5) hks
    (fun k => seedI s.executionEnv.calldata (i0 + k)) h6
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        obtain rfl : sl = 3 := by omega
        exact absurd hbit (by decide)
      refine ⟨hB.slotHead hsl (fun b' _ => ?_), ?_⟩
      · show XT _ i0 j0 (b' + 1) sl = _
        unfold XT; rw [if_pos hsl3]
      · unfold XT; rw [if_pos hsl3])
  rw [gfix7_flag hcd] at hc
  refine ⟨m', fun k hk hok t ht => ?_, hks', hf, gG.trans hc⟩
  unfold okI at hok
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok
  rw [hlanes k (by omega) (by interval_cases k <;> decide) a (by rw [aI_seedI hcd]; exact ha) t ht]
  unfold aD; rw [ha]; rfl

/-- The fixed-up lanes copied to a side buffer give `MixBuf`. -/
theorem mixBuf_of {cd m : ByteArray} {i0 dst : Nat} (hi0 : i0 ≤ 6)
    (h : ∀ k, k < 3 → okI cd (i0 + k) = true → ∀ t, t < 256 →
      lane (word m (dst + 32 * t)) k = ((aD cd (4 + (i0 + k) % 2) ((i0 + k) / 2))[t]!).toNat) :
    Exp.MixBuf m dst cd i0 := fun hok t ht k hk =>
  h k hk (by unfold okI; exact s3_okA_get hok (by omega) (by omega)) t ht

/-- The last block of the padded public key (`trabs` with two groups, then the
two padding xors), absorbed into slot 3. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : CTOFF ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' (upd S 3 (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (14 * 136) (S 3))) := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  have hsx : ∀ a b, spread a * 2 ^ 3 ^^^ spread b * 2 ^ 3 = spread (a ^^^ b) * 2 ^ 3 := fun a b => by
    rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
      spread_mul_two_pow _ (by norm_num), il_xor]
    exact il_congr fun k _ => by split <;> simp
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) ^^^ ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt' _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, hsx]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 14 * 136 + 8 * x = 1904 + 8 * x by omega,
      S4.le64_padPk_last hcd h17]
    congr 1
    by_cases h6 : x < 6
    · rw [if_pos h6, if_pos (by omega), trLane_eq cd S4.lm_top2, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
    · rw [if_neg h6]
      by_cases hx6 : x = 6
      · subst hx6; rw [trLane_eq cd S4.lm_top2]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx6, if_neg hx16, Nat.xor_zero]
          by_cases h8 : x < 8
          · rw [if_pos h8, trLane_eq cd S4.lm_top2, if_pos (by omega)]
          · rw [if_neg h8]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

/-- The two padding xors of the last `pk` block (lanes 6 and 16, slot 3). -/
theorem pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
    word (MachineState.writeBytes
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 559240) % 2 ^ 256) 32) 192)
      (Data.Bytes.natToBytesPadded ((word (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded ((word m 192 ^^^ 559240) % 2 ^ 256) 32) 192) 512 ^^^
        57896044618658097711785492504343953926634992332820282019728792003956564819968) % 2 ^ 256) 32) 512)
      (KS + 32 * x) =
    word m (KS + 32 * x) ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3 := by
  have hm : ∀ (w c : Nat), c < 2 ^ 256 → w < 2 ^ 256 → (w ^^^ c) % 2 ^ 256 = w ^^^ c :=
    fun w c hc hw => Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hw hc)
  unfold KS
  by_cases h6 : x = 6
  · subst h6
    rw [word_mstore_disjoint _ _ (by omega), word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)),
      hm _ _ (by norm_num) (word_lt _ _)]
    congr 1
  · by_cases h16 : x = 16
    · subst h16
      rw [word_mstore _ _ _ (Nat.mod_lt _ (by norm_num)), hm _ _ (by norm_num) (word_lt _ _),
        word_mstore_disjoint _ _ (by omega)]
      congr 1
    · rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega), if_neg h6, if_neg h16,
        Nat.xor_zero, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem zhat_frame {cd m m' : ByteArray} {rs : List (Nat × Nat)} (h : ZHatAt m cd)
    (hf : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 16384)) : ZHatAt m' cd := by
  intro k hk t ht
  have e : zhLane m' k t = zhLane m k t := by
    unfold zhLane zhAddr
    rw [word_frame hf ha (by omega) (by interval_cases k <;> simp [ZH] <;> omega)]
  rw [e]; exact h k hk t ht

theorem acc0_frame {cd m m' : ByteArray} {rs : List (Nat × Nat)} (h : AccCols0 m cd 5)
    (hf : FrameExcept m m' rs) (ha : Avoids rs ZH (ZH + 16384)) (hb : Avoids rs ACC (ACC + 8192)) :
    AccCols0 m' cd 5 := by
  intro hok t ht
  rw [word_frame hf hb (a := ACC + 32 * t) (by omega) (by omega), h hok t ht]
  congr 1; funext r
  exact (s3_accSum_congr 5 fun k hk => by
    unfold zhLane zhAddr
    rw [word_frame hf ha (by omega) (by interval_cases k <;> simp [ZH] <;> omega)]).symm

end MlDsaOpt65.Proofs.G57
