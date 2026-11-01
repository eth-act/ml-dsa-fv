import MlDsaOpt65.Main.S4.Math
import MlDsaOpt65.Math
import MlDsaOpt65.Fn.Keccak
import MlDsaOpt65.Fn.Blk
import MlDsaOpt65.Fn.Sponge
import MlDsaOpt65.Fn.Fix
import MlDsaOpt65.Main.S3.Lemmas
set_option warningAsError true
/-!
# Building blocks of the mixed SIMD groups 5–8 (ML-DSA-65, WP S4, v3 schedule)

As `MlDsaOpt44/Main/SegG234/Round.lean` for this artifact:

* `Blocks m St n`: the first `n` squeezed blocks of a group are in `ABUF` /
  `FL`, block `b` made from the slot states `St b`.
* `kb_round`: glue, `kf4`, glue, `blk b`.
* `ks4_trabs_full`, `ks4_trabs_last`, `absorb_round`: what `trabs` (and the
  final padding xors) do to the `tr` slot (slot 3).
* `accInst1_step`: a group's `pass3x` on the row-group-1 accumulator
  (`AccInst1`: row 4 in lane 0, row 5 in lane 1, lanes 2, 3 zero).
* `ginit_tr`, `gfix_trio`: `ginit [keep, 7, 0, l4]` and `gfix [7]` of groups
  5–7 (instances `i0 … i0 + 2` in slots 0–2, `Itr`; the `tr` sponge in slot 3, `XT`).
-/

namespace MlDsaOpt65.Proofs.S4

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs.Infra

/-- `Avoids` side conditions on literal layout ranges (lists built with `++`). -/
macro "s4_frame" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW,
    ABUF, FL, ZH, MlDsaOpt65.Proofs.ZH2, MlDsaOpt65.Proofs.BASES, MlDsaOpt65.Proofs.IDX,
    MlDsaOpt65.Proofs.ACC, MlDsaOpt65.Proofs.HP, MlDsaOpt65.Proofs.FIN, MlDsaOpt65.Proofs.RHO1,
    MlDsaOpt65.Proofs.CB, MlDsaOpt65.Proofs.TRL, MlDsaOpt65.Proofs.MU, MlDsaOpt65.Proofs.BK, TT,
    MlDsaOpt65.Proofs.SP, MlDsaOpt65.Proofs.TOP]
  omega))

theorem ks4_congr {m : ByteArray} {S S' : Nat → Fips202.SpongeState} (h : KS4 m S)
    (hS : ∀ k, k < 4 → S k = S' k) : KS4 m S' := fun x hx => by
  rw [h x hx]; exact il_congr fun k hk => by rw [hS k hk]

theorem ks4_frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (h : KS4 m S) (hf : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S := fun x hx => by
  rw [word_frame hf ha (a := KS + 32 * x) (by omega) (by omega)]; exact h x hx

theorem rc4_frame {m m' : ByteArray} {rs : List (Nat × Nat)} (h : RC4Table m) (hf : FrameExcept m m' rs)
    (ha : Avoids rs RC4 (RC4 + 768)) : RC4Table m' := RC4Table.frame h hf ha

theorem pack4_congr {v w : Nat → Nat} (h : ∀ k, k < 4 → v k = w k) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem flagWord_congr {F G : Nat → Fips202.SpongeState} (h : ∀ k, k < 4 → F k = G k) (g : Nat) :
    flagWord F g = flagWord G g := by
  unfold flagWord
  have e : ((List.range 8).map fun i => pack4 fun k => cand (F k) (8 * g + i) + 2 ^ 23 - Fips204.q) =
      (List.range 8).map fun i => pack4 fun k => cand (G k) (8 * g + i) + 2 ^ 23 - Fips204.q :=
    List.map_congr_left fun i _ => pack4_congr fun k hk => by rw [h k hk]
  rw [e]

/-- Blocks `0 … n − 1` of a SIMD group, block `b` made from the slot states `St b`. -/
def Blocks (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) (n : Nat) : Prop :=
  ∀ b, b < n → (∀ i, i < 56 → word m (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i) ∧
    (∀ g, g < 7 → word m (FL + 224 * b + 32 * g) = flagWord (St b) g)

theorem Blocks.zero (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) : Blocks m St 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem Blocks.frame {m m' : ByteArray} {St : Nat → Nat → Fips202.SpongeState} {n : Nat}
    {rs : List (Nat × Nat)} (h : Blocks m St n) (hf : FrameExcept m m' rs)
    (ha : Avoids rs ABUF (ABUF + 1792 * n)) (hb : Avoids rs FL (FL + 224 * n)) : Blocks m' St n :=
  fun b hbn => ⟨fun i hi => by
      rw [word_frame hf ha (a := ABUF + 1792 * b + 32 * i) (by omega) (by omega)]; exact (h b hbn).1 i hi,
    fun g hg => by
      rw [word_frame hf hb (a := FL + 224 * b + 32 * g) (by omega) (by omega)]; exact (h b hbn).2 g hg⟩

theorem Blocks.pending {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState} (h : Blocks m St 5)
    {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState} (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I)
    (h6 : word m HAVE6 = 0) {S : Nat → Fips202.SpongeState} (hS : S sl = permN 5 I) :
    MlDsaOpt65.Proofs.Pending m S sl I :=
  pending_of_blocks hsl hSt (fun b hb => (h b hb).1) (fun b hb => (h b hb).2) h6 hS

theorem sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b ≤ 5)
    (g1 : Reach (callState s pc0 stk m) (callState s 21901 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 9811 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : Blocks m St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ Blocks m' St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * b, ABUF + 1792 * b + 1792),
        (FL + 224 * b, FL + 224 * b + 224)] ∧
      Reach (callState s pc0 stk m) (callState s r2 [fb] m') (c1 + Gas.kf4 + c2 + Gas.blk) := by
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := [fb])
    (retOK_main (by decide) (by simp) hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blk_call hs (ret := r2) (tail := [fb])
    (retOK_main (by decide) (by simp) hj2 hr2) m1 hb
  obtain ⟨hA, hF⟩ := hbk _ (sized4_permute hS) hks1
  have ha2 : Avoids [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS, ABUF, FL]; omega
  refine ⟨m2, ks4_frame hks1 hf2 ha2, fun b' hb' => ?_, rc4_frame (rc4_frame hrc hf1 (by s4_frame)) hf2
    (by simp only [avoids_cons, avoids_nil, and_true, RC4, ABUF, FL]; omega), FrameExcept.trans hf1 hf2,
    ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = b
  · subst hbb
    exact ⟨fun i hi => by rw [hA i hi]; exact pack4_congr fun k hk => by rw [hSt k hk],
      fun g hg => by rw [hF g hg]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · have h1 := (hB.frame hf1 (by s4_frame) (by s4_frame)).frame hf2
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
    exact h1 b' (by omega)

/-! ## `trabs` on the `tr` slot -/

/-- `trabs`'s post with `kp = 0`, `sh = 3`, normalised. -/
theorem trabs_norm {m m' : ByteArray} {cd : ByteArray} {off lm n4 : Nat}
    (hpost : ∀ x, x < 25 → word m' (KS + 32 * x) =
      if 0 ≤ KS + 32 * x ∧ KS + 32 * x < 0 + 128 * n4 then
        word m (KS + 32 * x) ^^^ spread (trLane cd off lm n4 ((KS + 32 * x - 0) / 32)) * 2 ^ 3
      else word m (KS + 32 * x)) :
    ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * n4 then trLane cd off lm n4 x else 0) * 2 ^ 3 := by
  intro x hx
  rw [hpost x hx]
  by_cases h : x < 4 * n4
  · rw [if_pos (by unfold KS; omega), if_pos h, show (KS + 32 * x - 0) / 32 = x by unfold KS; omega]
  · rw [if_neg (by unfold KS; omega), if_neg h, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem trLane_lt (cd : ByteArray) (off lm n4 u : Nat) : trLane cd off lm n4 u < 2 ^ 64 := by
  unfold trLane; exact Nat.mod_lt _ (by norm_num)

/-- A full block `j < 14` of the padded public key, absorbed into slot 3. -/
theorem ks4_trabs_full {m m' : ByteArray} {cd : ByteArray} (hcd : CTOFF ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {j : Nat} (hj : j < 14)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 5 then
        trLane cd (136 * j) 0xffffffffffffffff000000000000000000000000000000000000000000000000 5 x
        else 0) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then
      Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (j * 136) (S 3) else S k := by
  refine ks4_xor_slot (by norm_num) hks _ (fun x _ => by
    split
    · exact trLane_lt _ _ _ _ _
    · norm_num) hw _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), if_pos (by omega), trLane_eq cd lm_top1,
      if_neg (by omega), le64_padPk_full hcd (by omega), Nat.mul_comm j]
  · rw [if_neg (by norm_num; omega)]
    by_cases h20 : x < 20
    · rw [if_pos (by omega), trLane_eq cd lm_top1, if_pos (by omega), Nat.xor_zero]
    · rw [if_neg (by omega), Nat.xor_zero]

theorem spread_xor_shift (a b : Nat) :
    spread a * 2 ^ 3 ^^^ spread b * 2 ^ 3 = spread (a ^^^ b) * 2 ^ 3 := by
  rw [spread_mul_two_pow _ (by norm_num), spread_mul_two_pow _ (by norm_num),
    spread_mul_two_pow _ (by norm_num), il_xor]
  exact il_congr fun k _ => by split <;> simp

/-- The last block of the padded public key (`trabs` with two groups, then the
two padding xors), absorbed into slot 3. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : CTOFF ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then
      Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (14 * 136) (S 3) else S k := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 2 then
        trLane cd 1904 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 2 x
        else 0) ^^^ ((if x = 6 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, spread_xor_shift]) _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS 3 (by omega)) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), show 14 * 136 + 8 * x = 1904 + 8 * x by omega,
      le64_padPk_last hcd h17]
    congr 1
    by_cases h6 : x < 6
    · rw [if_pos h6, if_pos (by omega), trLane_eq cd lm_top2, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), Nat.xor_zero, Nat.xor_zero]
    · rw [if_neg h6]
      by_cases hx6 : x = 6
      · subst hx6; rw [trLane_eq cd lm_top2]; norm_num
      · by_cases hx16 : x = 16
        · subst hx16; norm_num
        · simp only [if_neg hx6, if_neg hx16, Nat.xor_zero]
          by_cases h8 : x < 8
          · rw [if_pos h8, trLane_eq cd lm_top2, if_pos (by omega)]
          · rw [if_neg h8]
  · rw [if_neg (by norm_num; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

/-- One absorbing squeeze of the `tr` slot: glue, `trabs` (full block `j`),
glue, `kf4`, glue, `blk b`. -/
theorem absorb_round {s : State} (hs : Ctx s) (hcd : CTOFF ≤ s.executionEnv.calldata.size)
    {fb : UInt256} {m : ByteArray} {pc0 r0 r1 r2 c0 c1 c2 b j off : Nat} (hb : b ≤ 5) (hj : j < 14)
    (hoff : off = 136 * j)
    (g0 : Reach (callState s pc0 [fb] m) (callState s 12455
      [wd 0, wd 0xffffffffffffffff000000000000000000000000000000000000000000000000, wd 5, wd 3, wd off,
        wd r0, fb] m) c0)
    (g1 : ∀ m', Reach (callState s r0 [fb] m') (callState s 21901 [wd r1, fb] m') c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 9811 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
    (hj0 : Decode.isValidJumpDest optBytecode r0 = true) (hr0 : r0 < 2 ^ 16)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : Blocks m St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (if k = 3 then
      Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S 3)
      else S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (if k = 3 then
        Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S 3)
        else S k)) ∧
      Blocks m' St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' ([(0, 0 + 128 * 5)] ++ [(KS, KS + 800), (KB, KB + 800),
        (ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)]) ∧
      Reach (callState s pc0 [fb] m) (callState s r2 [fb] m')
        (c0 + Gas.trabs 5 + (c1 + Gas.kf4 + c2 + Gas.blk)) := by
  obtain ⟨m1, hw, hf1, hc1⟩ := trabs_call hs (ret := r0) (tail := [fb])
    (retOK_main (by decide) (by simp) hj0 hr0) m (off := off) (sh := 3) (n4 := 5)
    (lm := 0xffffffffffffffff000000000000000000000000000000000000000000000000) (kp := 0)
    (by subst hoff; omega) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have hks1 := ks4_trabs_full hcd hS hks hj (by subst hoff; exact trabs_norm hw)
  have hS1 : Sized4 fun k => if k = 3 then
      Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S 3)
      else S k := fun k hk => by
    dsimp only
    split
    · rw [xorBlock_size]; exact hS 3 (by omega)
    · exact hS k hk
  have ha : Avoids [(0, 0 + 128 * 5)] ABUF (ABUF + 1792 * b) := by
    simp only [avoids_cons, avoids_nil, and_true, ABUF]; omega
  have hb' : Avoids [(0, 0 + 128 * 5)] FL (FL + 224 * b) := by
    simp only [avoids_cons, avoids_nil, and_true, FL]; omega
  obtain ⟨m2, hks2, hB2, hrc2, hf2, hc2⟩ := kb_round hs hb (g1 m1) g2 hj1 hr1 hj2 hr2
    (rc4_frame hrc hf1 (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega)) hS1 hks1
    (hB.frame hf1 ha hb') hSt
  exact ⟨m2, hks2, hB2, hrc2, FrameExcept.trans hf1 hf2, (g0.trans hc1).trans hc2⟩

/-! ## The row-group-1 accumulator (`AccInst1`) -/

theorem okIUpTo_get {cd : ByteArray} :
    ∀ {n : Nat}, okIUpTo cd n = true → ∀ i, i < n → okI cd i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [okIUpTo, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact okIUpTo_get h.1 i hi
    · exact h.2

theorem okIUpTo_of_get {cd : ByteArray} :
    ∀ {n : Nat}, (∀ i, i < n → okI cd i = true) → okIUpTo cd n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [okIUpTo, Bool.and_eq_true]
    exact ⟨okIUpTo_of_get fun i hi => h i (by omega), h n (by omega)⟩

/-- Instance `2 s + j` is `A[4 + j][s]`. -/
theorem okIUpTo_aOf {cd : ByteArray} {n : Nat} (h : okIUpTo cd n = true) {j s : Nat} (hj : j < 2)
    (hs : 2 * s + j < n) : (aOf cd (4 + j) s).isSome = true := by
  have := okIUpTo_get h (2 * s + j) hs
  unfold okI at this
  rwa [show (2 * s + j) % 2 = j by omega, show (2 * s + j) / 2 = s by omega] at this

theorem lanes_lo2 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    lane (a + 2 ^ 64 * b) 0 = a ∧ lane (a + 2 ^ 64 * b) 1 = b ∧ lane (a + 2 ^ 64 * b) 2 = 0 ∧
      lane (a + 2 ^ 64 * b) 3 = 0 := by
  unfold lane
  norm_num at ha hb ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem word_lo2 {w : Nat} (hw : w < 2 ^ 256) (h2 : lane w 2 = 0) (h3 : lane w 3 = 0) :
    w = lane w 0 + 2 ^ 64 * lane w 1 := by
  unfold lane at *
  norm_num at *
  omega

theorem mod128_lanes (X : Nat) : X % 2 ^ 128 = lane X 0 + 2 ^ 64 * lane X 1 := by
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
  unfold lane; simp

theorem div64mod128_lanes (X : Nat) : X / 2 ^ 64 % 2 ^ 128 = lane X 1 + 2 ^ 64 * lane X 2 := by
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
  unfold lane
  rw [Nat.div_div_eq_div_mul]
  norm_num

/-- `ẑ_k` (`k < 4`) is lane `k` of `ZH`. -/
theorem zhLane_lo {m : ByteArray} {k : Nat} (hk : k < 4) (t : Nat) :
    zhLane m k t = lane (word m (ZH + 32 * t)) k := by
  unfold zhLane zhAddr
  rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.mul_zero, Nat.add_zero]

/-- `ẑ_4` is lane 0 of `ZH2`. -/
theorem zhLane_four (m : ByteArray) (t : Nat) : zhLane m 4 t = lane (word m (ZH + 0x2000 + 32 * t)) 0 := rfl

/-- `pass3x5` / `pass3x7`'s product: lanes 0, 1 times `z0`, lane 2 moved to lane 0 times `z1`. -/
theorem p5_eq (w X z0 z1 : Nat) :
    w + X % 2 ^ 128 * z0 + lane X 2 * z1 =
      w + ((lane X 0 * z0 + lane X 2 * z1) + 2 ^ 64 * (lane X 1 * z0)) := by
  rw [mod128_lanes]; ring

/-- `pass3x6`'s product: lane 0 moved to lane 1 times `z1`, lanes 1, 2 moved to
lanes 0, 1 times `z2`. -/
theorem p6_eq (w X z1 z2 : Nat) :
    w + lane X 0 * 2 ^ 64 * z1 + X / 2 ^ 64 % 2 ^ 128 * z2 =
      w + (lane X 1 * z2 + 2 ^ 64 * (lane X 0 * z1 + lane X 2 * z2)) := by
  rw [div64mod128_lanes]; ring

/-- `pass3x8`'s product: lane 0 moved to lane 1 times `z`. -/
theorem p8_eq (w X z : Nat) : w + lane X 0 * 2 ^ 64 * z = w + (0 + 2 ^ 64 * (lane X 0 * z)) := by
  ring

theorem accSum_succ (cd m : ByteArray) (r t n : Nat) :
    accSum cd m r t (n + 1) = accSum cd m r t n + ((aD cd r n)[t]!).toNat * zhLane m n t := rfl

/-- The row-group-1 accumulator starts zero. -/
theorem accInst1_zero {m : ByteArray} {cd : ByteArray} (hz : ZeroOn m (ACC + 0x2000) HP) :
    AccInst1 m cd 0 := fun _ t ht => by
  rw [word_zero_of_zeroOn hz (by omega) (by unfold ACC HP; omega)]
  unfold lane
  simp [accSum]

/-- The instances `n ≤ i < n'` add `D0` to lane 0 (row 4) and `D1` to lane 1 (row 5). -/
theorem accInst1_step {cd m m' : ByteArray} {n n' : Nat} (hn : n ≤ n') (hn' : n' ≤ 10)
    (hacc : AccInst1 m cd n) (hz : ZHatAt m cd)
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    {D0 D1 : Nat → Nat}
    (hD : okIUpTo cd n' = true → ∀ t, t < 256 →
      accSum cd m 4 t ((n + 1) / 2) + D0 t = accSum cd m 4 t ((n' + 1) / 2) ∧
      accSum cd m 5 t (n / 2) + D1 t = accSum cd m 5 t (n' / 2))
    (hpost : okIUpTo cd n' = true → ∀ t, t < 256 → word m' (ACC + 0x2000 + 32 * t) =
      (word m (ACC + 0x2000 + 32 * t) + (D0 t + 2 ^ 64 * D1 t)) % 2 ^ 256) :
    AccInst1 m' cd n' := by
  intro hok t ht
  have hok0 : okIUpTo cd n = true := okIUpTo_of_get fun i hi => okIUpTo_get hok i (by omega)
  obtain ⟨h0, h1, h2, h3⟩ := hacc hok0 t ht
  obtain ⟨e0, e1⟩ := hD hok t ht
  have hzt : ∀ k, k < 5 → zhLane m k t < 2 ^ 28 := fun k hk => (hz k hk t ht).1
  have b0 : accSum cd m 4 t ((n' + 1) / 2) ≤ (n' + 1) / 2 * 2 ^ 51 :=
    s3_accSum_le ht hzt _ (by omega) fun s hs => okIUpTo_aOf hok (j := 0) (by norm_num) (by omega)
  have b1 : accSum cd m 5 t (n' / 2) ≤ n' / 2 * 2 ^ 51 :=
    s3_accSum_le ht hzt _ (by omega) fun s hs => okIUpTo_aOf hok (j := 1) (by norm_num) (by omega)
  have c0 : (n' + 1) / 2 * 2 ^ 51 ≤ 5 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
  have c1 : n' / 2 * 2 ^ 51 ≤ 5 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
  have l0 : accSum cd m 4 t ((n' + 1) / 2) < 2 ^ 64 := by
    have : (5 : Nat) * 2 ^ 51 < 2 ^ 64 := by norm_num
    omega
  have l1 : accSum cd m 5 t (n' / 2) < 2 ^ 64 := by
    have : (5 : Nat) * 2 ^ 51 < 2 ^ 64 := by norm_num
    omega
  have hw := word_lo2 (word_lt m (ACC + 0x2000 + 32 * t)) h2 h3
  rw [h0, h1] at hw
  have hlt : accSum cd m 4 t ((n' + 1) / 2) + 2 ^ 64 * accSum cd m 5 t (n' / 2) < 2 ^ 256 := by
    norm_num at l0 l1 ⊢; omega
  have hnew : word m' (ACC + 0x2000 + 32 * t) =
      accSum cd m 4 t ((n' + 1) / 2) + 2 ^ 64 * accSum cd m 5 t (n' / 2) := by
    have e : ∀ a b c d : Nat, a + 2 ^ 64 * b + (c + 2 ^ 64 * d) = a + c + 2 ^ 64 * (b + d) :=
      fun a b c d => by ring
    rw [hpost hok t ht, hw, ← e0, ← e1, e]
    exact Nat.mod_eq_of_lt (by rw [e0, e1]; exact hlt)
  obtain ⟨q0, q1, q2, q3⟩ := lanes_lo2 l0 l1
  rw [hnew, s3_accSum_congr (r := 4) ((n' + 1) / 2) (fun k hk => hzh k (by omega) t ht),
    s3_accSum_congr (r := 5) (n' / 2) (fun k hk => hzh k (by omega) t ht)]
  exact ⟨q0, q1, q2, q3⟩

/-- `AccCols0` survives a frame that keeps `ACC` and `ẑ`. -/
theorem accCols0_frame {m m' : ByteArray} {cd : ByteArray}
    (h : AccCols0 m cd 5) (hacc : ∀ t, t < 256 → word m' (ACC + 32 * t) = word m (ACC + 32 * t))
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : AccCols0 m' cd 5 := by
  intro hok t ht
  rw [hacc t ht, h hok t ht]
  exact pack4_congr fun r _ => s3_accSum_congr 5 (fun k hk => hzh k hk t ht) |>.symm

/-! ## Slots of the mixed groups -/

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    MlDsaOpt65.Proofs.aI (seedA cd r col) = aOf cd r col :=
  GroupP.aI_aSeed hcd r col

/-- The seed state of row-group-1 instance `i` (`A[4 + i % 2][i / 2]`). -/
def seedI (cd : ByteArray) (i : Nat) : Fips202.SpongeState := seedA cd (4 + i % 2) (i / 2)

/-- Slots 0–2 of a three-instance group: instances `i0, i0 + 1, i0 + 2`. -/
def Itr (cd : ByteArray) (i0 k : Nat) : Fips202.SpongeState := seedI cd (i0 + k)

theorem Itr_sized (cd : ByteArray) (i0 : Nat) : ∀ k, k < 3 → (Itr cd i0 k).size = 25 :=
  fun _ _ => seedState_size _ _

theorem okI_eq {cd : ByteArray} (hcd : 32 ≤ cd.size) (i : Nat) :
    (MlDsaOpt65.Proofs.aI (seedI cd i)).isSome = okI cd i := by
  unfold seedI okI; rw [aI_seedA hcd]

/-- `gfix`'s lane `sl` (active, holding a valid instance `i`). -/
theorem gfix_lane {cd m' : ByteArray} (hcd : 32 ≤ cd.size) {amask sl i : Nat}
    {I : Nat → Fips202.SpongeState} (hsl : sl < 4) (hbit : amask.testBit sl = true)
    (hI : I sl = seedI cd i)
    (hlanes : ∀ sl, sl < 4 → amask.testBit sl = true → ∀ a, MlDsaOpt65.Proofs.aI (I sl) = some a →
      ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat)
    (hok : okI cd i = true) {t : Nat} (ht : t < 256) :
    lane (word m' (ABUF + 32 * t)) sl = ((aD cd (4 + i % 2) (i / 2))[t]!).toNat := by
  unfold okI at hok
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok
  rw [hlanes sl hsl hbit a (by rw [hI]; unfold seedI; rw [aI_seedA hcd]; exact ha) t ht]
  unfold aD; rw [ha]; rfl

/-- `gfix 7`'s flag on a three-instance group. -/
theorem gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (i0 : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl || (MlDsaOpt65.Proofs.aI (Itr cd i0 sl)).isSome) =
      (okI cd i0 && okI cd (i0 + 1) && okI cd (i0 + 2)) := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, Itr, okI_eq hcd,
    Nat.add_zero, Bool.and_assoc]

/-- Slots of a `tr`-rider group: slots `0 … 2` squeeze from the seeds `I`,
slot 3 is the `tr` sponge after `j0 + b` blocks. -/
def XT (cd : ByteArray) (I : Nat → Fips202.SpongeState) (j0 b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (I k) else absorbPre 136 (padPk cd) (j0 + b)

theorem XT_sized (cd : ByteArray) {I : Nat → Fips202.SpongeState} (hI : ∀ k, k < 3 → (I k).size = 25)
    (j0 b : Nat) : Sized4 (XT cd I j0 b) := fun k _ => by
  unfold XT; split
  · exact permN_size (hI k (by omega)) b
  · exact absorbPre_size _ _ _

/-- After absorbing block `j0 + b` into slot 3. -/
def YT (cd : ByteArray) (I : Nat → Fips202.SpongeState) (j0 b k : Nat) : Fips202.SpongeState :=
  if k = 3 then Fips202.xorBlock 136 (padPk cd) ((j0 + b) * 136) (XT cd I j0 b 3) else XT cd I j0 b k

theorem YT_sized (cd : ByteArray) {I : Nat → Fips202.SpongeState} (hI : ∀ k, k < 3 → (I k).size = 25)
    (j0 b : Nat) : Sized4 (YT cd I j0 b) := fun k hk => by
  unfold YT; split
  · rw [xorBlock_size]; exact XT_sized cd hI j0 b 3 (by omega)
  · exact XT_sized cd hI j0 b k hk

theorem permute_YT (cd : ByteArray) (I : Nat → Fips202.SpongeState) (j0 b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (YT cd I j0 b k) = XT cd I j0 (b + 1) k := by
  unfold YT XT
  by_cases h3 : k = 3
  · subst h3; simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), permN_succ]

theorem trSlot_of {m : ByteArray} {cd : ByteArray} {I : Nat → Fips202.SpongeState}
    (hI : ∀ k, k < 3 → (I k).size = 25) {j0 b n : Nat} (hn : j0 + b = n) (hks : KS4 m (XT cd I j0 b)) :
    TrSlot m cd n :=
  ⟨XT cd I j0 b, XT_sized cd hI j0 b, hks, by unfold XT; rw [if_neg (by decide), hn]⟩

/-- `ginit`'s keep mask of groups 6, 7: slot 3. -/
theorem keep8 : (0x8888888888888888888888888888888888888888888888888888888888888888 : Nat) =
    il fun k => if (8 : Nat).testBit k then M64 else 0 := by decide +kernel

/-- `ginit [keep, 7, 0, l4]` of groups 5–7: slots 0–2 fresh with the seeds of the
instances `i0, i0 + 1, i0 + 2`; slot 3 the `tr` sponge after `j0` blocks, kept
(`kmask = 8`) or fresh (`kmask = 0`, `j0 = 0`). -/
theorem ginit_tr {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState} {keep kmask j0 i0 : Nat}
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hk : ∀ k, k < 3 → kmask.testBit k = false)
    (h3 : kmask.testBit 3 = true → S 3 = absorbPre 136 (padPk s.executionEnv.calldata) j0)
    (h3' : kmask.testBit 3 = false → j0 = 0) (hi0 : i0 < 8)
    {pc0 r c0 l4 : Nat} {b : Bool}
    (hl4 : l4 = il fun k => if k < 3 then (i0 + k) / 2 + 256 * (4 + (i0 + k) % 2) + 0x1F0000 else 0)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 12015 [wd l4, wd 0, wd 7, wd keep, wd r, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) :
    ∃ m1, KS4 m1 (XT s.executionEnv.calldata (Itr s.executionEnv.calldata i0) j0 0) ∧
      word m1 HAVE6 = 0 ∧ FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s r [flag b] m1) (c0 + Gas.ginit) := by
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho h3
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  have hkeep' : keep < 2 ^ 256 := by rw [hkeep]; exact il_lt _
  have hl4' : l4 < 2 ^ 256 := by rw [hl4]; exact il_lt _
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := r) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0 (keep := keep) (amult := 7) (cmult := 0) (l4 := l4)
    hkeep' (by norm_num) (by norm_num) hl4'
  have hrho0 := Rho1At.frame hrho hf0 (by s4_frame)
  have hbit3 : ∀ k, k < 4 → kmask.testBit k = true → k = 3 := fun k hk' hb' => by
    by_contra hne
    rw [hk k (by omega)] at hb'
    exact absurd hb' (by decide)
  have hks1 : KS4 m1 (XT cd (Itr cd i0) j0 0) :=
    ks4_ginit (kmask := kmask)
      (L := fun k => if k < 3 then (i0 + k) / 2 + 256 * (4 + (i0 + k) % 2) + 0x1F0000 else 0)
      (ρ := fun x => le64 cd (8 * x)) (c := fun x => le64 cd (CTOFF + 8 * x)) (S := S)
      (by norm_num) (by norm_num) hkeep hl4
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x hx => by
        rw [word_frame hf0 (a := KS + 32 * x) (lo := KS) (hi := KS + 800) (by s4_frame) (by omega)
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
          exact freshLane_aSeed hcd32 (fun _ _ => rfl) (by omega) (by omega)
            (by interval_cases k <;> decide) (by simp) (by rw [if_pos h3k]) hx
        · obtain rfl : k = 3 := by omega
          unfold XT
          rw [if_neg (by decide), h3' hb', Nat.add_zero, absorbPre_zero]
          exact freshLane_zero (by decide) (by decide) (by simp) x)
      hg
  refine ⟨m1, hks1, by
    rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by s4_frame) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- `gfix 7` after the five squeezes of a three-instance `tr`-rider group. -/
theorem gfix_trio {s : State} (hs : Ctx s) (hcd : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    {i0 j0 pc r c : Nat} {fb : UInt256}
    (gG : Reach (callState s pc [fb] m) (callState s 11685 [wd 7, wd r, fb] m) c)
    (hj : Decode.isValidJumpDest optBytecode r = true) (hr : r < 2 ^ 16) (hrc : RC4Table m)
    (hks : KS4 m (XT s.executionEnv.calldata (Itr s.executionEnv.calldata i0) j0 5))
    (hB : Blocks m (fun b k => Keccak.permute
      (YT s.executionEnv.calldata (Itr s.executionEnv.calldata i0) j0 b k)) 5)
    (h6 : word m HAVE6 = 0) :
    ∃ m', (∀ k, k < 3 → okI s.executionEnv.calldata (i0 + k) = true → ∀ t, t < 256 →
        lane (word m' (ABUF + 32 * t)) k =
          ((aD s.executionEnv.calldata (4 + (i0 + k) % 2) ((i0 + k) / 2))[t]!).toNat) ∧
      KS4 m' (XT s.executionEnv.calldata (Itr s.executionEnv.calldata i0) j0 5) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Reach (callState s pc [fb] m)
        (callState s r [flag (okI s.executionEnv.calldata i0 && okI s.executionEnv.calldata (i0 + 1) &&
          okI s.executionEnv.calldata (i0 + 2)), fb] m') (c + Gas.gfix 3) := by
  obtain ⟨m', hlanes, hks', -, hf, hc⟩ := gfix_call hs (ret := r) (tail := [fb])
    (retOK_main (by decide) (by simp) hj hr) m hrc (amask := 7) (by norm_num) 3 (by decide)
    (XT s.executionEnv.calldata (Itr s.executionEnv.calldata i0) j0 5)
    (XT_sized _ (Itr_sized _ i0) j0 5) hks (Itr s.executionEnv.calldata i0) h6
    (fun sl hsl hbit => by
      have hsl3 : sl < 3 := by
        by_contra h
        obtain rfl : sl = 3 := by omega
        exact absurd hbit (by decide)
      refine hB.pending hsl (fun b' hb' => ?_) h6 ?_
      · show Keccak.permute (YT _ _ j0 b' sl) = _
        rw [permute_YT _ _ j0 b' hsl]; unfold XT; rw [if_pos hsl3]
      · unfold XT; rw [if_pos hsl3])
  rw [gfix7_flag hcd] at hc
  refine ⟨m', fun k hk hok t ht => ?_, hks', hf, gG.trans hc⟩
  exact gfix_lane (I := Itr s.executionEnv.calldata i0) (i := i0 + k) (amask := 7) hcd (by omega)
    (by interval_cases k <;> decide) rfl hlanes hok ht

/-- Regions every mixed group writes. -/
def gbase : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800),
    (ACC + 0x2000, ACC + 0x4000)]

/-- The row-group-1 invariant after a mixed group (all but the new accumulator
carried by the frame). -/
theorem invR_next {cd m m' : ByteArray} {n : Nat} {ex : List (Nat × Nat)}
    (rc4 : RC4Table m) (rc1 : RC1Table m) (tbl : TblAt m) (zhat : ZHatAt m cd) (hp : HPAt m cd)
    (rho : Rho1At m cd) (acc0 : AccCols0 m cd 5) (zMisc : ZeroOn m MISC (MISC + 0x1e0))
    (zCw : ZeroOn m CW ABUF) (zIdx : ZeroOn m BASES ACC)
    (hf : FrameExcept m m' (gbase ++ ex)) (hex : Avoids ex RC4 (RHO1 + 320))
    (acc1 : AccInst1 m' cd n) : InvR cd m' n := by
  have ha : ∀ lo hi, RC4 ≤ lo → hi ≤ RHO1 + 320 → Avoids gbase lo hi → Avoids (gbase ++ ex) lo hi :=
    fun lo hi h1 h2 h => (avoids_append _ _ _ _).mpr ⟨h, hex.mono h1 h2⟩
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t := fun k hk t ht =>
    zhLane_frame hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)) hk ht
  exact ⟨RC4Table.frame rc4 hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    RC1Table.frame rc1 hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    TblAt.frame tbl hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    ZHatAt.frame zhat hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    HPAt.frame hp hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    Rho1At.frame rho hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    accCols0_frame acc0 (fun t ht => word_frame hf (lo := ACC) (hi := ACC + 0x2000)
      (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)) (by omega) (by omega)) hzh,
    acc1,
    ZeroOn.frame zMisc hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    ZeroOn.frame zCw hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    ZeroOn.frame zIdx hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame))⟩

end MlDsaOpt65.Proofs.S4
