import MlDsaOpt65.Main.S4.Math
import MlDsaOpt65.Math
import MlDsaOpt65.Fn.Keccak
import MlDsaOpt65.Fn.Blk
import MlDsaOpt65.Fn.Sponge
import MlDsaOpt65.Fn.Fix
import MlDsaOpt65.Fn.Group
set_option warningAsError true
/-!
# Building blocks of the mixed SIMD groups 5–8 (ML-DSA-65, WP S4)

As `MlDsaOpt44/Main/SegG234/Round.lean` for this artifact:

* `Blocks m St n`: the first `n` squeezed blocks of a group are in `ABUF` /
  `FL`, block `b` made from the slot states `St b`.
* `kb_round`: glue, `kf4`, glue, `blk b`.
* `ks4_trabs_full`, `ks4_trabs_last`, `absorb_round`: what `trabs` (and the
  final padding xors) do to the `tr` slot (slot 3).
* `accCols1_step`: one mixed group's `pass3` on the row-group-1 accumulator.
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

/-- Lane `sl` of the candidate word `t < 256` of five blocks. -/
theorem Blocks.lane {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState} (h : Blocks m St 5)
    {sl : Nat} (hsl : sl < 4) {t : Nat} (ht : t < 256) :
    lane (word m (ABUF + 32 * t)) sl < 2 ^ 23 := by
  have hb : t / 56 < 5 := by omega
  rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
    (h _ hb).1 _ (Nat.mod_lt _ (by norm_num)), lane_pack4_cand _ _ hsl]
  exact cand_lt _ _

theorem sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b ≤ 5)
    (g1 : Reach (callState s pc0 stk m) (callState s 20991 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 9857 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
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
    (g0 : Reach (callState s pc0 [fb] m) (callState s 12084
      [wd 0, wd 0xffffffffffffffff000000000000000000000000000000000000000000000000, wd 5, wd 3, wd off,
        wd r0, fb] m) c0)
    (g1 : ∀ m', Reach (callState s r0 [fb] m') (callState s 20991 [wd r1, fb] m') c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 9857 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
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

/-! ## The row-group-1 accumulator -/

theorem lane_pack4_lt64 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := lane_pack4_lt h hk

theorem pack4_lane_eq {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane; norm_num; omega

theorem accSum_congr {cd m m' : ByteArray} {t : Nat}
    (hzh : ∀ k, k < 5 → zhLane m' k t = zhLane m k t) (r : Nat) :
    ∀ n, n ≤ 5 → accSum cd m' r t n = accSum cd m r t n
  | 0, _ => rfl
  | n + 1, hn => by
    show accSum cd m' r t n + _ * zhLane m' n t = accSum cd m r t n + _ * zhLane m n t
    rw [accSum_congr hzh r n (by omega), hzh n (by omega)]

theorem aD_lt_of {cd : ByteArray} {r s : Nat} (h : (aOf cd r s).isSome = true) {t : Nat} (ht : t < 256) :
    ((aD cd r s)[t]!).toNat < 8380417 := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
  have hD : aD cd r s = a := by unfold aD; rw [ha]; rfl
  rw [hD]
  obtain ⟨-, hrange⟩ := rejNTTPoly_range _ a ha
  have := hrange t ht
  simp only [show (MlDsa.Fips204.q : Int) = 8380417 from rfl] at this
  omega

/-- Rows 4, 5 accumulate `≤ n · 2^51` over valid columns `s < n`. -/
theorem accSum1_le {cd m : ByteArray} {t : Nat} (ht : t < 256) (hz : ∀ k, k < 4 → zhLane m k t < 2 ^ 28)
    {j : Nat} (hj : j < 2) : ∀ n, n ≤ 4 → okUpTo1 cd n = true → accSum cd m (4 + j) t n ≤ n * 2 ^ 51
  | 0, _, _ => Nat.le_refl _
  | n + 1, hn, hok => by
    simp only [okUpTo1, okCol1, Bool.and_eq_true] at hok
    have ih := accSum1_le ht hz hj n (by omega) hok.1
    have hsome : (aOf cd (4 + j) n).isSome = true := by
      rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> subst h
      · exact hok.2.1
      · exact hok.2.2
    have h2 := hz n (by omega)
    have h1 := aD_lt_of hsome ht
    have h3 : ((aD cd (4 + j) n)[t]!).toNat * zhLane m n t < 2 ^ 23 * 2 ^ 28 :=
      Nat.mul_lt_mul'' (by omega) h2
    have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
    show accSum cd m (4 + j) t n + _ ≤ _
    omega

/-- One mixed group's `pass3` (column `n` of rows 4, 5 in lanes 0, 1; raw
candidates `< 2^23` in lanes 2, 3) on the row-group-1 accumulator. -/
theorem accCols1_step {m m' : ByteArray} {cd : ByteArray} {n : Nat} (hn : n < 4)
    (hacc : AccCols1 m cd n) (hz : ∀ k, k < 4 → ∀ t, t < 256 → zhLane m k t < 2 ^ 28)
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    {A : Nat → Nat}
    (hA : okCol1 cd n = true → ∀ t, t < 256 →
      (∀ j, j < 2 → lane (A t) j = ((aD cd (4 + j) n)[t]!).toNat) ∧
      (∀ j, 2 ≤ j → j < 4 → lane (A t) j < 2 ^ 23))
    (hAlt : ∀ t, A t < 2 ^ 256)
    (hpost : ∀ t, t < 256 → word m' (ACC + 0x2000 + 32 * t) =
      (word m (ACC + 0x2000 + 32 * t) + A t * lane (word m (ZH + 32 * t)) n) % 2 ^ 256) :
    AccCols1 m' cd (n + 1) := by
  intro hok t ht
  have hok' := hok
  simp only [okUpTo1, Bool.and_eq_true] at hok'
  obtain ⟨hl01, hl23⟩ := hacc hok'.1 t ht
  obtain ⟨hA01, hA23⟩ := hA hok'.2 t ht
  have hzn : lane (word m (ZH + 32 * t)) n = zhLane m n t := by
    unfold zhLane zhAddr; rw [Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn]; simp
  have hzl : zhLane m n t < 2 ^ 28 := hz n hn t ht
  -- lane values of the new word
  set w := word m (ACC + 0x2000 + 32 * t) with hw
  set z := zhLane m n t
  have hv : ∀ j, j < 4 → lane w j + lane (A t) j * z < 2 ^ 64 ∧
      (j < 2 → lane w j + lane (A t) j * z = accSum cd m (4 + j) t (n + 1)) ∧
      (2 ≤ j → lane w j + lane (A t) j * z ≤ (n + 1) * 2 ^ 51) := by
    intro j hj
    by_cases hj2 : j < 2
    · have hle := accSum1_le ht (fun k hk => hz k hk t ht) hj2 (n + 1) (by omega) hok
      have e : accSum cd m (4 + j) t (n + 1) = accSum cd m (4 + j) t n +
          ((aD cd (4 + j) n)[t]!).toNat * zhLane m n t := rfl
      have h1 : lane w j + lane (A t) j * z = accSum cd m (4 + j) t (n + 1) := by
        rw [hl01 j hj2, hA01 j hj2, e]
      refine ⟨?_, fun _ => h1, fun h => absurd h (by omega)⟩
      rw [h1]
      have : (n + 1) * 2 ^ 51 < 2 ^ 64 := by
        calc (n + 1) * 2 ^ 51 ≤ 4 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
          _ < 2 ^ 64 := by norm_num
      omega
    · have h1 := hl23 j (by omega) hj
      have h2 := hA23 j (by omega) hj
      have h3 : lane (A t) j * z < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul'' h2 hzl
      have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
      have h4 : (n + 1) * 2 ^ 51 < 2 ^ 64 := by
        calc (n + 1) * 2 ^ 51 ≤ 4 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
          _ < 2 ^ 64 := by norm_num
      refine ⟨by omega, fun h => absurd h hj2, fun _ => by omega⟩
  have hwlt : w < 2 ^ 256 := word_lt _ _
  have hsum : (w + A t * z) % 2 ^ 256 = pack4 fun j => lane w j + lane (A t) j * z := by
    calc (w + A t * z) % 2 ^ 256 =
        (pack4 (fun j => lane w j) + pack4 (fun j => lane (A t) j) * z) % 2 ^ 256 := by
          rw [pack4_lane_eq hwlt, pack4_lane_eq (hAlt t)]
      _ = _ := by rw [pack4_add_mul, Nat.mod_eq_of_lt (pack4_lt fun j hj => (hv j hj).1)]
  have hacc' : ∀ j, j < 4 → lane (word m' (ACC + 0x2000 + 32 * t)) j = lane w j + lane (A t) j * z := by
    intro j hj
    rw [hpost t ht, hzn, ← hw, hsum, lane_pack4_lt64 (fun k hk => (hv k hk).1) hj]
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_⟩
  · rw [hacc' j (by omega), (hv j (by omega)).2.1 hj]
    exact (accSum_congr (fun k hk => hzh k hk t ht) _ _ (by omega)).symm
  · rw [hacc' j hj']; exact (hv j hj').2.2 hj

/-- `AccCols0` survives a frame that keeps `ACC` and `ẑ`. -/
theorem accCols0_frame {m m' : ByteArray} {cd : ByteArray} {n : Nat} (hn : n ≤ 5)
    (h : AccCols0 m cd n) (hacc : ∀ t, t < 256 → word m' (ACC + 32 * t) = word m (ACC + 32 * t))
    (hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : AccCols0 m' cd n := by
  intro hok t ht
  rw [hacc t ht, h hok t ht]
  exact pack4_congr fun r _ => (accSum_congr (fun k hk => hzh k hk t ht) r n hn).symm

/-- The row-group-1 accumulator starts zero. -/
theorem accCols1_zero {m : ByteArray} {cd : ByteArray} (hz : ZeroOn m (ACC + 0x2000) HP) :
    AccCols1 m cd 0 := fun _ t ht => by
  rw [word_zero_of_zeroOn hz (by omega) (by unfold ACC HP; omega)]
  refine ⟨fun j _ => ?_, fun j _ _ => ?_⟩
  · unfold lane; simp; rfl
  · unfold lane; simp

/-! ## Slots of the mixed groups -/

/-- The seed state of `A[r][col]`. -/
def seedA (cd : ByteArray) (r col : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd r col)

theorem aI_seedA {cd : ByteArray} (hcd : 32 ≤ cd.size) (r col : Nat) :
    MlDsaOpt65.Proofs.aI (seedA cd r col) = aOf cd r col :=
  GroupP.aI_aSeed hcd r col

/-- `gfix 3`'s flag when slots 0, 1 hold the seeds of `A[4][col]`, `A[5][col]`. -/
theorem gfix3_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) {col : Nat} {I : Nat → Fips202.SpongeState}
    (h0 : I 0 = seedA cd 4 col) (h1 : I 1 = seedA cd 5 col) :
    ((List.range 4).all fun sl => !(3 : Nat).testBit sl || (MlDsaOpt65.Proofs.aI (I sl)).isSome) =
      okCol1 cd col := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (3 : Nat).testBit 0 = true by decide, show (3 : Nat).testBit 1 = true by decide,
    show (3 : Nat).testBit 2 = false by decide, show (3 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, h0, h1,
    aI_seedA hcd, okCol1]

/-- The `ABUF` words `pass3` reads after `gfix 3`: rows 4, 5 of column `col` in
lanes 0, 1, raw candidates in lanes 2, 3. -/
theorem gfix3_lanes {cd m6 m7 : ByteArray} (hcd : 32 ≤ cd.size) {col : Nat}
    {I : Nat → Fips202.SpongeState} (h0 : I 0 = seedA cd 4 col) (h1 : I 1 = seedA cd 5 col)
    (hlanes : ∀ sl, sl < 4 → (3 : Nat).testBit sl = true → ∀ a, MlDsaOpt65.Proofs.aI (I sl) = some a →
      ∀ t, t < 256 → lane (word m7 (ABUF + 32 * t)) sl = (a[t]!).toNat)
    (hkeep : ∀ sl, sl < 4 → (3 : Nat).testBit sl = false → ∀ t, t < 256 →
      lane (word m7 (ABUF + 32 * t)) sl = lane (word m6 (ABUF + 32 * t)) sl)
    {St : Nat → Nat → Fips202.SpongeState} (hB : Blocks m6 St 5) :
    okCol1 cd col = true → ∀ t, t < 256 →
      (∀ j, j < 2 → lane (word m7 (ABUF + 32 * t)) j = ((aD cd (4 + j) col)[t]!).toNat) ∧
      (∀ j, 2 ≤ j → j < 4 → lane (word m7 (ABUF + 32 * t)) j < 2 ^ 23) := by
  intro hok t ht
  simp only [okCol1, Bool.and_eq_true] at hok
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_⟩
  · have hs : (aOf cd (4 + j) col).isSome = true := by
      rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> subst h
      · exact hok.1
      · exact hok.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    have hI : MlDsaOpt65.Proofs.aI (I j) = some a := by
      rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> subst h
      · rw [h0, aI_seedA hcd]; exact ha
      · rw [h1, aI_seedA hcd]; exact ha
    rw [hlanes j (by omega) (by rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> subst h <;> decide)
      a hI t ht]
    unfold aD; rw [ha]; rfl
  · rw [hkeep j hj' (by
      rcases (show j = 2 ∨ j = 3 by omega) with h | h <;> subst h <;> decide) t ht]
    exact hB.lane hj' ht

/-- Regions every mixed group writes. -/
def gbase : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800),
    (ACC + 0x2000, ACC + 0x4000)]

/-- The row-group-1 invariant after a mixed group (all but the new
accumulator and `CB` carried by the frame). -/
theorem invR_next {cd m m' : ByteArray} {n : Nat} {ex : List (Nat × Nat)}
    (rc4 : RC4Table m) (rc1 : RC1Table m) (tbl : TblAt m) (zhat : ZHatAt m cd) (hp : HPAt m cd)
    (rho : Rho1At m cd) (acc0 : AccCols0 m cd 5) (zMisc : ZeroOn m MISC (MISC + 0x1e0))
    (zCw : ZeroOn m CW ABUF) (zIdx : ZeroOn m BASES ACC)
    (hf : FrameExcept m m' (gbase ++ ex)) (hex : Avoids ex RC4 (RHO1 + 320))
    (acc1 : AccCols1 m' cd n) (cb : CbAt m' cd) : InvR cd m' n := by
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
    accCols0_frame le_rfl acc0 (fun t ht => word_frame hf (lo := ACC) (hi := ACC + 0x2000)
      (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)) (by omega) (by omega)) hzh,
    acc1, cb,
    ZeroOn.frame zMisc hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    ZeroOn.frame zCw hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame)),
    ZeroOn.frame zIdx hf (ha _ _ (by s4_frame) (by s4_frame) (by unfold gbase; s4_frame))⟩

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

end MlDsaOpt65.Proofs.S4
