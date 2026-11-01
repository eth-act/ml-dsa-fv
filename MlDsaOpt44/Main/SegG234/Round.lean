import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Sponge
import MlDsaOpt44.Math.SpongeG234
set_option warningAsError true
/-!
# Building blocks of the mixed SIMD groups (`seg_g234`)

* `Blocks m St n`: the first `n` squeezed blocks of a group are in `ABUF` /
  `FL`, block `b` made from the slot states `St b`; `Blocks.frame`,
  `Blocks.pending`.
* `kb_round`: glue, `kf4`, glue, `blk b`.
* `ks4_trabs_full`, `ks4_trabs_last`: what `trabs` (and the final padding
  xors) do to the `tr` slot (slot 3): xor one padded block of `pk`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- `Avoids` side conditions on literal layout ranges (lists built with `++`). -/
macro "frame_tac" : tactic => `(tactic| (
  simp only [avoids_cons, avoids_nil, avoids_append, List.cons_append, List.nil_append, and_true, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW, ABUF, FL, ZH, BASES, IDX, ACC, HP, FIN,
    RHO1, CB, TRL, MU, BK, TT, SP, TOP, KZ]
  omega))

theorem KS4.congr {m : ByteArray} {S S' : Nat → Fips202.SpongeState} (h : KS4 m S)
    (hS : ∀ k, k < 4 → S k = S' k) : KS4 m S' := fun x hx => by
  rw [h x hx]; exact il_congr fun k hk => by rw [hS k hk]

theorem KS4.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (h : KS4 m S) (hf : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S := fun x hx => by
  rw [word_frame hf ha (a := KS + 32 * x) (by omega) (by omega)]; exact h x hx

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
    Pending m S sl I :=
  pending_of_blocks hsl hSt (fun b hb => (h b hb).1) (fun b hb => (h b hb).2) h6 hS

theorem sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b ≤ 5)
    (g1 : Reach (callState s pc0 stk m) (callState s 21570 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 8887 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
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
  refine ⟨m2, hks1.frame hf2 ha2, fun b' hb' => ?_, (hrc.frame hf1 (by avoids_tac)).frame hf2
    (by simp only [avoids_cons, avoids_nil, and_true, RC4, ABUF, FL]; omega), ?_,
    ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  · by_cases hbb : b' = b
    · subst hbb
      exact ⟨fun i hi => by rw [hA i hi]; exact pack4_congr fun k hk => by rw [hSt k hk],
        fun g hg => by rw [hF g hg]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
    · have h1 := (hB.frame hf1 (by avoids_tac) (by avoids_tac)).frame hf2
        (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
        (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
      exact h1 b' (by omega)
  · have := FrameExcept.trans hf1 hf2
    exact this

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

/-- A full block `j < 9` of the padded public key, absorbed into slot 3. -/
theorem ks4_trabs_full {m m' : ByteArray} {cd : ByteArray} (hcd : 1312 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {j : Nat} (hj : j < 9)
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

/-- The last block of the padded public key (`trabs` with three groups, then
the two padding xors), absorbed into slot 3. -/
theorem ks4_trabs_last {m m' : ByteArray} {cd : ByteArray} (hcd : 1312 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) * 2 ^ 3 ^^^ spread ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)) * 2 ^ 3) :
    KS4 m' fun k => if k = 3 then
      Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (9 * 136) (S 3) else S k := by
  have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
  refine ks4_xor_slot (by norm_num) hks (fun x => (if x < 4 * 3 then
        trLane cd 1224 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 3 x
        else 0) ^^^ ((if x = 11 then 31 else 0) ^^^ (if x = 16 then 2 ^ 63 else 0)))
    (fun x _ => xor_lt64 (by split; exact trLane_lt _ _ _ _ _; norm_num)
      (xor_lt64 (by split <;> norm_num) (by split <;> omega)))
    (fun x hx => by rw [hw x hx, Nat.xor_assoc, spread_xor_shift]) _ ?_
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

/-- One absorbing squeeze of the `tr` slot: glue, `trabs` (full block `j`),
glue, `kf4`, glue, `blk b`. -/
theorem absorb_round {s : State} (hs : Ctx s) (hcd : 1312 ≤ s.executionEnv.calldata.size)
    {fb : UInt256} {m : ByteArray} {pc0 r0 r1 r2 c0 c1 c2 b j off : Nat} (hb : b ≤ 5) (hj : j < 9)
    (hoff : off = 136 * j)
    (g0 : Reach (callState s pc0 [fb] m) (callState s 11497
      [wd 0, wd 0xffffffffffffffff000000000000000000000000000000000000000000000000, wd 5, wd 3, wd off,
        wd r0, fb] m) c0)
    (g1 : ∀ m', Reach (callState s r0 [fb] m') (callState s 21570 [wd r1, fb] m') c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 8887 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
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
    (hrc.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega)) hS1 hks1
    (hB.frame hf1 ha hb') hSt
  exact ⟨m2, hks2, hB2, hrc2, FrameExcept.trans hf1 hf2, (g0.trans hc1).trans hc2⟩

end MlDsaOpt44.Proofs
