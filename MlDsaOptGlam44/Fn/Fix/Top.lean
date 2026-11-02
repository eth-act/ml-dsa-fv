import MlDsaOptGlam44.Fn.Fix.Phase
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOptGlam44.Fn.Blk
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Fix/Top.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `fix`: first-flag scan, sixth squeeze, flag words
-/

namespace MlDsaOptGlam44.Proofs.Fix

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Fix

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-! ## First-flag scan -/

/-- Scan layout of slot `sl`. -/
abbrev Sc (s : State) (ret : Nat) (tail : List UInt256) (sl rp : Nat) (M : ByteArray) : State :=
  sst s ret tail (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl) rp M

theorem scan_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htail : tail.length ≤ 960) (hsz : 2616 ≤ s.activeWords.toNat) {sl : Nat}
    (M : ByteArray) (g0 : Nat) (hg0 : g0 < 32)
    (h0 : ∀ g, g < g0 → word M (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 0) :
    ∀ d g, g + d = g0 →
      Reach (Sc s ret tail sl (20480 + 256 * g) M) (Sc s ret tail sl (20480 + 256 * g0) M) (d * 55)
  | 0, g, h => by
    rw [show g = g0 by omega]; exact (Reach.refl _).mono (by omega)
  | d + 1, g, h => by
    have h1 := fx_scan_next (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) (qsv sl)
      (fmv sl) (20480 + 256 * g) (by omega) (by rw [flag_addr, fmv_and]; exact h0 g (by omega))
    rw [show 256 + (20480 + 256 * g) = 20480 + 256 * (g + 1) by omega] at h1
    exact (h1.trans (scan_reach hs htail hsz M g0 hg0 h0 d (g + 1) (by omega))).mono
      (by rw [Nat.succ_mul]; omega)

/-! ## Memory facts -/

theorem byteAt_readPadded' (m : ByteArray) (p n i : Nat) :
    byteAt (MachineState.readPadded m p n) i = if i < n then byteAt m (p + i) else 0 := by
  rw [byteAt_eq_getD, EvmProof.Memory.readPadded_getElem?_getD]
  split
  · rw [byteAt_eq_getD]
  · rfl

private theorem foldl_foldl_set_size {α β : Type} (l1 : List α) (l2 : List β) (f : α → β → Nat)
    (g : Array UInt64 → α → β → UInt64) (A : Array UInt64) :
    (l1.foldl (fun B a => l2.foldl (fun B a' => B.set! (f a a') (g B a a')) B) A).size = A.size := by
  induction l1 generalizing A with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    clear ih
    induction l2 generalizing A with
    | nil => rfl
    | cons a' l' ih' => rw [List.foldl_cons, ih', Array.set!, Array.size_setIfInBounds]

private theorem round_size (A : Array UInt64) (rc : UInt64) :
    (EvmSemantics.Crypto.Keccak.round A rc).size = 25 := by
  unfold EvmSemantics.Crypto.Keccak.round
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [Array.set!, Array.size_setIfInBounds, foldl_foldl_set_size]
  simp

theorem permute_size' {A : Array UInt64} (h : A.size = 25) :
    (EvmSemantics.Crypto.Keccak.permute A).size = 25 := by
  unfold EvmSemantics.Crypto.Keccak.permute
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize List.range' 0 24 1 = l
  induction l generalizing A with
  | nil => exact h
  | cons a l ih => rw [List.foldl_cons]; exact ih (round_size _ _)

set_option linter.unusedVariables false in  -- glam: trivial table
theorem rc4_frame {m m' : ByteArray} {rs : List (Nat × Nat)} (hr : RC4Table m)
    (h : FrameExcept m m' rs) (ha : Avoids rs RC4 (RC4 + 768)) : RC4Table m' := trivial  -- glam: no iota table

theorem ks4_frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (hr : KS4 m S) (h : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S :=
  fun x hx => by rw [h.word (ha.mono (by omega) (by omega))]; exact hr x hx

/-- Regions written by the squeeze path (`KS` is restored from `BK`). -/
def sqRegions : List (Nat × Nat) :=
  [(4064, 4096), (1024, 1824), (65280, 66080), (29440, 31232), (32352, 32576)]

/-- Close `Avoids` goals over literal regions. -/
macro "fx_av" : tactic => `(tactic| (
  simp only [avoids_cons, avoids_nil, avoids_append, and_true, List.cons_append, List.nil_append,
    EvmProof.Memory.readPadded_size, natToBytesPadded_size, KS, KB, RC4, HAVE6, ABUF, FL, BK, MlDsaOptGlam44.Proofs.Fix.sqRegions]
  omega))

/-! ## The sixth squeeze -/

theorem squeeze_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.fix ret tail) (htail : tail.length ≤ 960)
    (hsz : 2616 ≤ s.activeWords.toNat) (sl : Nat) (M : ByteArray) (hrc : RC4Table M)
    (h6 : word M 4064 = 0) (rp wp : Nat) :
    ∃ M5, Reach (G s ret tail sl 20716 29440 rp wp M) (G s ret tail sl 20355 31232 rp wp M5) 41122 ∧
      FrameExcept M M5 sqRegions ∧ word M5 4064 = 1 ∧
      ∀ S, Sized4 S → KS4 M S →
        (∀ i, i < 56 → word M5 (29440 + 32 * i) =
          pack4 fun k => cand (EvmSemantics.Crypto.Keccak.permute (S k)) i) ∧
        (∀ g, g < 7 → word M5 (32352 + 32 * g) =
          flagWord (fun k => EvmSemantics.Crypto.Keccak.permute (S k)) g) := by
  have hlen : ([wd wp, wd rp, wd 29440, wd (fmv sl), wd (qsv sl), wd (nmask sl), wd (lmask sl),
    wd (64 * sl), wd ret] ++ tail).length ≤ 1000 := by simp; omega
  have hmem : 66080 ≤ 32 * s.activeWords.toNat := by omega
  have hrok : ∀ B', B' = Stack.leaf → ∀ r', Decode.isValidJumpDest optBytecode r' = true → r' < 2 ^ 16 →
      RetOK B' r' ([wd wp, wd rp, wd 29440, wd (fmv sl), wd (qsv sl), wd (nmask sl), wd (lmask sl),
        wd (64 * sl), wd ret] ++ tail) := fun B' hB r' hj hr' =>
    hr.callee (by subst hB; simp [Stack.fix, Stack.kf4, Stack.blk, Stack.leaf]) hj hr'
  -- HAVE6 := 1, then KS → BK
  set M1 := MachineState.writeBytes M (Data.Bytes.natToBytesPadded 1 32) 4064 with hM1
  have h1 := fx_sq_pre (ret := ret) hs htail hsz M (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
    29440 rp wp (by decide) (by decide) h6
  set M2 := MachineState.writeBytes M1 (MachineState.readPadded M1 0 800) 65280 with hM2
  have h2 := Infra.reach_mcopy hs ⟨8909, by decide⟩ (pc := 20747) (d := 65280) (src := 0) (n := 800)
    (m := M1) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by omega) hlen
  have hf2 : FrameExcept M M2 [(4064, 4096), (65280, 66080)] :=
    (FrameExcept.trans (FrameExcept.mstore M 4064 1) (FrameExcept.writeBytes M1 _ 65280)).mono (by
      intro r hr
      simp only [EvmProof.Memory.readPadded_size, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(4064, 4096), by simp, by simp⟩
      · exact ⟨(65280, 66080), by simp, by simp⟩)
  have h3 := fx_sq_kf4 (ret := ret) hs htail hsz M2 (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
    29440 rp wp
  obtain ⟨M3, hk, hfk, hck⟩ := kf4_call hs (ret := 20755) (hrok _ rfl _
      (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) M2
    (rc4_frame hrc hf2 (by fx_av))
  have h5 := fx_sq_blk (ret := ret) hs htail hsz M3 (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
    29440 rp wp
  obtain ⟨M4, hb, hfb, hcb⟩ := blk_call hs (ret := 20769) (hrok _ rfl _
      (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) M3 (abp := 29440) (flp := 32352)
    (by simp [KS]) (by simp [TOP]) (by simp [KS]) (by simp [TOP]) (by omega)
  have h7 := fx_sq_post (ret := ret) hs htail hsz M4 (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
    29440 rp wp
  set M5 := MachineState.writeBytes M4 (MachineState.readPadded M4 65280 800) 0 with hM5
  have h8 := Infra.reach_mcopy hs ⟨8923, by decide⟩ (pc := 20777) (d := 0) (src := 65280) (n := 800)
    (m := M4) (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by omega) hlen
  have h9 := fx_cont (ret := ret) hs htail hsz M5 (64 * sl) (lmask sl) (nmask sl) (qsv sl) (fmv sl)
    29440 rp wp
  try rw [call_iff] at hck hcb
  have hreach := ((((((((h1.trans h2).trans h3).trans hck).trans h5).trans hcb).trans h7).trans
    h8).trans h9)
  have hw5 : ∀ a, 800 ≤ a → word M5 a = word M4 a := fun a ha =>
    word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; omega)
  refine ⟨M5, hreach.mono (by simp [Gas.kf4, Gas.blk]), ?_, ?_, ?_⟩
  · intro a ha
    by_cases hlo : a < 800
    · rw [hM5, byteAt_writeBytes, if_pos (by rw [EvmProof.Memory.readPadded_size]; omega),
        byteAt_readPadded', if_pos (by omega), Nat.sub_zero,
        hfb.byteAt (by fx_av), hfk.byteAt (by fx_av), hM2, byteAt_writeBytes,
        if_pos (by rw [EvmProof.Memory.readPadded_size]; omega), byteAt_readPadded', if_pos (by omega),
        show 65280 + a - 65280 = a by omega, Nat.zero_add]
      exact (FrameExcept.mstore M 4064 1).byteAt (by fx_av)
    · have := ha
      simp only [sqRegions, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at this
      rw [hM5, byteAt_writeBytes, if_neg (by rw [EvmProof.Memory.readPadded_size]; omega), hfb.byteAt (by fx_av), hfk.byteAt (by fx_av)]
      exact hf2.byteAt (by fx_av)
  · rw [hw5 _ (by omega), hfb.word (by fx_av), hfk.word (by fx_av), hM2,
      word_writeBytes_disjoint _ _ (by rw [EvmProof.Memory.readPadded_size]; omega), hM1]
    exact word_mstore _ _ _ (by norm_num)
  · intro S hS hks
    have hS' : Sized4 fun k => EvmSemantics.Crypto.Keccak.permute (S k) :=
      fun k hk => permute_size' (hS k hk)
    obtain ⟨hc, hfl⟩ := hb _ hS' (hk S hS (ks4_frame hks hf2 (by fx_av)))
    refine ⟨fun i hi => ?_, fun g hg => ?_⟩
    · rw [hw5 _ (by omega), ← hc i hi]
    · rw [hw5 _ (by omega), ← hfl g hg]

/-! ## Flag words and candidate words -/

theorem testBit_foldl_or (j : Nat) : ∀ (l : List Nat) (a : Nat),
    (l.foldl (· ||| ·) a).testBit j = (a.testBit j || l.any (fun x => x.testBit j))
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, testBit_foldl_or j l, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem testBit_orList (l : List Nat) (j : Nat) :
    (orList l).testBit j = l.any (fun x => x.testBit j) := by
  unfold orList; rw [testBit_foldl_or]; simp

theorem cand_lt (S : Fips202.SpongeState) (i : Nat) : cand S i < 2 ^ 23 := by
  unfold cand
  have h0 : sbyte S (3 * i) < 256 := Nat.mod_lt _ (by decide)
  have h1 : sbyte S (3 * i + 1) < 256 := Nat.mod_lt _ (by decide)
  have h2 : sbyte S (3 * i + 2) % 128 < 128 := Nat.mod_lt _ (by decide)
  omega

theorem lane_pack4' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> norm_num at h0 h1 h2 h3 ⊢ <;> omega

theorem lane_pack4_cand (S : Nat → Fips202.SpongeState) (i : Nat) {k : Nat} (hk : k < 4) :
    lane (pack4 fun k => cand (S k) i) k = cand (S k) i :=
  lane_pack4' (fun k _ => Nat.lt_trans (cand_lt _ _) (by decide)) hk

theorem flagWord_bit (S : Nat → Fips202.SpongeState) (g : Nat) {k : Nat} (hk : k < 4) :
    flagWord S g / 2 ^ (64 * k + 23) % 2 =
      if (List.range 8).any (fun i => decide (Fips204.q ≤ cand (S k) (8 * g + i))) then 1 else 0 := by
  have key : ∀ i, (pack4 fun k' => cand (S k') (8 * g + i) + 2 ^ 23 - Fips204.q).testBit
      (64 * k + 23) = decide (Fips204.q ≤ cand (S k) (8 * g + i)) := by
    intro i
    have hv : ∀ k', k' < 4 → cand (S k') (8 * g + i) + 2 ^ 23 - Fips204.q < 2 ^ 64 := fun k' _ => by
      have := cand_lt (S k') (8 * g + i); unfold Fips204.q; omega
    have := testBit_lane (pack4 fun k' => cand (S k') (8 * g + i) + 2 ^ 23 - Fips204.q) k 23
    rw [lane_pack4' hv hk] at this
    simp only [show decide (23 < 64) = true by decide, Bool.true_and] at this
    rw [← this, Nat.testBit_eq_decide_div_mod_eq]
    have := cand_lt (S k) (8 * g + i)
    unfold Fips204.q
    by_cases hq : 8380417 ≤ cand (S k) (8 * g + i)
    · rw [decide_eq_true hq, decide_eq_true (by omega)]
    · rw [decide_eq_false hq, decide_eq_false (by omega)]
  rw [← Nat.toNat_testBit, flagWord, testBit_orList, List.any_map]
  simp only [Function.comp_def, key]
  split <;> simp_all

theorem any_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i, i < n → f i = g i) :
    (List.range n).any f = (List.range n).any g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i, hi, hf⟩ => ⟨i, hi, h i hi ▸ hf⟩, fun ⟨i, hi, hg⟩ => ⟨i, hi, (h i hi).symm ▸ hg⟩⟩

end MlDsaOptGlam44.Proofs.Fix
