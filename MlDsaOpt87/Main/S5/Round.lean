import MlDsaOpt87.Main.S5.Sponge
import MlDsaOpt87.Fn.Keccak
import MlDsaOpt87.Fn.Blk
import MlDsaOpt87.Fn.Sponge
import MlDsaOpt87.Fn.Ginit.Call
import MlDsaOpt87.Fn.Group
set_option warningAsError true
/-!
# Building blocks of the mixed groups 10–13 of ML-DSA-87 (WP S5)

* `s5_kb_round`: glue, `kf4`, glue, `blk b`; `s5_absorb_round`: glue, `trabs`
  (one full block of the padded public key into slot 3), then `s5_kb_round`.
* `s5X`, `s5Y`: slot states of a mixed group (rows 4–6 of column `col` in
  slots 0–2, the `tr` sponge after `j0 + b` blocks in slot 3).
* `s5_accMid_step`, `s5_accMid3`, `s5_accCols_frame`: the accumulator tables.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs.Infra

/-- The regions a mixed group may write (`groupFrame 1`, plus `TRL` for group 13). -/
def s5Frame : List (Nat × Nat) := groupFrame 1 ++ [(TRL, TRL + 256)]

/-- `Avoids` side conditions on literal layout ranges (lists built with `++`, `groupFrame`). -/
macro "s5_frame_tac" : tactic => `(tactic| (
  simp only [MlDsaOptCommon.avoids_cons, MlDsaOptCommon.avoids_nil, MlDsaOptCommon.avoids_append,
    List.cons_append, List.nil_append, and_true, MlDsaOpt87.Proofs.groupFrame,
    MlDsaOpt87.Proofs.s5Frame, MlDsaOpt87.Proofs.GroupP.gsFrame, KS, KB, RC4, RC1, MISC, NNEG, CNT, HAVE6, TBL, CW, ABUF, FL, ZH, MlDsaOpt87.Proofs.ZH2,
    MlDsaOpt87.Proofs.BASES, MlDsaOpt87.Proofs.IDX, MlDsaOpt87.Proofs.ACC, MlDsaOpt87.Proofs.HP,
    MlDsaOpt87.Proofs.FIN, MlDsaOpt87.Proofs.RHO1, MlDsaOpt87.Proofs.CB, MlDsaOpt87.Proofs.TRL,
    MlDsaOpt87.Proofs.MU, MlDsaOpt87.Proofs.BK, TT, MlDsaOpt87.Proofs.SP, MlDsaOpt87.Proofs.TOP]
  omega))

/-- Close the side goal of `GroupP.FrameExcept.of_avoid` for literal layout ranges. -/
macro "s5_sub" : tactic => `(tactic| (
  intro a ha
  simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil, IsEmpty.forall_iff,
    forall_const, implies_true, and_true, List.cons_append, List.nil_append,
    MlDsaOpt87.Proofs.groupFrame, MlDsaOpt87.Proofs.s5Frame, MlDsaOpt87.Proofs.GroupP.gsFrame,
    KS, KB, RC4, HAVE6, ABUF, FL, ZH, MlDsaOpt87.Proofs.ACC, MlDsaOpt87.Proofs.BK,
    MlDsaOpt87.Proofs.TRL] at ha ⊢
  omega))

/-- One squeeze of a group: glue, `kf4`, glue, `blk b`. -/
theorem s5_kb_round {s : State} (hs : Ctx s) {fb : UInt256} {stk : List UInt256} {m : ByteArray}
    {pc0 r1 r2 c1 c2 b : Nat} (hb : b ≤ 5)
    (g1 : Reach (callState s pc0 stk m) (callState s 21922 [wd r1, fb] m) c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 10772 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : S5Blocks m St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ S5Blocks m' St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ABUF + 1792 * b, ABUF + 1792 * b + 1792),
        (FL + 224 * b, FL + 224 * b + 224)] ∧
      Reach (callState s pc0 stk m) (callState s r2 [fb] m') (c1 + Gas.kf4 + c2 + Gas.blk) := by
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := [fb])
    (retOK_main (by decide) (by simp) hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blk_call hs (ret := r2) (tail := [fb])
    (retOK_main (by decide) (by simp) hj2 hr2) m1 hb
  obtain ⟨hA, hF⟩ := hbk _ (s5_sized4_permute hS) hks1
  have ha2 : Avoids [(ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS, ABUF, FL]; omega
  refine ⟨m2, s5_KS4_frame hks1 hf2 ha2, fun b' hb' => ?_,
    RC4Table.frame (RC4Table.frame hrc hf1 (by avoids_tac)) hf2
      (by simp only [avoids_cons, avoids_nil, and_true, RC4, ABUF, FL]; omega), FrameExcept.trans hf1 hf2,
    ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = b
  · subst hbb
    exact ⟨fun i hi => by rw [hA i hi]; exact s5_pack4_congr fun k hk => by rw [hSt k hk],
      fun g hg => by rw [hF g hg]; exact s5_flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · have h1 := (hB.frame hf1 (by avoids_tac) (by avoids_tac)).frame hf2
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)
    exact h1 b' (by omega)

/-- One absorbing squeeze of the `tr` slot: glue, `trabs` (full block `j < 19`),
glue, `kf4`, glue, `blk b`. -/
theorem s5_absorb_round {s : State} (hs : Ctx s) (hcd : 2592 ≤ s.executionEnv.calldata.size)
    {fb : UInt256} {m : ByteArray} {pc0 r0 r1 r2 c0 c1 c2 b j off : Nat} (hb : b ≤ 5) (hj : j < 19)
    (hoff : off = 136 * j)
    (g0 : Reach (callState s pc0 [fb] m) (callState s 13300
      [wd 0, wd 0xffffffffffffffff000000000000000000000000000000000000000000000000, wd 5, wd 3, wd off,
        wd r0, fb] m) c0)
    (g1 : ∀ m', Reach (callState s r0 [fb] m') (callState s 21922 [wd r1, fb] m') c1)
    (g2 : ∀ m', Reach (callState s r1 [fb] m')
      (callState s 10772 [wd (FL + 224 * b), wd (ABUF + 1792 * b), wd r2, fb] m') c2)
    (hj0 : Decode.isValidJumpDest optBytecode r0 = true) (hr0 : r0 < 2 ^ 16)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : S5Blocks m St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (if k = 3 then
      Fips202.xorBlock 136 (padPk s.executionEnv.calldata) (j * 136) (S 3) else S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (if k = 3 then
        Fips202.xorBlock 136 (padPk s.executionEnv.calldata) (j * 136) (S 3) else S k)) ∧
      S5Blocks m' St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' ([(0, 0 + 128 * 5)] ++ [(KS, KS + 800), (KB, KB + 800),
        (ABUF + 1792 * b, ABUF + 1792 * b + 1792), (FL + 224 * b, FL + 224 * b + 224)]) ∧
      Reach (callState s pc0 [fb] m) (callState s r2 [fb] m')
        (c0 + Gas.trabs 5 + (c1 + Gas.kf4 + c2 + Gas.blk)) := by
  obtain ⟨m1, hw, hf1, hc1⟩ := trabs_call hs (ret := r0) (tail := [fb])
    (retOK_main (by decide) (by simp) hj0 hr0) m (off := off) (sh := 3) (n4 := 5)
    (lm := 0xffffffffffffffff000000000000000000000000000000000000000000000000) (kp := 0)
    (by subst hoff; omega) (by norm_num) (by norm_num) (by norm_num) (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have hks1 := s5_ks4_trabs_full hcd hS hks hj (by subst hoff; exact s5_trabs_norm hw)
  have hS1 : Sized4 fun k => if k = 3 then
      Fips202.xorBlock 136 (padPk s.executionEnv.calldata) (j * 136) (S 3) else S k := fun k hk => by
    dsimp only
    split
    · rw [xorBlock_size]; exact hS 3 (by omega)
    · exact hS k hk
  have ha : Avoids [(0, 0 + 128 * 5)] ABUF (ABUF + 1792 * b) := by
    simp only [avoids_cons, avoids_nil, and_true, ABUF]; omega
  have hb' : Avoids [(0, 0 + 128 * 5)] FL (FL + 224 * b) := by
    simp only [avoids_cons, avoids_nil, and_true, FL]; omega
  obtain ⟨m2, hks2, hB2, hrc2, hf2, hc2⟩ := s5_kb_round hs hb (g1 m1) g2 hj1 hr1 hj2 hr2
    (RC4Table.frame hrc hf1 (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega)) hS1 hks1
    (hB.frame hf1 ha hb') hSt
  exact ⟨m2, hks2, hB2, hrc2, FrameExcept.trans hf1 hf2, (g0.trans hc1).trans hc2⟩

/-! ## Slot states of a mixed group -/

/-- Mixed group of column `col` at the start of squeeze `b`: rows 4–6 of column
`col` in slots 0–2, the `tr` sponge after `j0 + b` blocks in slot 3. -/
def s5X (cd : ByteArray) (col j0 b k : Nat) : Fips202.SpongeState :=
  if k < 3 then permN b (seedState 168 (aSeed cd (4 + k) col)) else absorbPre 136 (padPk cd) (j0 + b)

theorem s5X_sized (cd : ByteArray) (col j0 b : Nat) : Sized4 (s5X cd col j0 b) := fun k _ => by
  unfold s5X; split
  · exact permN_size (seedState_size _ _) b
  · exact absorbPre_size _ _ _

/-- After absorbing block `j0 + b` into slot 3. -/
def s5Y (cd : ByteArray) (col j0 b k : Nat) : Fips202.SpongeState :=
  if k = 3 then Fips202.xorBlock 136 (padPk cd) ((j0 + b) * 136) (s5X cd col j0 b 3)
  else s5X cd col j0 b k

theorem s5Y_sized (cd : ByteArray) (col j0 b : Nat) : Sized4 (s5Y cd col j0 b) := fun k hk => by
  unfold s5Y; split
  · rw [xorBlock_size]; exact s5X_sized cd col j0 b 3 (by omega)
  · exact s5X_sized cd col j0 b k hk

theorem s5_permute_Y (cd : ByteArray) (col j0 b : Nat) {k : Nat} (hk : k < 4) :
    Keccak.permute (s5Y cd col j0 b k) = s5X cd col j0 (b + 1) k := by
  unfold s5Y s5X
  by_cases h3 : k = 3
  · subst h3; simp only [if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
    rw [show j0 + (b + 1) = (j0 + b) + 1 by omega, absorbPre_succ]
  · rw [if_neg h3, if_pos (by omega), if_pos (by omega), permN_succ]

/-- `gfix 7`'s flag on the seeds of rows 4–6 of column `col`. -/
theorem s5_gfix7_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) (col : Nat) :
    ((List.range 4).all fun sl => !(7 : Nat).testBit sl || (aI (if sl < 3 then
      seedState 168 (aSeed cd (4 + sl) col) else Fips202.emptyState)).isSome) = okCol cd 1 col 3 := by
  have e : ∀ r, MlDsaOpt87.Proofs.aI (seedState 168 (aSeed cd r col)) = aOf cd r col :=
    fun r => GroupP.aI_aSeed hcd r col
  simp only [e, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (7 : Nat).testBit 0 = true by decide, show (7 : Nat).testBit 1 = true by decide,
    show (7 : Nat).testBit 2 = true by decide, show (7 : Nat).testBit 3 = false by decide,
    show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide, show (2 : Nat) < 3 by decide,
    if_true, okCol, Bool.not_true, Bool.false_or, Bool.not_false, Bool.true_or,
    Bool.and_true, show List.range 3 = [0, 1, 2] from rfl]

theorem s5_and_low3 (w : Nat) : w &&& (2 ^ 192 - 1) = pack4 fun r => if r < 3 then lane w r else 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  unfold pack4 lane
  simp only [show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide,
    show (2 : Nat) < 3 by decide, if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
  norm_num
  omega

/-- The masked `pass3m` of a mixed group whose slots `0 … 2` hold rows 4–6 of column `col`. -/
theorem s5_pass3m_rows {cd m6 : ByteArray} {col : Nat}
    (hlanes : ∀ sl, sl < 3 → ∀ a, aOf cd (4 + sl) col = some a →
      ∀ t, t < 256 → lane (word m6 (ABUF + 32 * t)) sl = (a[t]!).toNat)
    (hrows : okCol cd 1 col 3 = true) {t : Nat} (ht : t < 256) :
    (word m6 (ABUF + 32 * t) &&& (2 ^ 192 - 1)) =
      pack4 fun r => if r < 3 then ((aD cd (4 + r) col)[t]!).toNat else 0 := by
  rw [s5_and_low3]
  apply s5_pack4_congr
  intro r hr
  split
  · have hs : (aOf cd (4 + r) col).isSome = true := by
      unfold okCol at hrows
      rw [List.all_eq_true] at hrows
      exact hrows r (List.mem_range.mpr (by omega))
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    rw [hlanes r (by omega) a ha t ht]
    unfold aD; rw [ha]; rfl
  · rfl

/-! ## Accumulators -/

theorem s5_aD_lt (cd : ByteArray) (r s : Nat) {t : Nat} (ht : t < 256) :
    ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  unfold aD
  cases h : aOf cd r s with
  | none => simp [MlDsa.Fips204.zeroPoly, ht]
  | some a =>
    simp only [Option.getD_some]
    have := ((MlDsaOpt87.Proofs.rejNTTPoly_range _ a h).2 t ht)
    have hq : (MlDsa.Fips204.q : Int) = 8380417 := rfl
    omega

theorem s5_accSum_congr {cd m m' : ByteArray} {r t : Nat}
    (hzh : ∀ k, k < 7 → zhLane m' k t = zhLane m k t) :
    ∀ n, n ≤ 7 → accSum cd m' r t n = accSum cd m r t n
  | 0, _ => rfl
  | n + 1, hn => by
    show accSum cd m' r t n + _ * zhLane m' n t = accSum cd m r t n + _ * zhLane m n t
    rw [s5_accSum_congr hzh n (by omega), hzh n (by omega)]

theorem s5_accSum_le {cd m : ByteArray} {r t : Nat} (ht : t < 256)
    (hz : ∀ k, k < 7 → zhLane m k t < 2 ^ 28) : ∀ n, n ≤ 7 → accSum cd m r t n ≤ n * 2 ^ 51
  | 0, _ => Nat.le_refl _
  | n + 1, hn => by
    have ih := s5_accSum_le (cd := cd) (r := r) ht hz n (by omega)
    have h3 : ((aD cd r n)[t]!).toNat * zhLane m n t < 2 ^ 23 * 2 ^ 28 :=
      Nat.mul_lt_mul'' (s5_aD_lt cd r n ht) (hz n (by omega))
    have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
    show accSum cd m r t n + _ ≤ _
    omega

theorem s5_accCols_frame {m m' cd : ByteArray} {rb n : Nat} (h : AccCols m cd rb n) (hn : n ≤ 7)
    (hw : ∀ t, t < 256 → word m' (ACC + 0x2000 * rb + 32 * t) = word m (ACC + 0x2000 * rb + 32 * t))
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : AccCols m' cd rb n := by
  intro hok t ht
  rw [hw t ht, h hok t ht]
  exact congrArg pack4 (funext fun j => (s5_accSum_congr (fun k hk => hzh k hk t ht) n hn).symm)

theorem s5_accMid3 {m cd : ByteArray} (h : AccCols m cd 1 3) : AccMid m cd 3 := by
  intro hok t ht
  simp only [Bool.and_eq_true] at hok
  rw [show ACC + 0x2000 + 32 * t = ACC + 0x2000 * 1 + 32 * t by ring, h hok.1 t ht]
  exact congrArg pack4 (funext fun j => by split <;> rfl)

/-- One more column of rows 4–6: lanes 0–2 of `ACC + 0x2000` gain
`A[4 + r][n][t] · ẑ_n[t]`, lane 3 (row 7) is unchanged. -/
theorem s5_accMid_step {m m' cd : ByteArray} {n : Nat} (hn : 3 ≤ n) (hn7 : n < 7)
    (hacc : AccMid m cd n) (hz : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m k t < 2 ^ 28)
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t)
    (hpost : okCol cd 1 n 3 = true → ∀ t, t < 256 → word m' (ACC + 0x2000 + 32 * t) =
      (word m (ACC + 0x2000 + 32 * t) +
        pack4 (fun r => if r < 3 then ((aD cd (4 + r) n)[t]!).toNat else 0) * zhLane m n t) % 2 ^ 256) :
    AccMid m' cd (n + 1) := by
  intro hok t ht
  have hok' := hok
  simp only [okMid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
  have hcol : okCol cd 1 n 3 = true := hok'.2.2.resolve_left (by omega)
  have hok1 : (okUpTo cd 1 4 3 && okMid cd n) = true := by
    simp only [Bool.and_eq_true]; exact ⟨hok'.1, hok'.2.1⟩
  rw [hpost hcol t ht, hacc hok1 t ht, pack4_add_mul]
  have hz' := fun k hk => hz k hk t ht
  rw [Nat.mod_eq_of_lt (pack4_lt fun r hr => by
    by_cases h3 : r < 3
    · rw [if_pos h3, if_pos h3]
      have := s5_accSum_le (cd := cd) (r := 4 + r) ht hz' (n + 1) (by omega)
      have h' : (n + 1) * 2 ^ 51 < 2 ^ 64 := by
        calc (n + 1) * 2 ^ 51 ≤ 7 * 2 ^ 51 := Nat.mul_le_mul_right _ (by omega)
          _ < 2 ^ 64 := by norm_num
      exact Nat.lt_of_le_of_lt this h'
    · rw [if_neg h3, if_neg h3, Nat.zero_mul, Nat.add_zero]
      have := s5_accSum_le (cd := cd) (r := 4 + r) ht hz' 3 (by omega)
      omega)]
  refine congrArg pack4 (funext fun j => ?_)
  by_cases h3 : j < 3
  · rw [if_pos h3, if_pos h3, if_pos h3,
      s5_accSum_congr (fun k hk => hzh k hk t ht) (n + 1) (by omega)]
    rfl
  · rw [if_neg h3, if_neg h3, if_neg h3, Nat.zero_mul, Nat.add_zero,
      s5_accSum_congr (fun k hk => hzh k hk t ht) 3 (by omega)]

/-! ## Invariant transport across a mixed group -/


theorem s5_invE_frame {cd m m' : ByteArray} (h : InvE cd m) (hf : FrameExcept m m' s5Frame) :
    InvE cd m' where
  rc4 := RC4Table.frame h.rc4 hf (by s5_frame_tac)
  rc1 := RC1Table.frame h.rc1 hf (by s5_frame_tac)
  tbl := TblAt.frame h.tbl hf (by s5_frame_tac)
  zhat := ZHatAt.frame h.zhat hf (by s5_frame_tac)
  hp := HPAt.frame h.hp hf (by s5_frame_tac)
  c := CAt.frame h.c hf (by s5_frame_tac) (by s5_frame_tac) (by s5_frame_tac)
  rho := Rho1At.frame h.rho hf (by s5_frame_tac)

theorem s5_frame_widen {m m' : ByteArray} (hf : FrameExcept m m' (groupFrame 1)) :
    FrameExcept m m' s5Frame :=
  GroupP.FrameExcept.of_avoid hf (by s5_sub)

theorem s5_zh_frame {m m' : ByteArray} (hf : FrameExcept m m' s5Frame) :
    ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t :=
  fun k hk t ht => zhLane_frame hf (by s5_frame_tac) (by omega) ht

theorem s5_acc0_frame {cd m m' : ByteArray} (h : AccCols m cd 0 7) (hf : FrameExcept m m' s5Frame) :
    AccCols m' cd 0 7 :=
  s5_accCols_frame h le_rfl (fun t ht => word_frame hf (lo := ACC) (hi := ACC + 8192)
    (by s5_frame_tac) (by omega) (by omega)) (s5_zh_frame hf)

theorem s5_gs_acc1 {m m' : ByteArray} (hf : FrameExcept m m' GroupP.gsFrame) {t : Nat} (ht : t < 256) :
    word m' (ACC + 0x2000 + 32 * t) = word m (ACC + 0x2000 + 32 * t) :=
  word_frame hf (lo := ACC + 0x2000) (hi := ACC + 0x4000) (by s5_frame_tac) (by omega) (by omega)

theorem s5_gs_trl {m m' : ByteArray} (hf : FrameExcept m m' GroupP.gsFrame) {x : Nat} (hx : x < 8) :
    word m' (TRL + 32 * x) = word m (TRL + 32 * x) :=
  word_frame hf (lo := TRL) (hi := TRL + 256) (by s5_frame_tac) (by omega) (by omega)

theorem s5_gs_zh {m m' : ByteArray} (hf : FrameExcept m m' GroupP.gsFrame) {k t : Nat} (hk : k < 8)
    (ht : t < 256) : zhLane m' k t = zhLane m k t :=
  zhLane_frame hf (by s5_frame_tac) hk ht

theorem s5_zhLane_lo (m : ByteArray) {k : Nat} (hk : k < 4) (t : Nat) :
    zhLane m k t = lane (word m (ZH + 32 * t)) k := by
  unfold zhLane zhAddr
  rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.mul_zero, Nat.add_zero]

theorem s5_zhLane_hi (m : ByteArray) {k : Nat} (hk : k < 4) (t : Nat) :
    zhLane m (4 + k) t = lane (word m (ZH2 + 32 * t)) k := by
  unfold zhLane zhAddr ZH2
  rw [show (4 + k) / 4 = 1 by omega, show (4 + k) % 4 = k by omega]
  rfl

/-- `ginit` of a mixed group that keeps slot 3 (`keep = 0x8888…`): slots 0–2
are the seeds of rows 4–6 of column `col`, slot 3 the kept `tr` sponge. -/
theorem s5_ginit_keep {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hrho : Rho1At m s.executionEnv.calldata) {S : Nat → Fips202.SpongeState}
    (hksS : KS4 m S) {col j0 l4 pc0 ret c0 : Nat} (hcol : col < 8)
    (hl4 : l4 = il fun k => if k < 3 then col + 256 * (4 + k) + 0x1F0000 else 0)
    (hS3 : S 3 = absorbPre 136 (padPk s.executionEnv.calldata) j0) (b : Bool)
    (g0 : Reach (callState s pc0 [flag b] m)
      (callState s 12945 [wd l4, wd 0, wd 7,
        wd 0x8888888888888888888888888888888888888888888888888888888888888888, wd ret, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) c0)
    (hj : Decode.isValidJumpDest optBytecode ret = true) (hr : ret < 2 ^ 16) :
    ∃ m1, KS4 m1 (s5X s.executionEnv.calldata col j0 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s pc0 [flag b] m) (callState s ret [flag b] m1) (c0 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  generalize hcdv : s.executionEnv.calldata = cd at hcd hrho hS3
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := ret) (tail := [flag b])
    (retOK_main (by decide) (by simp) hj hr) m0
    (keep := 0x8888888888888888888888888888888888888888888888888888888888888888) (amult := 7)
    (cmult := 0) (l4 := l4) (by norm_num) (by norm_num) (by norm_num) (by rw [hl4]; exact il_lt _)
  have hrho0 := Rho1At.frame hrho hf0 (by avoids_tac)
  have hks0 := s5_KS4_frame hksS hf0 (by avoids_tac)
  have hcd32 : 32 ≤ cd.size := by unfold HDR at hcd; omega
  have hks1 : KS4 m1 (s5X cd col j0 0) :=
    s5_ks4_ginit (kmask := 8) (L := fun k => if k < 3 then col + 256 * (4 + k) + 0x1F0000 else 0)
      (S := S) hrho0 (by norm_num) (by decide +kernel) hl4
      (fun x hx => ks4_and_keep hks0 8 hx)
      (fun k _ => by split <;> omega)
      (fun k hk h => by
        have hk3 : k = 3 := by
          interval_cases k <;> first | rfl | exact absurd h (by decide)
        subst hk3; exact ⟨by decide, by simp⟩)
      (fun k hk h => by
        have hk3 : k = 3 := by
          interval_cases k <;> first | rfl | exact absurd h (by decide)
        subst hk3
        unfold s5X
        rw [if_neg (by decide), hS3, Nat.add_zero])
      (fun k hk hb' x hx => by
        have h3 : k < 3 := by
          by_contra hne
          have : k = 3 := by omega
          subst this; exact absurd hb' (by decide)
        have e : s5X cd col j0 0 k = seedState 168 (aSeed cd (4 + k) col) := by
          unfold s5X; rw [if_pos h3]; rfl
        rw [e]
        exact s5_freshLane_aSeed hcd32 (by omega) (by omega)
          (by interval_cases k <;> decide) (by simp [h3]) hx)
      hg
  refine ⟨m1, hks1, by rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

theorem s5_gst_acc1 {m m' : ByteArray} (hf : FrameExcept m m' (GroupP.gsFrame ++ [(TRL, TRL + 256)]))
    {t : Nat} (ht : t < 256) : word m' (ACC + 0x2000 + 32 * t) = word m (ACC + 0x2000 + 32 * t) :=
  word_frame hf (lo := ACC + 0x2000) (hi := ACC + 0x4000) (by s5_frame_tac) (by omega) (by omega)

theorem s5_gst_zh {m m' : ByteArray} (hf : FrameExcept m m' (GroupP.gsFrame ++ [(TRL, TRL + 256)]))
    {k t : Nat} (hk : k < 8) (ht : t < 256) : zhLane m' k t = zhLane m k t :=
  zhLane_frame hf (by s5_frame_tac) hk ht

/-- The two padding xors of the last `pk` block (lane 1 `^= 0x1F`, lane 16 `^= 0x80 << 56`). -/
theorem s5_pad_words {m : ByteArray} {x : Nat} (hx : x < 25) :
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

end MlDsaOpt87.Proofs
