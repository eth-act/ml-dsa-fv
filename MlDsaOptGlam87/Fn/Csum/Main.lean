import MlDsaOptGlam87.Fn.Csum.Iter
import MlDsaOpt87.Fn.Csum.Spec
import MlDsaOpt65.Math.G4.CsumCore
import MlDsaOpt44.Fn.Ct.Csum4Main
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/Csum/Main.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `csum` (v4): the stored words and the contract body (ML-DSA-87)

As `MlDsaOpt44/Fn/Ct/Csum4Main.lean` with `τ = 60` loads per word, the table at `T`
(rows from calldata offset `off`) and the output at `S`. The count word before position
`t` is `pack4 (spOff − N c t)` (`g_zero`, `g_step`: each `CW` code `±REP` is subtracted),
and every emitted word is the count word minus `pack4 (2^13 S'_r(t))` (the 44 transpose
and mask-13 lemmas `CS4.tp_bits`, `CS4.extract`), lane-wise without borrow (`emit_sub`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOptGlam87.Proofs.G4

open MlDsaOpt87.Proofs MlDsaOpt87.Proofs.G4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs
open MlDsaOptGlam87.Proofs.Infra
open MlDsaOpt44.Proofs.CS (cell cell_lt cell_add cell_word)
open MlDsaOpt44.Proofs.CS4 (c4T c4g1 c4g2 c4g3 c4g4 c4w0 c4w1 c4w2 c4w3 tp tp_bits ut_lt extract
  extract0 pack4_congr REP_val N N_le)

/-! ## Window entries are 10-bit -/

theorem tEntry_le (cd : ByteArray) (off r e : Nat) : tEntry cd off r e ≤ 1023 := by
  unfold tEntry
  split_ifs
  · have := MlDsaOptG4.bitsToInteger_lt (cd.extract (off + 320 * r) (off + 320 * (r + 1))) (10 * (e - 256)) 10
    unfold t1f; omega
  · omega

/-! ## The window sum -/

/-- Word `m` of the window sum at `bu`. -/
def W (M : ByteArray) (bu m : Nat) : Nat := word M (bu + word M (49152 + 32 * m))

def wsum (M : ByteArray) (bu : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wsum M bu n + W M bu n

def csn (M : ByteArray) (bu f n : Nat) : Nat := ((List.range n).map fun m => cell (W M bu m) f).sum

theorem csn_succ (M : ByteArray) (bu f n : Nat) :
    csn M bu f (n + 1) = csn M bu f n + cell (W M bu n) f := by
  simp [csn, List.range_succ]

theorem wsum_tau (M : ByteArray) (bu : Nat) : wsum M bu 60 = 0 + W M bu 0 + W M bu 1 + W M bu 2 + W M bu 3 + W M bu 4 + W M bu 5 + W M bu 6 + W M bu 7 + W M bu 8 + W M bu 9 + W M bu 10 + W M bu 11 + W M bu 12 + W M bu 13 + W M bu 14 + W M bu 15 + W M bu 16 + W M bu 17 + W M bu 18 + W M bu 19 + W M bu 20 + W M bu 21 + W M bu 22 + W M bu 23 + W M bu 24 + W M bu 25 + W M bu 26 + W M bu 27 + W M bu 28 + W M bu 29 + W M bu 30 + W M bu 31 + W M bu 32 + W M bu 33 + W M bu 34 + W M bu 35 + W M bu 36 + W M bu 37 + W M bu 38 + W M bu 39 + W M bu 40 + W M bu 41 + W M bu 42 + W M bu 43 + W M bu 44 + W M bu 45 + W M bu 46 + W M bu 47 + W M bu 48 + W M bu 49 + W M bu 50 + W M bu 51 + W M bu 52 + W M bu 53 + W M bu 54 + W M bu 55 + W M bu 56 + W M bu 57 + W M bu 58 + W M bu 59 := rfl

theorem sW_toNat (m0 M : ByteArray) (bu : Nat)  -- glam: all τ bases from the stack
    (hm0 : ∀ i, i < 60 → word m0 (49152 + 32 * i) = word M (49152 + 32 * i)) :
    (sW m0 M bu).toNat = wsum M bu 60 % 2 ^ 256 := by
  have e0 : word m0 49152 = word M 49152 := by simpa using hm0 0 (by norm_num)
  have e1 : word m0 49184 = word M 49184 := by simpa using hm0 1 (by norm_num)
  have e2 : word m0 49216 = word M 49216 := by simpa using hm0 2 (by norm_num)
  have e3 : word m0 49248 = word M 49248 := by simpa using hm0 3 (by norm_num)
  have e4 : word m0 49280 = word M 49280 := by simpa using hm0 4 (by norm_num)
  have e5 : word m0 49312 = word M 49312 := by simpa using hm0 5 (by norm_num)
  have e6 : word m0 49344 = word M 49344 := by simpa using hm0 6 (by norm_num)
  have e7 : word m0 49376 = word M 49376 := by simpa using hm0 7 (by norm_num)
  have e8 : word m0 49408 = word M 49408 := by simpa using hm0 8 (by norm_num)
  have e9 : word m0 49440 = word M 49440 := by simpa using hm0 9 (by norm_num)
  have e10 : word m0 49472 = word M 49472 := by simpa using hm0 10 (by norm_num)
  have e11 : word m0 49504 = word M 49504 := by simpa using hm0 11 (by norm_num)
  have e12 : word m0 49536 = word M 49536 := by simpa using hm0 12 (by norm_num)
  have e13 : word m0 49568 = word M 49568 := by simpa using hm0 13 (by norm_num)
  have e14 : word m0 49600 = word M 49600 := by simpa using hm0 14 (by norm_num)
  have e15 : word m0 49632 = word M 49632 := by simpa using hm0 15 (by norm_num)
  have e16 : word m0 49664 = word M 49664 := by simpa using hm0 16 (by norm_num)
  have e17 : word m0 49696 = word M 49696 := by simpa using hm0 17 (by norm_num)
  have e18 : word m0 49728 = word M 49728 := by simpa using hm0 18 (by norm_num)
  have e19 : word m0 49760 = word M 49760 := by simpa using hm0 19 (by norm_num)
  have e20 : word m0 49792 = word M 49792 := by simpa using hm0 20 (by norm_num)
  have e21 : word m0 49824 = word M 49824 := by simpa using hm0 21 (by norm_num)
  have e22 : word m0 49856 = word M 49856 := by simpa using hm0 22 (by norm_num)
  have e23 : word m0 49888 = word M 49888 := by simpa using hm0 23 (by norm_num)
  have e24 : word m0 49920 = word M 49920 := by simpa using hm0 24 (by norm_num)
  have e25 : word m0 49952 = word M 49952 := by simpa using hm0 25 (by norm_num)
  have e26 : word m0 49984 = word M 49984 := by simpa using hm0 26 (by norm_num)
  have e27 : word m0 50016 = word M 50016 := by simpa using hm0 27 (by norm_num)
  have e28 : word m0 50048 = word M 50048 := by simpa using hm0 28 (by norm_num)
  have e29 : word m0 50080 = word M 50080 := by simpa using hm0 29 (by norm_num)
  have e30 : word m0 50112 = word M 50112 := by simpa using hm0 30 (by norm_num)
  have e31 : word m0 50144 = word M 50144 := by simpa using hm0 31 (by norm_num)
  have e32 : word m0 50176 = word M 50176 := by simpa using hm0 32 (by norm_num)
  have e33 : word m0 50208 = word M 50208 := by simpa using hm0 33 (by norm_num)
  have e34 : word m0 50240 = word M 50240 := by simpa using hm0 34 (by norm_num)
  have e35 : word m0 50272 = word M 50272 := by simpa using hm0 35 (by norm_num)
  have e36 : word m0 50304 = word M 50304 := by simpa using hm0 36 (by norm_num)
  have e37 : word m0 50336 = word M 50336 := by simpa using hm0 37 (by norm_num)
  have e38 : word m0 50368 = word M 50368 := by simpa using hm0 38 (by norm_num)
  have e39 : word m0 50400 = word M 50400 := by simpa using hm0 39 (by norm_num)
  have e40 : word m0 50432 = word M 50432 := by simpa using hm0 40 (by norm_num)
  have e41 : word m0 50464 = word M 50464 := by simpa using hm0 41 (by norm_num)
  have e42 : word m0 50496 = word M 50496 := by simpa using hm0 42 (by norm_num)
  have e43 : word m0 50528 = word M 50528 := by simpa using hm0 43 (by norm_num)
  have e44 : word m0 50560 = word M 50560 := by simpa using hm0 44 (by norm_num)
  have e45 : word m0 50592 = word M 50592 := by simpa using hm0 45 (by norm_num)
  have e46 : word m0 50624 = word M 50624 := by simpa using hm0 46 (by norm_num)
  have e47 : word m0 50656 = word M 50656 := by simpa using hm0 47 (by norm_num)
  have e48 : word m0 50688 = word M 50688 := by simpa using hm0 48 (by norm_num)
  have e49 : word m0 50720 = word M 50720 := by simpa using hm0 49 (by norm_num)
  have e50 : word m0 50752 = word M 50752 := by simpa using hm0 50 (by norm_num)
  have e51 : word m0 50784 = word M 50784 := by simpa using hm0 51 (by norm_num)
  have e52 : word m0 50816 = word M 50816 := by simpa using hm0 52 (by norm_num)
  have e53 : word m0 50848 = word M 50848 := by simpa using hm0 53 (by norm_num)
  have e54 : word m0 50880 = word M 50880 := by simpa using hm0 54 (by norm_num)
  have e55 : word m0 50912 = word M 50912 := by simpa using hm0 55 (by norm_num)
  have e56 : word m0 50944 = word M 50944 := by simpa using hm0 56 (by norm_num)
  have e57 : word m0 50976 = word M 50976 := by simpa using hm0 57 (by norm_num)
  have e58 : word m0 51008 = word M 51008 := by simpa using hm0 58 (by norm_num)
  have e59 : word m0 51040 = word M 51040 := by simpa using hm0 59 (by norm_num)
  simp only [sW, ld0, ld1, ld2, ld3, bwOf, Nat.reduceMul, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59]
  simp only [EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]
  rw [wsum_tau]
  simp only [W, Nat.reduceMul, Nat.reduceAdd]
  apply congrArg (· % 2 ^ 256)
  ring

theorem wsum_cells (M : ByteArray) (bu : Nat)
    (hc : ∀ m f, m < 60 → f < 16 → cell (W M bu m) f ≤ 1023) :
    ∀ n, n ≤ 60 → wsum M bu n < 2 ^ 256 ∧ (∀ f, f < 16 → cell (wsum M bu n) f = csn M bu f n) ∧
      ∀ f, f < 16 → csn M bu f n ≤ 1023 * n
  | 0, _ => ⟨by simp [wsum], fun f _ => by simp [wsum, csn, cell], fun f _ => by simp [csn]⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := wsum_cells M bu hc n (by omega)
    have hadd := cell_add (x := wsum M bu n) (y := W M bu n) h1 (word_lt M _) (fun f hf => by
      rw [h2 f hf]; have := h3 f hf; have := hc n f (by omega) hf; omega)
    refine ⟨hadd.1, fun f hf => ?_, fun f hf => ?_⟩
    · show cell (wsum M bu n + W M bu n) f = _
      rw [csn_succ, hadd.2 f hf, h2 f hf]
    · rw [csn_succ]; have := h3 f hf; have := hc n f (by omega) hf; omega

/-! ## The running count -/

theorem spOff_eq : spOff = 1072955263 := by
  unfold spOff; norm_num [Fips204.q]

theorem gval_lt' (n : Nat) : pack4 (fun _ => 1072955263 - n) < 2 ^ 256 := by
  simp only [pack4]; omega

theorem g_zero {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {M : ByteArray}
    (hnn : word M 4000 = negCount c) :
    cse M = UInt256.ofNat (pack4 fun _ => spOff - N c 0) := by
  have hz := N_zero h
  unfold cse
  rw [hnn, ofNat_sub (by omega) (by norm_num), ofNat_mul, ofNat_sub]
  · congr 1; rw [spOff_eq]; simp only [pack4]; omega
  · omega
  · norm_num

theorem g_step {c : Fips204.Poly} {ps : List Nat} (h : CFacts c ps) {t' : Nat} (ht : t' < 256) :
    UInt256.ofNat (pack4 fun _ => spOff - N c t') - UInt256.ofNat (codeOf c[t']!) =
      UInt256.ofNat (pack4 fun _ => spOff - N c (t' + 1)) := by
  have hs := N_step h ht
  have h1 := N_le c t'
  have h2 := N_le c (t' + 1)
  rw [spOff_eq] at *
  rcases h.coeff t' ht with hc | hc | hc
  · simp only [hc, codeOf, if_true] at hs ⊢
    simp at hs
    rw [ofNat_sub (by omega) (gval_lt' _), hs]; simp
  · have hne : (1 : Int) ≠ 0 := by decide
    have hne' : (1 : Int) ≠ -1 := by decide
    simp only [hc, codeOf, hne, hne', if_false, if_true] at hs ⊢
    simp at hs
    apply EvmProof.Word.word_ext
    rw [EvmProof.Word.word_toNat_sub, toNat_ofNat_of_lt (gval_lt' _),
      toNat_ofNat_of_lt (by rw [REP_val]; norm_num), toNat_ofNat_of_lt (gval_lt' _), REP_val]
    simp only [pack4]; omega
  · have hne : (-1 : Int) ≠ 0 := by decide
    have hne' : (-1 : Int) ≠ 1 := by decide
    simp only [hc, codeOf, hne, hne', if_false, if_true] at hs ⊢
    simp at hs
    rw [REP_val]
    have hle : 6277101735386680764176071790128604879584176795969512275969 ≤
        pack4 (fun _ => 1072955263 - N c t') := by simp only [pack4]; omega
    have heq : pack4 (fun _ => 1072955263 - N c t') - 6277101735386680764176071790128604879584176795969512275969 =
        pack4 (fun _ => 1072955263 - N c (t' + 1)) := by simp only [pack4]; omega
    rw [ofNat_sub hle (gval_lt' _), heq]

/-- An emitted word: the count word minus the shifted window sums, lane-wise without borrow. -/
theorem emit_sub {n : Nat} {S : Nat → Nat} (hS : ∀ r, r < 4 → S r ≤ 1023 * 60) (hn : n ≤ 256) :
    (UInt256.ofNat (pack4 fun _ => spOff - n) - UInt256.ofNat (pack4 fun r => S r * 2 ^ 13)).toNat =
      pack4 fun r => spOff - (2 ^ 13 * S r + n) := by
  have h0 := hS 0 (by omega); have h1 := hS 1 (by omega)
  have h2 := hS 2 (by omega); have h3 := hS 3 (by omega)
  rw [spOff_eq, ofNat_sub (by simp only [pack4]; omega) (gval_lt' _),
    toNat_ofNat_of_lt (by simp only [pack4]; omega)]
  simp only [pack4]; omega

/-! ## One iteration, in terms of the input memory `m` -/

section
variable {m : ByteArray} {c : Fips204.Poly} {cd : ByteArray} {ps : List Nat} {T S off : Nat}

/-- What `csum` needs to know about its input memory and pointers. -/
structure Pre (m : ByteArray) (c : Fips204.Poly) (cd : ByteArray) (ps : List Nat) (T S off : Nat) :
    Prop where
  facts : CFacts c ps
  cw : ∀ t, t < 256 → word m (CW + 32 * t) = codeOf c[t]!
  nn : word m NNEG = negCount c
  base : ∀ i, i < 60 → word m (BASES + 32 * i) = baseOf c ps[i]!
  tt : TTable m T off cd
  hT : 2048 ≤ T
  hTS : T + 6144 ≤ S
  hS : 32768 ≤ S
  hS2 : S + 8192 ≤ 49152

theorem code_word (h : Pre m c cd ps T S off) {u k a : Nat} (hu : u < 64) (hk : k < 4)
    (ha : a = 12288 + 128 * u + 32 * k) : word (stU m T S u).1 a = codeOf c[4 * u + k]! := by
  have := h.hS
  rw [stU_other m T S (by omega) u (by omega), ← h.cw (4 * u + k) (by omega)]
  congr 1; unfold CW; omega

/-- The count word after `u` iterations. -/
theorem g_iter (h : Pre m c cd ps T S off) : ∀ u, u ≤ 64 →
    (stU m T S u).2 = UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u))
  | 0, _ => g_zero h.facts h.nn
  | u + 1, hu => by
    show c4g4 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2 = _
    unfold c4g4 c4g3 c4g2 c4g1
    rw [g_iter h u (by omega), code_word h (k := 0) (by omega) (by omega) (by omega),
      code_word h (k := 1) (by omega) (by omega) (by omega),
      code_word h (k := 2) (by omega) (by omega) (by omega),
      code_word h (k := 3) (by omega) (by omega) (by omega), Nat.add_zero,
      g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega)]
    congr 3

theorem be16_frame (u : Nat) (hu : u ≤ 64) {a : Nat} (ha : a + 2 ≤ S) :
    be16 (stU m T S u).1 a = be16 m a := by
  unfold be16; rw [stU_byte m T S (by omega) u hu, stU_byte m T S (by omega) u hu]

/-- Cell `f` of window word `i` at iteration `u`. -/
theorem cell_W (h : Pre m c cd ps T S off) {u i f : Nat} (hu : u < 64) (hi : i < 60) (hf : f < 16) :
    cell (W (stU m T S u).1 (T - 32 * u) i) f =
      tEntry cd off (f % 4) (4 * u + f / 4 + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0) := by
  have hT := h.hT; have hTS := h.hTS; have hS := h.hS; have hS2 := h.hS2
  have hp : ps[i]! < 256 := by
    have hmem : ps[i]! ∈ ps := by
      rw [getElem!_pos ps i (by rw [h.facts.len]; exact hi)]; exact List.getElem_mem _
    exact ((h.facts.mem _).1 hmem).1
  unfold W
  rw [stU_other m T S (a := 49152 + 32 * i) (by omega) u (by omega),
    show 49152 + 32 * i = BASES + 32 * i by rfl,
    h.base i hi, cell_word _ _ hf, be16_frame u (by omega) (by unfold baseOf; split_ifs <;> omega)]
  have ht := h.tt (4 * u + f / 4 + 256 - ps[i]! + if c[ps[i]!]! = -1 then 256 else 0)
    (by split_ifs <;> omega) (f % 4) (by omega)
  rw [← ht]
  congr 1
  unfold baseOf
  split_ifs <;> omega

theorem cell_W_le (h : Pre m c cd ps T S off) {u : Nat} (hu : u < 64) :
    ∀ i f, i < 60 → f < 16 → cell (W (stU m T S u).1 (T - 32 * u) i) f ≤ 1023 := fun i f hi hf => by
  rw [cell_W h hu hi hf]; exact tEntry_le _ _ _ _

theorem base_stU (h : Pre m c cd ps T S off) {u : Nat} (hu : u ≤ 64) :
    ∀ i, i < 60 → word m (49152 + 32 * i) = word (stU m T S u).1 (49152 + 32 * i) := fun i hi => by  -- glam
  have := h.hS2
  exact (stU_other m T S (by omega) u hu).symm

/-- The window sums of iteration `u`. -/
theorem sum_cells (h : Pre m c cd ps T S off) {u k r : Nat} (hu : u < 64) (hk : k < 4) (hr : r < 4) :
    cell (sW m (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) = sPrime c cd off r (4 * u + k) ∧
      cell (sW m (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) ≤ 1023 * 60 := by
  obtain ⟨h1, h2, h3⟩ := wsum_cells _ _ (fun i f hi hf => cell_W_le h hu i f hi hf) 60 le_rfl
  rw [sW_toNat _ _ _ (base_stU h (by omega)), Nat.mod_eq_of_lt h1, h2 _ (by omega)]
  refine ⟨?_, h3 _ (by omega)⟩
  rw [sPrime_ps h.facts, csn]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [cell_W h hu hi (by omega), show (4 * k + r) % 4 = r by omega, show (4 * k + r) / 4 = k by omega]

theorem emit_lanes (h : Pre m c cd ps T S off) {u k : Nat} (hu : u < 64) (hk : k < 4) {G : UInt256}
    (hg : UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + k + 1)) = G) :
    (G - UInt256.ofNat (pack4 fun r => cell (sW m (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) * 2 ^ 13)).toNat =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd off r (4 * u + k) + nNeg c (4 * u + k)) := by
  rw [← hg, emit_sub (fun r hr => (sum_cells h hu hk hr).2) (N_le _ _), nNeg_eq]
  exact pack4_congr fun r hr => by rw [(sum_cells h hu hk hr).1]

/-- The word stored for `t = 4 u + k`. -/
theorem store_val (h : Pre m c cd ps T S off) {u k : Nat} (hu : u < 64) (hk : k < 4) :
    word (stU m T S (u + 1)).1 (S + 128 * u + 32 * k) =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd off r (4 * u + k) + nNeg c (4 * u + k)) := by
  show word (csMem m (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2) _ = _
  have hS := h.hS; have hS2 := h.hS2
  have hg := g_iter h u (by omega)
  have hT := fun i (hi : i < 256) => tp_bits (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u)
    (stU m T S u).2 (sW m (stU m T S u).1 (T - 32 * u)) hi
  have c0 := code_word h (k := 0) (a := 12288 + 128 * u) hu (by omega) (by omega)
  have c1 := code_word h (k := 1) (a := 32 + (12288 + 128 * u)) hu (by omega) (by omega)
  have c2 := code_word h (k := 2) (a := 64 + (12288 + 128 * u)) hu (by omega) (by omega)
  have c3 := code_word h (k := 3) (a := 96 + (12288 + 128 * u)) hu (by omega) (by omega)
  have g1 : c4g1 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 0 + 1)) := by
    unfold c4g1; rw [hg, c0, Nat.add_zero, g_step h.facts (by omega)]
  have g2 : c4g2 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 1 + 1)) := by
    unfold c4g2; rw [g1, c1, Nat.add_zero, g_step h.facts (by omega)]
  have g3 : c4g3 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 2 + 1)) := by
    unfold c4g3; rw [g2, c2, g_step h.facts (by omega)]
  have g4 : c4g4 (stU m T S u).1 (12288 + 128 * u) (stU m T S u).2 =
      UInt256.ofNat (pack4 fun _ => spOff - N c (4 * u + 3 + 1)) := by
    unfold c4g4; rw [g3, c3, g_step h.facts (by omega)]
  interval_cases k
  · rw [show S + 128 * u + 32 * 0 = S + 128 * u by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, c4mem, word_mstore_disjoint, word_mstore]
    unfold c4w0 sT
    rw [extract0 _ _ hT]
    exact emit_lanes h hu (k := 0) (by omega) g1.symm
  · rw [show S + 128 * u + 32 * 1 = 32 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, c4mem, word_mstore_disjoint, word_mstore]
    unfold c4w1 sT
    rw [extract _ _ hT (k := 1) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 1) (by omega) g2.symm
  · rw [show S + 128 * u + 32 * 2 = 64 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, c4mem, word_mstore_disjoint, word_mstore]
    unfold c4w2 sT
    rw [extract _ _ hT (k := 2) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 2) (by omega) g3.symm
  · rw [show S + 128 * u + 32 * 3 = 96 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, c4mem, word_mstore_disjoint, word_mstore]
    unfold c4w3 sT
    rw [extract _ _ hT (k := 3) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 3) (by omega) g4.symm

end

theorem stU_later (m : ByteArray) (T S : Nat) {a u : Nat} (ha : a + 32 ≤ S + 128 * (u + 1)) :
    ∀ u', u + 1 ≤ u' → u' ≤ 64 → word (stU m T S u').1 a = word (stU m T S (u + 1)).1 a
  | 0, h1, _ => by omega
  | u' + 1, h1, h2 => by
    by_cases he : u + 1 = u' + 1
    · rw [he]
    · show word (csMem _ _ _ _ _ _) a = _
      rw [csMem_other _ _ _ _ _ _ (by omega), stU_later m T S ha u' (by omega) (by omega)]

/-- The contract body of `csum_call`. -/
theorem csum_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray) {g : Nat} (hg : g < 2)
    (hb : ∀ i, i < P.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ (off : Nat) (c : Fips204.Poly), c.size = 256 →
        (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m (TT + 0x1800 * g) off s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 0x2000 * g + 32 * t) =
          pack4 fun r => spOff - (2 ^ 13 * sPrime c s.executionEnv.calldata off r t + nNeg c t)) ∧
      FrameExcept m m' [(SP + 0x2000 * g, SP + 0x2000 * g + 8192)] ∧
      Call s Entry.csum [wd (SP + 0x2000 * g), wd (TT + 0x1800 * g)] ret tail m [] m' Gas.csum := by
  have htail : tail.length ≤ 950 := by have := hr.depth; simp only [Stack.csum, Stack.leaf] at this; omega
  have htau : P.tau = 60 := rfl
  have eT : TT + 0x1800 * g = 20480 + 6144 * g := rfl
  have eS : SP + 0x2000 * g = 32768 + 8192 * g := rfl
  rw [eT, eS]
  refine ⟨(stU m (20480 + 6144 * g) (32768 + 8192 * g) 64).1, ?_, fun a ha => ?_, ?_⟩
  · intro off c hsz hco hrep htt t ht
    obtain ⟨hcw, hnn, ps, hlen, hnd, hmem, hbase⟩ := hrep
    rw [htau] at hlen hbase
    have h : Pre m c s.executionEnv.calldata ps (20480 + 6144 * g) (32768 + 8192 * g) off :=
      ⟨⟨hco, hlen, hnd, hmem⟩, hcw, hnn, fun i hi => hbase i hi, htt, by omega, by omega, by omega,
        by omega⟩
    rw [show 32768 + 8192 * g + 32 * t = 32768 + 8192 * g + 128 * (t / 4) + 32 * (t % 4) by omega,
      stU_later m _ _ (u := t / 4) (by omega) 64 (by omega) le_rfl, store_val h (by omega) (by omega),
      show 4 * (t / 4) + t % 4 = t by omega]
  · have h : a < 32768 + 8192 * g ∨ 32768 + 8192 * g + 8192 ≤ a := by
      have := ha (32768 + 8192 * g, 32768 + 8192 * g + 8192) (by simp)
      simpa using this
    exact stU_byte m _ _ h 64 le_rfl
  · rw [call_iff, Entry.csum, Gas.csum]
    have h := cs_run hs htail hr.jumpdest hr.small m (T := 20480 + 6144 * g) (S := 32768 + 8192 * g)
      (by omega) (by omega) (by omega) (by omega) (fun i hi => hb i (by rw [htau]; exact hi))
    exact (h.mono (by norm_num)).of_eq (by simp) rfl

end MlDsaOptGlam87.Proofs.G4
