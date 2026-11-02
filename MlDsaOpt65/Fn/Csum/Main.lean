import MlDsaOpt65.Fn.Csum.Iter
import MlDsaOpt65.Fn.Csum.Spec
import MlDsaOpt65.Math.G4.CsumCore
import MlDsaOpt44.Fn.Ct.Csum4Main
set_option warningAsError true
/-!
# `csum` (v4): the stored words and the contract body (ML-DSA-65)

As `MlDsaOpt44/Fn/Ct/Csum4Main.lean` with `τ = 49` loads per word, the table at `T`
(rows from calldata offset `off`) and the output at `S`. The count word before position
`t` is `pack4 (spOff − N c t)` (`g_zero`, `g_step`: each `CW` code `±REP` is subtracted),
and every emitted word is the count word minus `pack4 (2^13 S'_r(t))` (the 44 transpose
and mask-13 lemmas `CS4.tp_bits`, `CS4.extract`), lane-wise without borrow (`emit_sub`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MlDsaOpt65.Proofs.G4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Infra
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

theorem wsum_tau (M : ByteArray) (bu : Nat) : wsum M bu 49 = 0 + W M bu 0 + W M bu 1 + W M bu 2 + W M bu 3 + W M bu 4 + W M bu 5 + W M bu 6 + W M bu 7 + W M bu 8 + W M bu 9 + W M bu 10 + W M bu 11 + W M bu 12 + W M bu 13 + W M bu 14 + W M bu 15 + W M bu 16 + W M bu 17 + W M bu 18 + W M bu 19 + W M bu 20 + W M bu 21 + W M bu 22 + W M bu 23 + W M bu 24 + W M bu 25 + W M bu 26 + W M bu 27 + W M bu 28 + W M bu 29 + W M bu 30 + W M bu 31 + W M bu 32 + W M bu 33 + W M bu 34 + W M bu 35 + W M bu 36 + W M bu 37 + W M bu 38 + W M bu 39 + W M bu 40 + W M bu 41 + W M bu 42 + W M bu 43 + W M bu 44 + W M bu 45 + W M bu 46 + W M bu 47 + W M bu 48 := rfl

theorem sW_toNat (m0 M : ByteArray) (bu : Nat)
    (hm0 : ∀ i, i < 11 → word m0 (49152 + 32 * i) = word M (49152 + 32 * i)) :
    (sW m0 M bu).toNat = wsum M bu 49 % 2 ^ 256 := by
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
  simp only [sW, ld0, ld1, ld2, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
    EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]
  rw [wsum_tau]
  simp only [W, Nat.reduceMul, Nat.reduceAdd]
  apply congrArg (· % 2 ^ 256)
  ring

theorem wsum_cells (M : ByteArray) (bu : Nat)
    (hc : ∀ m f, m < 49 → f < 16 → cell (W M bu m) f ≤ 1023) :
    ∀ n, n ≤ 49 → wsum M bu n < 2 ^ 256 ∧ (∀ f, f < 16 → cell (wsum M bu n) f = csn M bu f n) ∧
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
theorem emit_sub {n : Nat} {S : Nat → Nat} (hS : ∀ r, r < 4 → S r ≤ 1023 * 49) (hn : n ≤ 256) :
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
  base : ∀ i, i < 49 → word m (BASES + 32 * i) = baseOf c ps[i]!
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
theorem cell_W (h : Pre m c cd ps T S off) {u i f : Nat} (hu : u < 64) (hi : i < 49) (hf : f < 16) :
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
    ∀ i f, i < 49 → f < 16 → cell (W (stU m T S u).1 (T - 32 * u) i) f ≤ 1023 := fun i f hi hf => by
  rw [cell_W h hu hi hf]; exact tEntry_le _ _ _ _

theorem base_stU (h : Pre m c cd ps T S off) {u : Nat} (hu : u ≤ 64) :
    ∀ i, i < 11 → word m (49152 + 32 * i) = word (stU m T S u).1 (49152 + 32 * i) := fun i hi => by
  have := h.hS2
  exact (stU_other m T S (by omega) u hu).symm

/-- The window sums of iteration `u`. -/
theorem sum_cells (h : Pre m c cd ps T S off) {u k r : Nat} (hu : u < 64) (hk : k < 4) (hr : r < 4) :
    cell (sW m (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) = sPrime c cd off r (4 * u + k) ∧
      cell (sW m (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) ≤ 1023 * 49 := by
  obtain ⟨h1, h2, h3⟩ := wsum_cells _ _ (fun i f hi hf => cell_W_le h hu i f hi hf) 49 le_rfl
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
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w0 sT
    rw [extract0 _ _ hT]
    exact emit_lanes h hu (k := 0) (by omega) g1.symm
  · rw [show S + 128 * u + 32 * 1 = 32 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w1 sT
    rw [extract _ _ hT (k := 1) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 1) (by omega) g2.symm
  · rw [show S + 128 * u + 32 * 2 = 64 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold c4w2 sT
    rw [extract _ _ hT (k := 2) (by omega) (by omega) (by norm_num)]
    exact emit_lanes h hu (k := 2) (by omega) g3.symm
  · rw [show S + 128 * u + 32 * 3 = 96 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
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
  have htail : tail.length ≤ 960 := by have := hr.depth; simp only [Stack.csum, Stack.leaf] at this; omega
  have htau : P.tau = 49 := rfl
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

end MlDsaOpt65.Proofs.G4
