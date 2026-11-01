import MlDsaOpt65.Fn.Csum.Iter
import MlDsaOpt65.Fn.Csum.Spec
import MlDsaOpt65.Math.G4.CsumCore
import MlDsaOpt44.Fn.Ct.CsumMain
set_option warningAsError true
/-!
# `csum` (WP G4): the stored words and the contract body (ML-DSA-65)

As `MlDsaOpt44/Fn/Ct/CsumMain.lean` with `τ = 49` loads per word, the table at `T`
(rows from calldata offset `off`) and the output at `S`. The 16-bit cell lemmas, the
transpose (`CS.extract`) and the emitted word (`CS.emit_val`) are the 44 lemmas.
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
open MlDsaOpt44.Proofs.CS (cs4o0 cs5g cs5w0 cs5w1 cs5w2 cs5w3 cell cell_lt cell_add cell_word
  ut_lt extract extract0 emit_val pack4_congr N N_lt)

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

theorem sW_toNat (M : ByteArray) (bu : Nat) : (sW M bu).toNat = wsum M bu 49 % 2 ^ 256 := by
  simp only [sW, ld0, ld1, ld2, EvmProof.Word.ofNat_add_mod, EvmProof.Word.word_toNat_ofNat]
  rw [wsum_tau]
  simp only [W, Nat.reduceMul, Nat.reduceAdd]
  apply congrArg (· % 2 ^ 256)
  omega

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

theorem g_iter (h : Pre m c cd ps T S off) : ∀ u, u ≤ 64 → (stU m T S u).2 = UInt256.ofNat (N c (4 * u))
  | 0, _ => by
    show UInt256.ofNat 49 - UInt256.ofNat (word m 4000) = _
    rw [show word m 4000 = negCount c from h.nn, g_zero h.facts]
  | u + 1, hu => by
    show cs5g (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2
      (sT (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2) = _
    unfold cs5g
    rw [g_iter h u (by omega), code_word h (k := 0) (by omega) (by omega) (by omega),
      code_word h (k := 1) (by omega) (by omega) (by omega),
      code_word h (k := 2) (by omega) (by omega) (by omega),
      code_word h (k := 3) (by omega) (by omega) (by omega), Nat.add_zero,
      g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega)]
    congr 2

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

/-- The window sums of iteration `u`. -/
theorem sum_cells (h : Pre m c cd ps T S off) {u k r : Nat} (hu : u < 64) (hk : k < 4) (hr : r < 4)
    (cw sp : Nat) (g : UInt256) :
    cell (sW (stU m T S u).1 (T - 32 * u)).toNat (4 * k + r) = sPrime c cd off r (4 * u + k) := by
  obtain ⟨h1, h2, -⟩ := wsum_cells _ _ (fun i f hi hf => cell_W_le h hu i f hi hf) 49 le_rfl
  rw [sW_toNat, Nat.mod_eq_of_lt h1, h2 _ (by omega), sPrime_ps h.facts, csn]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [cell_W h hu hi (by omega), show (4 * k + r) % 4 = r by omega, show (4 * k + r) / 4 = k by omega]

/-- The word stored for `t = 4 u + k`. -/
theorem store_val (h : Pre m c cd ps T S off) {u k : Nat} (hu : u < 64) (hk : k < 4) :
    word (stU m T S (u + 1)).1 (S + 128 * u + 32 * k) =
      pack4 fun r => 2 ^ 13 * sPrime c cd off r (4 * u + k) + nNeg c (4 * u + k) := by
  show word (csMem (stU m T S u).1 (T - 32 * u) (12288 + 128 * u) (S + 128 * u) (stU m T S u).2) _ = _
  have hg := g_iter h u (by omega)
  have hS := h.hS; have hS2 := h.hS2
  interval_cases k
  · rw [show S + 128 * u + 32 * 0 = S + 128 * u by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w0 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), Nat.add_zero, g_step h.facts (by omega),
      extract0, emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 0) (by omega) hr 0 0 0, nNeg_eq, Nat.add_zero]
  · rw [show S + 128 * u + 32 * 1 = 32 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w1 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      extract _ _ _ _ _ _ (k := 1) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 1) (by omega) hr 0 0 0, nNeg_eq]
  · rw [show S + 128 * u + 32 * 2 = 64 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w2 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      code_word h (k := 2) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega),
      extract _ _ _ _ _ _ (k := 2) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 2) (by omega) hr 0 0 0, nNeg_eq]
  · rw [show S + 128 * u + 32 * 3 = 96 + (S + 128 * u) by omega]
    simp (disch := first | omega | exact ut_lt _) only [csMem, word_mstore_disjoint, word_mstore]
    unfold cs5w3 sT
    rw [hg, code_word h (k := 0) hu (by omega) (by omega), code_word h (k := 1) hu (by omega) (by omega),
      code_word h (k := 2) hu (by omega) (by omega), code_word h (k := 3) hu (by omega) (by omega),
      Nat.add_zero, g_step h.facts (t' := 4 * u) (by omega), g_step h.facts (t' := 4 * u + 1) (by omega),
      g_step h.facts (t' := 4 * u + 2) (by omega), g_step h.facts (t' := 4 * u + 3) (by omega),
      extract _ _ _ _ _ _ (k := 3) (by omega) rfl (by omega), emit_val (N_lt _ _) _ (fun r _ => cell_lt _ _)]
    apply pack4_congr; intro r hr
    rw [sum_cells h hu (k := 3) (by omega) hr 0 0 0, nNeg_eq]

end

theorem stU_later (m : ByteArray) (T S : Nat) {a u : Nat} (ha : a + 32 ≤ S + 128 * (u + 1)) :
    ∀ u', u + 1 ≤ u' → u' ≤ 64 → word (stU m T S u').1 a = word (stU m T S (u + 1)).1 a
  | 0, h1, _ => by omega
  | u' + 1, h1, h2 => by
    by_cases he : u + 1 = u' + 1
    · rw [he]
    · show word (csMem _ _ _ _ _) a = _
      rw [csMem_other _ _ _ _ _ (by omega), stU_later m T S ha u' (by omega) (by omega)]

/-- The contract body of `csum_call`. -/
theorem csum_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray) {g : Nat} (hg : g < 2)
    (hb : ∀ i, i < P.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ (off : Nat) (c : Fips204.Poly), c.size = 256 →
        (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m (TT + 0x1800 * g) off s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 0x2000 * g + 32 * t) =
          pack4 fun r => 2 ^ 13 * sPrime c s.executionEnv.calldata off r t + nNeg c t) ∧
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
