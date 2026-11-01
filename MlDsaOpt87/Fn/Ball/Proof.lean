import MlDsaOpt87.Fn.Ball.Defs
import MlDsaOpt87.Fn.Ball.Prologue
import MlDsaOpt87.Fn.Ball.Stream
import MlDsaOpt87.Fn.Keccak
import MlDsaOptCommon.BallScan
set_option maxRecDepth 100000
/-! # `sib` (ML-DSA-87): loop invariant, scan and the contract proof

The bookkeeping (`SInv`, `sinv_accept`) is `MlDsaOpt44/Fn/Ball/Proof.lean` with `τ = 60`
(loop start `196`) and the ML-DSA-87 `BASES`/`IDX` addresses; `sibRegions` also lists `KS`,
`KB` and `KZ` (clobbered by `kf1`). The byte of position `p` is read from the `KS` block
(`KSU`, `ksu_stream_byte`), refilled at `p = 136` (`sib_visit`); the scan is the parametric
`MlDsaOptCommon.BallScan`. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

namespace Ball

theorem tau_eq : P.tau = 60 := rfl

open MlDsaOptCommon.BallScan (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv foldl_ballStep_done sampleInBallOf_eq)

/-! ## Words and bytes -/

theorem byteAt_eq_get (b : ByteArray) (p : Nat) : byteAt b p = b[p]!.toNat := by
  unfold byteAt
  split
  · rename_i h; simp [getElem!_pos, h]
  · rename_i h; simp [getElem!_neg, h]; rfl

theorem le64_byte (b : ByteArray) (a r : Nat) (hr : r < 8) :
    le64 b a / 2 ^ (8 * r) % 256 = byteAt b (a + r) := by
  have h0 := byteAt_lt b a; have h1 := byteAt_lt b (a + 1)
  have h2 := byteAt_lt b (a + 2); have h3 := byteAt_lt b (a + 3)
  have h4 := byteAt_lt b (a + 4); have h5 := byteAt_lt b (a + 5)
  have h6 := byteAt_lt b (a + 6); have h7 := byteAt_lt b (a + 7)
  simp only [le64, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  interval_cases r <;> norm_num <;> omega

theorem le64_lt (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 64 := by
  have h0 := byteAt_lt b a; have h1 := byteAt_lt b (a + 1)
  have h2 := byteAt_lt b (a + 2); have h3 := byteAt_lt b (a + 3)
  have h4 := byteAt_lt b (a + 4); have h5 := byteAt_lt b (a + 5)
  have h6 := byteAt_lt b (a + 6); have h7 := byteAt_lt b (a + 7)
  simp only [le64, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  norm_num; omega

theorem div_mod_two_low (y r : Nat) (hr : r < 8) : y / 2 ^ r % 2 = y % 256 / 2 ^ r % 2 := by
  interval_cases r <;> norm_num <;> omega

/-- The sign bit the code reads (`signs & 1` after `n` shifts) is `bit bs n`. -/
theorem sign_bit (bs : ByteArray) (n : Nat) (hn : n < 64) :
    1 &&& le64 bs 0 / 2 ^ n = Fips204.bit bs n := by
  rw [Nat.and_comm, Nat.and_one_is_mod]
  unfold Fips204.bit
  have hn' : n = 8 * (n / 8) + n % 8 := by omega
  rw [hn', Nat.pow_add, ← Nat.div_div_eq_div_mul, div_mod_two_low _ _ (by omega),
    le64_byte _ _ _ (by omega), byteAt_eq_get, ← hn']
  simp

theorem beNat_zero {m : ByteArray} {a : Nat} :
    ∀ w, (∀ k, k < w → byteAt m (a + k) = 0) → beNat m a w = 0
  | 0, _ => rfl
  | w + 1, h => by
    simp only [beNat]; rw [beNat_zero w (fun k hk => h k (by omega)), h w (by omega)]

theorem word_zero {m : ByteArray} {a : Nat} (h : ∀ k, k < 32 → byteAt m (a + k) = 0) :
    word m a = 0 := by
  rw [word_eq_beNat]; exact beNat_zero 32 h

theorem word_mstore_ite (m : ByteArray) {a b v : Nat} (hv : v < 2 ^ 256)
    (h : a = b ∨ a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) a) b =
      if a = b then v else word m b := by
  split
  · rename_i hab; subst hab; exact word_mstore m a v hv
  · exact word_mstore_disjoint m v (by omega)

theorem byteAt_mstore_ne (m : ByteArray) {a b : Nat} (v : Nat) (h : b < a ∨ a + 32 ≤ b) :
    byteAt (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) a) b = byteAt m b :=
  byteAt_writeBytes_of_not_mem (by rw [natToBytesPadded_size]; exact h)

theorem byteAt_mstore8_ite (m : ByteArray) (a b v : Nat) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[UInt8.ofNat v]) a) b =
      if a = b then v % 256 else byteAt m b := by
  have hsize : (ByteArray.mk #[UInt8.ofNat v]).size = 1 := rfl
  rw [byteAt_writeBytes, hsize]
  split
  · rename_i h
    rw [if_pos (by omega), show b - a = 0 by omega, byteAt, dif_pos (by omega)]
    change (UInt8.ofNat v).toNat = v % 256
    rw [UInt8.toNat_ofNat']
  · rw [if_neg (by omega)]

/-! ## The coefficient counts -/

def cntTo (c : Fips204.Poly) : Nat → Nat
  | 0 => 0
  | n + 1 => cntTo c n + if c[n]! = -1 then 1 else 0

theorem filter_cntTo (c : Fips204.Poly) : ∀ n,
    ((List.range n).filter fun p => c[p]! = -1).length = cntTo c n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_cntTo c n, cntTo]
    by_cases h : c[n]! = -1 <;> simp [h]

theorem negCount_eq (c : Fips204.Poly) : negCount c = cntTo c 256 := filter_cntTo c 256

theorem cntTo_le (c : Fips204.Poly) : ∀ n, cntTo c n ≤ n
  | 0 => le_rfl
  | n + 1 => by have := cntTo_le c n; simp only [cntTo]; split <;> omega

theorem cntTo_update (c c' : Fips204.Poly) (x : Nat) (h : ∀ t, t ≠ x → c'[t]! = c[t]!) : ∀ n,
    cntTo c' n + (if x < n ∧ c[x]! = -1 then 1 else 0) =
      cntTo c n + (if x < n ∧ c'[x]! = -1 then 1 else 0)
  | 0 => by simp [cntTo]
  | n + 1 => by
    have ih := cntTo_update c c' x h n
    simp only [cntTo]
    by_cases hxn : x = n
    · subst hxn
      have h1 : ¬ (x < x ∧ c[x]! = -1) := fun h => by omega
      have h2 : ¬ (x < x ∧ c'[x]! = -1) := fun h => by omega
      rw [if_neg h1, if_neg h2] at ih
      by_cases a : c[x]! = -1 <;> by_cases b : c'[x]! = -1 <;> simp [a, b] <;> omega
    · rw [h n (Ne.symm hxn)]
      have e1 : (x < n + 1 ∧ c[x]! = -1) ↔ (x < n ∧ c[x]! = -1) := by
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      have e2 : (x < n + 1 ∧ c'[x]! = -1) ↔ (x < n ∧ c'[x]! = -1) := by
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      simp only [e1, e2]
      omega

theorem getElem!_set! (a : Array Int) (i j : Nat) (z : Int) :
    (a.set! j z)[i]! = if i = j ∧ j < a.size then z else a[i]! :=
  MlDsa44.Proofs.Sampling.getElem!_set! a i j z

theorem size_set! (a : Array Int) (j : Nat) (z : Int) : (a.set! j z).size = a.size :=
  MlDsa44.Proofs.Sampling.size_set! a j z

/-! ## The loop invariant -/

/-- The scratch regions `sib` writes. -/
abbrev sibRegions : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (CW, CW + 8192), (BASES, BASES + 2048),
    (IDX, IDX + 256), (NNEG, NNEG + 64)]

/-- Memory after placing `n = i − 196` coefficients of the array `c`: `f s` is
the position whose window base sits in `BASES[s]`. -/
structure SInv (m M : ByteArray) (c : Fips204.Poly) (i : Nat) : Prop where
  frame : FrameExcept m M sibRegions
  cw : ∀ t, t < 256 → word M (CW + 32 * t) = codeOf c[t]!
  nneg : word M NNEG = negCount c
  cnt : word M CNT = i - 196
  slots : ∃ f : Nat → Nat, (∀ s s', s < i - 196 → s' < i - 196 → f s = f s' → s = s') ∧
    (∀ p, (∃ s, s < i - 196 ∧ f s = p) ↔ p < 256 ∧ c[p]! ≠ 0) ∧
    ∀ s, s < i - 196 → word M (BASES + 32 * s) = baseOf c (f s) ∧ byteAt M (IDX + f s) = s + 1
  idx0 : ∀ t, t < 256 → c[t]! = 0 → byteAt M (IDX + t) = 0
  free : ∀ s, i - 196 ≤ s → s < 60 → word M (BASES + 32 * s) = 0

theorem baseOf_le (c : Fips204.Poly) (p : Nat) (hp : p < 256) : baseOf c p ≤ 6104 := by
  unfold baseOf; split <;> omega

theorem sinv_init (m : ByteArray) (hz : SibFresh m) : SInv m m Fips204.zeroPoly 196 := by
  obtain ⟨hcw, hbi, hnn⟩ := hz
  have hz0 : ∀ t : Nat, Fips204.zeroPoly[t]! = (0 : Int) := fun t => by
    simp only [Fips204.zeroPoly, getElem!_def, Array.getElem?_replicate]
    split <;> rename_i h <;> [skip; rfl]
    split at h <;> simp_all
  refine ⟨FrameExcept.refl _ _, fun t ht => ?_, ?_, ?_, ⟨id, fun _ _ h => absurd h (by omega),
    fun p => ⟨fun ⟨_, h, _⟩ => absurd h (by omega), fun ⟨_, h⟩ => absurd (hz0 p) h⟩,
    fun _ h => absurd h (by omega)⟩, fun t ht _ => ?_, fun s _ hs => ?_⟩
  · rw [hz0, word_zero (fun k hk => hcw _ (by simp only [CW]; omega) (by simp only [CW]; omega))]
    rfl
  · rw [word_zero (fun k hk => hnn _ (by simp only [NNEG]; omega) (by simp only [NNEG]; omega)),
      negCount_eq]
    have : ∀ n, cntTo Fips204.zeroPoly n = 0 := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => simp [cntTo, ih, hz0]
    rw [this]
  · exact word_zero (fun k hk => hnn _ (by simp only [NNEG, CNT]; omega)
      (by simp only [NNEG, CNT]; omega))
  · exact hbi _ (by simp only [BASES, IDX]; omega) (by simp only [IDX]; omega)
  · exact word_zero (fun k hk => hbi _ (by simp only [BASES]; omega)
      (by simp only [BASES, IDX]; omega))

/-- Read-after-write on the `sib` memory terms. -/
macro "sib87_memsimp" : tactic => `(tactic| simp (disch := omega) only [memA, memB, memC, word_mstore_ite,
  word_mstore8_disjoint, byteAt_mstore_ne, byteAt_mstore8_ite, CW, NNEG, CNT, BASES, IDX])

/-- The sign coefficient for the bit `sg`. -/
abbrev sgnOf (sg : Nat) : Int := if sg = 1 then -1 else 1

theorem negCount_step (c : Fips204.Poly) (hsz : c.size = 256) (i j sg : Nat) (hi : i < 256)
    (hj : j < 256) (hci : c[i]! = 0) (hsg : sg ≤ 1) :
    negCount ((c.set! i c[j]!).set! j (sgnOf sg)) = negCount c + sg := by
  rw [negCount_eq, negCount_eq]
  have h1 := cntTo_update c (c.set! i c[j]!) i (fun t ht => by
    rw [getElem!_set!, if_neg (fun h => ht h.1)]) 256
  have h2 := cntTo_update (c.set! i c[j]!) ((c.set! i c[j]!).set! j (sgnOf sg)) j (fun t ht => by
    rw [getElem!_set!, if_neg (fun h => ht h.1)]) 256
  have e1 : (c.set! i c[j]!)[i]! = c[j]! := by
    rw [getElem!_set!, if_pos ⟨rfl, by omega⟩]
  have e2 : (c.set! i c[j]!)[j]! = c[j]! := by
    rw [getElem!_set!]; split
    · rename_i h; rw [h.1]
    · rfl
  have e3 : ((c.set! i c[j]!).set! j (sgnOf sg))[j]! = sgnOf sg := by
    rw [getElem!_set!, if_pos ⟨rfl, by rw [size_set!, hsz]; omega⟩]
  rw [e1, hci] at h1
  rw [e2, e3] at h2
  simp only [show i < 256 from hi, show j < 256 from hj, true_and] at h1 h2
  have : (if sgnOf sg = -1 then 1 else 0) = sg := by
    unfold sgnOf; rcases (by omega : sg = 0 ∨ sg = 1) with rfl | rfl <;> decide
  rw [this] at h2
  simp only [show ¬ ((0 : Int) = -1) by decide, if_false] at h1
  omega

theorem codeOf_sgn (sg : Nat) (hsg : sg ≤ 1) :
    codeOf (sgnOf sg) = if sg = 1 then 1 else 2 ^ 256 - 1 := by
  rcases (by omega : sg = 0 ∨ sg = 1) with rfl | rfl <;> decide

theorem baseOf_congr {c c' : Fips204.Poly} {p : Nat} (h : c'[p]! = c[p]!) :
    baseOf c' p = baseOf c p := by
  unfold baseOf; rw [h]

/-- `IDX`/`BASES` after block `A` and, when `j` holds a coefficient, block `B`. -/
def sibMB (M : ByteArray) (c : Fips204.Poly) (i j nn sg code : Nat) : ByteArray :=
  if byteAt M (IDX + j) = 0 then memA M i j nn sg code
  else memB (memA M i j nn sg code) i j (byteAt M (IDX + j)) (baseOf c j)

/-- Close a read-after-write goal after `sib87_memsimp`. -/
macro "sib87_memclose" : tactic => `(tactic| all_goals ((try split_ifs) <;> first | omega | (congr 1; omega)))

/-- Writes outside `sibRegions` leave nothing else changed. -/
macro "sib87_memframe" : tactic => `(tactic| (
  intro a ha
  have r1 := ha (CW, CW + 8192) (by simp)
  have r2 := ha (BASES, BASES + 2048) (by simp)
  have r3 := ha (IDX, IDX + 256) (by simp)
  have r4 := ha (NNEG, NNEG + 64) (by simp)
  simp only [CW, BASES, IDX, NNEG] at r1 r2 r3 r4
  sib87_memsimp
  sib87_memclose))

set_option maxHeartbeats 2000000 in
/-- One accepted byte: the memory after blocks `A`, (`B`), `C` represents the
updated array. -/
theorem sinv_accept {m M : ByteArray} {c : Fips204.Poly} {i j sg nn code : Nat}
    (h : SInv m M c i) (hsz : c.size = 256) (hi1 : 196 ≤ i) (hi : i < 256) (hji : j ≤ i)
    (hhigh : ∀ t, i ≤ t → c[t]! = 0) (hsg : sg ≤ 1) (hnn : nn = negCount c)
    (hcode : code = if sg = 1 then 1 else 2 ^ 256 - 1) :
    (byteAt M (IDX + j) ≠ 0 → byteAt M (IDX + j) < 61 ∧
        word (memA M i j nn sg code) (49120 + byteAt M (IDX + j) * 32) = baseOf c j) ∧
    word (sibMB M c i j nn sg code) 4032 = i - 196 ∧
    SInv m (memC (sibMB M c i j nn sg code) j sg (i - 196))
      ((c.set! i c[j]!).set! j (sgnOf sg)) (i + 1) := by
  obtain ⟨hfr, hcw, hnneg, hcnt, ⟨f, finj, fmem, fslot⟩, hidx0, hfree⟩ := h
  have hn : i - 196 < 60 := by omega
  have hj256 : j < 256 := by omega
  have hci : c[i]! = 0 := hhigh i le_rfl
  have hc' : ∀ p, ((c.set! i c[j]!).set! j (sgnOf sg))[p]! =
      if p = j then sgnOf sg else if p = i then c[j]! else c[p]! := by
    intro p
    rw [getElem!_set!, getElem!_set!, size_set!, hsz]
    by_cases hpj : p = j
    · simp [hpj, hj256]
    · by_cases hpi : p = i <;> simp [hpj, hpi, hi, hj256]
  have hsv : sgnOf sg ≠ 0 := by unfold sgnOf; split <;> decide
  have hwj := word_lt M (12288 + j * 32)
  have hnn' : nn ≤ 256 := by rw [hnn, negCount_eq]; exact cntTo_le c 256
  have hcode' : code < 2 ^ 256 := by rw [hcode]; split <;> norm_num
  have hbj := baseOf_le c j hj256
  have hcnt' : word M 4032 = i - 196 := hcnt
  have hnneg' : word M 4000 = nn := by rw [hnn]; exact hnneg
  have hflt : ∀ s, s < i - 196 → f s < 256 := fun s hs => ((fmem (f s)).1 ⟨s, hs, rfl⟩).1
  have hfnz : ∀ s, s < i - 196 → c[f s]! ≠ 0 := fun s hs => ((fmem (f s)).1 ⟨s, hs, rfl⟩).2
  have hfi : ∀ s, s < i - 196 → f s ≠ i := fun s hs he => hfnz s hs (he ▸ hci)
  have hnc : negCount ((c.set! i c[j]!).set! j (sgnOf sg)) = nn + sg := by
    rw [hnn]; exact negCount_step c hsz i j sg hi hj256 hci hsg
  -- block `A`
  have hA_cw : ∀ t, t < 256 → word (memA M i j nn sg code) (CW + 32 * t) =
      if t = j then code else if t = i then word M (CW + 32 * j) else word M (CW + 32 * t) := by
    intro t ht; simp only [CW]; sib87_memsimp; sib87_memclose
  have hA_nn : word (memA M i j nn sg code) NNEG = nn + sg := by
    simp only [NNEG]; sib87_memsimp; sib87_memclose
  have hA_cnt : word (memA M i j nn sg code) CNT = i - 196 := by
    simp only [CNT]; sib87_memsimp; sib87_memclose
  have hA_bases : ∀ s, s < 60 →
      word (memA M i j nn sg code) (BASES + 32 * s) = word M (BASES + 32 * s) := by
    intro s hs; simp only [BASES]; sib87_memsimp; sib87_memclose
  have hA_idx : ∀ t, t < 256 → byteAt (memA M i j nn sg code) (IDX + t) = byteAt M (IDX + t) := by
    intro t ht; simp only [IDX]; sib87_memsimp
  have hA_fr : FrameExcept M (memA M i j nn sg code) sibRegions := by sib87_memframe
  -- block `C`
  have hC_cw : ∀ MB : ByteArray, ∀ t, t < 256 →
      word (memC MB j sg (i - 196)) (CW + 32 * t) = word MB (CW + 32 * t) := by
    intro MB t ht; simp only [CW]; sib87_memsimp; sib87_memclose
  have hC_nn : ∀ MB : ByteArray, word (memC MB j sg (i - 196)) NNEG = word MB NNEG := by
    intro MB; simp only [NNEG]; sib87_memsimp; sib87_memclose
  have hC_cnt : ∀ MB : ByteArray, word (memC MB j sg (i - 196)) CNT = 1 + (i - 196) := by
    intro MB; simp only [CNT]; sib87_memsimp; sib87_memclose
  have hC_bases : ∀ MB : ByteArray, ∀ s, s < 60 → word (memC MB j sg (i - 196)) (BASES + 32 * s) =
      if s = i - 196 then 4064 + j * 8 - sg * 2048 else word MB (BASES + 32 * s) := by
    intro MB s hs; simp only [BASES]; sib87_memsimp; sib87_memclose
  have hC_idx : ∀ MB : ByteArray, ∀ t, t < 256 → byteAt (memC MB j sg (i - 196)) (IDX + t) =
      if t = j then i - 195 else byteAt MB (IDX + t) := by
    intro MB t ht; simp only [IDX]; sib87_memsimp; sib87_memclose
  have hC_fr : ∀ MB : ByteArray, FrameExcept MB (memC MB j sg (i - 196)) sibRegions := by
    intro MB; sib87_memframe
  have hcwC : ∀ MB : ByteArray, (∀ t, t < 256 → word MB (CW + 32 * t) =
      word (memA M i j nn sg code) (CW + 32 * t)) → ∀ t, t < 256 →
      word (memC MB j sg (i - 196)) (CW + 32 * t) = codeOf ((c.set! i c[j]!).set! j (sgnOf sg))[t]! := by
    intro MB hMB t ht
    rw [hC_cw MB t ht, hMB t ht, hA_cw t ht, hc' t]
    by_cases htj : t = j
    · rw [if_pos htj, if_pos htj, codeOf_sgn sg hsg, hcode]
    · rw [if_neg htj, if_neg htj]
      by_cases hti : t = i
      · rw [if_pos hti, if_pos hti, hcw j hj256]
      · rw [if_neg hti, if_neg hti, hcw t ht]
  have hnewbase : 4064 + j * 8 - sg * 2048 = baseOf ((c.set! i c[j]!).set! j (sgnOf sg)) j := by
    unfold baseOf; rw [hc' j, if_pos rfl]
    unfold sgnOf; rcases (by omega : sg = 0 ∨ sg = 1) with rfl | rfl <;> simp <;> omega
  by_cases hcj : c[j]! = 0
  · -- `j` was empty: block `B` is skipped
    have hk : byteAt M (IDX + j) = 0 := hidx0 j hj256 hcj
    have hMB : sibMB M c i j nn sg code = memA M i j nn sg code := by
      unfold sibMB; rw [if_pos hk]
    have hfj : ∀ s, s < i - 196 → f s ≠ j := fun s hs he => hfnz s hs (he ▸ hcj)
    rw [hMB]
    refine ⟨fun h0 => absurd hk h0, hA_cnt, ⟨fun a ha => by rw [hC_fr _ a ha, hA_fr a ha, hfr a ha],
      hcwC _ (fun _ _ => rfl), by rw [hC_nn, hA_nn, hnc], by rw [hC_cnt]; omega,
      ⟨fun s => if s = i - 196 then j else f s, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro s s' hs hs' he
      simp only at he
      by_cases hsn : s = i - 196 <;> by_cases hs'n : s' = i - 196
      · omega
      · rw [if_pos hsn, if_neg hs'n] at he; exact absurd he.symm (hfj s' (by omega))
      · rw [if_neg hsn, if_pos hs'n] at he; exact absurd he (hfj s (by omega))
      · rw [if_neg hsn, if_neg hs'n] at he; exact finj s s' (by omega) (by omega) he
    · intro p
      rw [hc' p]
      constructor
      · rintro ⟨s, hs, rfl⟩
        by_cases hsn : s = i - 196
        · simp only [if_pos hsn, if_true]; exact ⟨hj256, hsv⟩
        · have hs' : s < i - 196 := by omega
          simp only [if_neg hsn]
          rw [if_neg (hfj s hs'), if_neg (hfi s hs')]
          exact ⟨hflt s hs', hfnz s hs'⟩
      · rintro ⟨hp, hne⟩
        by_cases hpj : p = j
        · exact ⟨i - 196, by omega, by simp [hpj]⟩
        · rw [if_neg hpj] at hne
          by_cases hpi : p = i
          · rw [if_pos hpi] at hne; exact absurd hcj hne
          · rw [if_neg hpi] at hne
            obtain ⟨s, hs, hfs⟩ := (fmem p).2 ⟨hp, hne⟩
            exact ⟨s, by omega, by simp [show s ≠ i - 196 by omega, hfs]⟩
    · intro s hs
      by_cases hsn : s = i - 196
      · simp only [if_pos hsn]
        rw [hC_bases _ s (by omega), if_pos hsn, hC_idx _ j hj256, if_pos rfl]
        exact ⟨hnewbase, by omega⟩
      · have hs' : s < i - 196 := by omega
        simp only [if_neg hsn]
        rw [hC_bases _ s (by omega), if_neg hsn, hA_bases s (by omega), hC_idx _ _ (hflt s hs'),
          if_neg (hfj s hs'), hA_idx _ (hflt s hs'), (fslot s hs').1]
        refine ⟨(baseOf_congr ?_).symm, (fslot s hs').2⟩
        rw [hc', if_neg (hfj s hs'), if_neg (hfi s hs')]
    · intro t ht hz
      rw [hc' t] at hz
      have htj : t ≠ j := fun e => by rw [if_pos e] at hz; exact hsv hz
      rw [if_neg htj] at hz
      rw [hC_idx _ t ht, if_neg htj, hA_idx t ht]
      apply hidx0 t ht
      by_cases hti : t = i
      · rw [hti]; exact hci
      · rw [if_neg hti] at hz; exact hz
    · intro s hs1 hs2
      rw [hC_bases _ s hs2, if_neg (by omega), hA_bases s hs2]
      exact hfree s (by omega) hs2
  · -- `j` held a coefficient (slot `s0`): block `B` moves it to `i`
    obtain ⟨s0, hs0, hfs0⟩ := (fmem j).2 ⟨hj256, hcj⟩
    have hk : byteAt M (IDX + j) = s0 + 1 := by rw [← hfs0]; exact (fslot s0 hs0).2
    have hij : i ≠ j := fun e => hcj (e ▸ hci)
    have hMB : sibMB M c i j nn sg code =
        memB (memA M i j nn sg code) i j (s0 + 1) (baseOf c j) := by
      unfold sibMB; rw [if_neg (by omega), hk]
    have hfj : ∀ s, s < i - 196 → s ≠ s0 → f s ≠ j :=
      fun s hs hne e => hne (finj s s0 hs hs0 (e.trans hfs0.symm))
    have hB_cw : ∀ MA : ByteArray, ∀ t, t < 256 →
        word (memB MA i j (s0 + 1) (baseOf c j)) (CW + 32 * t) = word MA (CW + 32 * t) := by
      intro MA t ht; simp only [CW]; sib87_memsimp; sib87_memclose
    have hB_nn : ∀ MA : ByteArray, word (memB MA i j (s0 + 1) (baseOf c j)) NNEG = word MA NNEG := by
      intro MA; simp only [NNEG]; sib87_memsimp; sib87_memclose
    have hB_cnt : ∀ MA : ByteArray, word (memB MA i j (s0 + 1) (baseOf c j)) CNT = word MA CNT := by
      intro MA; simp only [CNT]; sib87_memsimp; sib87_memclose
    have hB_bases : ∀ MA : ByteArray, ∀ s, s < 60 →
        word (memB MA i j (s0 + 1) (baseOf c j)) (BASES + 32 * s) =
          if s = s0 then (i - j) * 8 + baseOf c j else word MA (BASES + 32 * s) := by
      intro MA s hs; simp only [BASES]; sib87_memsimp; sib87_memclose
    have hB_idx : ∀ MA : ByteArray, ∀ t, t < 256 →
        byteAt (memB MA i j (s0 + 1) (baseOf c j)) (IDX + t) =
          if t = i then s0 + 1 else byteAt MA (IDX + t) := by
      intro MA t ht; simp only [IDX]; sib87_memsimp; sib87_memclose
    have hB_fr : ∀ MA : ByteArray, FrameExcept MA (memB MA i j (s0 + 1) (baseOf c j)) sibRegions := by
      intro MA; sib87_memframe
    refine ⟨fun _ => ⟨by omega, ?_⟩, ?_, ?_⟩
    · rw [hk, show 49120 + (s0 + 1) * 32 = BASES + 32 * s0 by simp only [BASES]; omega,
        hA_bases s0 (by omega), (fslot s0 hs0).1, hfs0]
    · rw [hMB, show (4032 : Nat) = CNT from rfl, hB_cnt, hA_cnt]
    rw [hMB]
    let f' : Nat → Nat := fun s => if s = i - 196 then j else if s = s0 then i else f s
    have hf'j : ∀ s, s < i - 196 + 1 → (f' s = j ↔ s = i - 196) := by
      intro s hs
      simp only [f']
      by_cases hsn : s = i - 196
      · simp [hsn]
      · rw [if_neg hsn]
        by_cases hss : s = s0
        · rw [if_pos hss]; exact ⟨fun e => absurd e hij, fun e => absurd e hsn⟩
        · rw [if_neg hss]; exact ⟨fun e => absurd e (hfj s (by omega) hss), fun e => absurd e hsn⟩
    have hf'i : ∀ s, s < i - 196 + 1 → (f' s = i ↔ s = s0) := by
      intro s hs
      simp only [f']
      by_cases hsn : s = i - 196
      · rw [if_pos hsn]; exact ⟨fun e => absurd e.symm hij, fun e => by omega⟩
      · rw [if_neg hsn]
        by_cases hss : s = s0
        · simp [hss]
        · rw [if_neg hss]; exact ⟨fun e => absurd e (hfi s (by omega)), fun e => absurd e hss⟩
    refine ⟨fun a ha => by rw [hC_fr _ a ha, hB_fr _ a ha, hA_fr a ha, hfr a ha],
      hcwC _ (hB_cw _), by rw [hC_nn, hB_nn, hA_nn, hnc], by rw [hC_cnt]; omega,
      ⟨f', ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s s' hs hs' he
      have hs1 : s < i - 196 + 1 := by omega
      have hs1' : s' < i - 196 + 1 := by omega
      by_cases hsn : s = i - 196
      · exact hsn.trans ((hf'j s' hs1').1 (he ▸ (hf'j s hs1).2 hsn)).symm
      · by_cases hss : s = s0
        · exact hss.trans ((hf'i s' hs1').1 (he ▸ (hf'i s hs1).2 hss)).symm
        · have hs'n : s' ≠ i - 196 := fun e => hsn ((hf'j s hs1).1 (he.trans ((hf'j s' hs1').2 e)))
          have hs's : s' ≠ s0 := fun e => hss ((hf'i s hs1).1 (he.trans ((hf'i s' hs1').2 e)))
          simp only [f', if_neg hsn, if_neg hss, if_neg hs'n, if_neg hs's] at he
          exact finj s s' (by omega) (by omega) he
    · intro p
      rw [hc' p]
      constructor
      · rintro ⟨s, hs, rfl⟩
        by_cases hsn : s = i - 196
        · simp only [f', if_pos hsn, if_true]; exact ⟨hj256, hsv⟩
        · by_cases hss : s = s0
          · simp only [f', if_neg hsn, if_pos hss, if_neg hij, if_true]; exact ⟨hi, hcj⟩
          · have hs' : s < i - 196 := by omega
            simp only [f', if_neg hsn, if_neg hss]
            rw [if_neg (hfj s hs' hss), if_neg (hfi s hs')]
            exact ⟨hflt s hs', hfnz s hs'⟩
      · rintro ⟨hp, hne⟩
        by_cases hpj : p = j
        · exact ⟨i - 196, by omega, by simp [f', hpj]⟩
        · rw [if_neg hpj] at hne
          by_cases hpi : p = i
          · exact ⟨s0, by omega, by simp [f', hpi, show s0 ≠ i - 196 by omega]⟩
          · rw [if_neg hpi] at hne
            obtain ⟨s, hs, hfs⟩ := (fmem p).2 ⟨hp, hne⟩
            have hss : s ≠ s0 := fun e => hpj (hfs ▸ e ▸ hfs0)
            exact ⟨s, by omega, by simp [f', show s ≠ i - 196 by omega, hss, hfs]⟩
    · intro s hs
      by_cases hsn : s = i - 196
      · simp only [f', if_pos hsn]
        rw [hC_bases _ s (by omega), if_pos hsn, hC_idx _ j hj256, if_pos rfl]
        exact ⟨hnewbase, by omega⟩
      · by_cases hss : s = s0
        · simp only [f', if_neg hsn, if_pos hss]
          rw [hC_bases _ s (by omega), if_neg hsn, hB_bases _ s (by omega), if_pos hss,
            hC_idx _ i hi, if_neg hij, hB_idx _ i hi, if_pos rfl]
          refine ⟨?_, by omega⟩
          unfold baseOf
          rw [hc' i, if_neg hij, if_pos rfl]
          split <;> omega
        · have hs' : s < i - 196 := by omega
          simp only [f', if_neg hsn, if_neg hss]
          rw [hC_bases _ s (by omega), if_neg hsn, hB_bases _ s (by omega), if_neg hss,
            hA_bases s (by omega), hC_idx _ _ (hflt s hs'), if_neg (hfj s hs' hss),
            hB_idx _ _ (hflt s hs'), if_neg (hfi s hs'), hA_idx _ (hflt s hs'), (fslot s hs').1]
          refine ⟨(baseOf_congr ?_).symm, (fslot s hs').2⟩
          rw [hc', if_neg (hfj s hs' hss), if_neg (hfi s hs')]
    · intro t ht hz
      rw [hc' t] at hz
      have htj : t ≠ j := fun e => by rw [if_pos e] at hz; exact hsv hz
      rw [if_neg htj] at hz
      have hti : t ≠ i := fun e => by rw [if_pos e] at hz; exact hcj hz
      rw [if_neg hti] at hz
      rw [hC_idx _ t ht, if_neg htj, hB_idx _ t ht, if_neg hti, hA_idx t ht]
      exact hidx0 t ht hz
    · intro s hs1 hs2
      rw [hC_bases _ s hs2, if_neg (by omega), hB_bases _ s hs2, if_neg (by omega),
        hA_bases s hs2]
      exact hfree s (by omega) hs2

/-! ## The `KS` block -/

/-- `KS` holds the state `S` (replicated) with the rate lanes `1, 2, 8, 12` un-complemented. -/
def KSU (M : ByteArray) (S : MlDsa44.Fips202.SpongeState) : Prop :=
  ∀ x, x < 25 → word M (KS + 32 * x) =
    rep (if x = 1 ∨ x = 2 ∨ x = 8 ∨ x = 12 then laneOf S x else cpl x (laneOf S x))

theorem notw_eq : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat) = 2 ^ 256 - 1 := by norm_num

theorem ksu_of_flip {M M' : ByteArray} {S : MlDsa44.Fips202.SpongeState} (hK : KS1 M S)
    (h : ∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) : KSU M' S := by
  intro x hx
  rw [h x hx]
  unfold flip4
  split
  · rename_i hx4
    rw [hK x hx, notw_eq]
    exact MlDsaOpt44.Proofs.not_rep_cpl (by simp only [complemented]; simp; omega)
      (MlDsaOpt44.Proofs.laneOf_lt _ _)
  · rw [hK x hx]

theorem ks1_of_flip {M M' : ByteArray} {S : MlDsa44.Fips202.SpongeState} (hK : KSU M S)
    (h : ∀ x, x < 25 → word M' (KS + 32 * x) = flip4 M x) : KS1 M' S := by
  intro x hx
  rw [h x hx]
  unfold flip4
  split
  · rename_i hx4
    rw [hK x hx, if_pos hx4, notw_eq, MlDsaOpt44.Proofs.not_rep (MlDsaOpt44.Proofs.laneOf_lt _ _)]
    unfold cpl
    rw [if_pos (by simp only [complemented]; simp; omega)]
  · rename_i hx4
    rw [hK x hx, if_neg hx4]

/-- The byte the scan reads from a replicated lane. -/
theorem rep_byte (v : Nat) {r : Nat} (hr : r < 8) :
    255 &&& rep v / 2 ^ (r * 8) = v / 2 ^ (8 * r) % 256 := by
  have hpow : 2 ^ (8 * r) * (256 * 2 ^ (56 - 8 * r)) = 2 ^ 64 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  have key : rep v = v + 2 ^ (8 * r) * (256 * (2 ^ (56 - 8 * r) * (v * (1 + 2 ^ 64 + 2 ^ 128)))) := by
    calc rep v = v + 2 ^ 64 * (v * (1 + 2 ^ 64 + 2 ^ 128)) := by unfold rep REP pack4; ring
      _ = _ := by rw [← hpow]; ring
  rw [Nat.and_comm, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm r 8, key, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem ksu_byte {M : ByteArray} {S : MlDsa44.Fips202.SpongeState} (hK : KSU M S) {q : Nat}
    (hq : q < 136) :
    255 &&& word M (q / 8 * 32) / 2 ^ (q % 8 * 8) = laneOf S (q / 8) / 2 ^ (8 * (q % 8)) % 256 := by
  rw [show q / 8 * 32 = KS + 32 * (q / 8) by simp only [KS]; omega, hK _ (by omega)]
  have hc : (if q / 8 = 1 ∨ q / 8 = 2 ∨ q / 8 = 8 ∨ q / 8 = 12 then laneOf S (q / 8)
      else cpl (q / 8) (laneOf S (q / 8))) = laneOf S (q / 8) := by
    split
    · rfl
    · unfold cpl
      rw [if_neg (by simp only [complemented]; simp; omega)]
  rw [hc]
  exact rep_byte _ (by omega)

/-- The seed state of `c̃`. -/
abbrev S0 (cd : ByteArray) : MlDsa44.Fips202.SpongeState :=
  MlDsaOpt44.Proofs.seedState 136 (ctOf cd)

theorem permN_succ' (n : Nat) (S : MlDsa44.Fips202.SpongeState) :
    permN (n + 1) S = EvmSemantics.Crypto.Keccak.permute (permN n S) := by
  unfold permN; rw [Function.iterate_succ_apply']

/-- Byte `p` of `H(c̃)` read from the block in `KS`. -/
theorem ksu_stream_byte {cd M : ByteArray} (hcd : Z0 ≤ cd.size) {p : Nat} (hp : p < 272)
    (hK : KSU M (permN (p / 136 + 1) (S0 cd))) :
    255 &&& word M (p % 136 / 8 * 32) / 2 ^ (p % 136 % 8 * 8) = (cStream cd)[p]!.toNat := by
  rw [ksu_byte hK (Nat.mod_lt _ (by norm_num)),
    ← le64_cStream hcd (j := p / 136) (x := p % 136 / 8) (by omega) (by omega),
    le64_byte _ _ _ (by omega), byteAt_eq_get]
  congr 2
  omega

theorem land_rep {v : Nat} (hv : v < 2 ^ 64) : 18446744073709551615 &&& rep v = v := by
  rw [Nat.and_comm, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,
    show rep v = v * 6277101735386680764176071790128604879584176795969512275969 by
      unfold rep REP pack4; norm_num]
  omega

/-- `KS`, `KB` and `KZ` changes (`kf1`) keep the bookkeeping. -/
theorem sinv_frameKS {m M M' : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i)
    (hi : i ≤ 256)
    (hf : FrameExcept M M' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)]) : SInv m M' c i := by
  have hw : ∀ a, 1824 ≤ a → a + 32 ≤ TOP → word M' a = word M a := fun a ha ht =>
    hf.word (by simp only [avoids_cons, avoids_nil, and_true, KS, KB, KZ, TOP] at *; omega)
  have hb : ∀ a, 1824 ≤ a → a + 1 ≤ TOP → byteAt M' a = byteAt M a := fun a ha ht =>
    hf.byteAt (by simp only [avoids_cons, avoids_nil, and_true, KS, KB, KZ, TOP] at *; omega)
  obtain ⟨hfr, hcw, hnneg, hcnt, ⟨f, finj, fmem, fslot⟩, hidx0, hfree⟩ := h
  refine ⟨(hfr.trans hf).mono ?_, fun t ht => ?_, ?_, ?_, ⟨f, finj, fmem, fun s hs => ?_⟩,
    fun t ht hc => ?_, fun s h1 h2 => ?_⟩
  · intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact ⟨r, h, le_rfl, le_rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact ⟨_, by simp [sibRegions], le_rfl, le_rfl⟩
  · rw [hw _ (by simp only [CW]; omega) (by simp only [CW, TOP]; omega)]; exact hcw t ht
  · rw [hw _ (by simp only [NNEG]; omega) (by simp only [NNEG, TOP]; omega)]; exact hnneg
  · rw [hw _ (by simp only [CNT]; omega) (by simp only [CNT, TOP]; omega)]; exact hcnt
  · have hfs := ((fmem (f s)).1 ⟨s, hs, rfl⟩).1
    rw [hw _ (by simp only [BASES]; omega) (by simp only [BASES, TOP]; omega),
      hb _ (by simp only [IDX]; omega) (by simp only [IDX, TOP]; omega)]; exact fslot s hs
  · rw [hb _ (by simp only [IDX]; omega) (by simp only [IDX, TOP]; omega)]; exact hidx0 t ht hc
  · rw [hw _ (by simp only [BASES]; omega) (by simp only [BASES, TOP]; omega)]; exact hfree s h1 h2

theorem rc1_of_frame {m M : ByteArray} (hrc : RC1Table m) (hf : FrameExcept m M sibRegions) :
    RC1Table M := fun i hi => by
  have hav : Avoids sibRegions (RC1 + 32 * i) (RC1 + 32 * i + 32) := by
    simp only [sibRegions, avoids_cons, avoids_nil, and_true, KS, KB, KZ, CW, BASES, IDX, NNEG, RC1]
    omega
  rw [hf.word hav]
  exact hrc i hi

theorem frame_mstore8 (m : ByteArray) (a : Nat) (b : UInt8) :
    FrameExcept m (MachineState.writeBytes m (ByteArray.mk #[b]) a) [(a, a + 1)] :=
  FrameExcept.writeBytes m _ a

theorem ksu_scan {M : ByteArray} {S : MlDsa44.Fips202.SpongeState} (hK : KSU M S) (c : Fips204.Poly)
    {i j nn sg code cnt : Nat} :
    KSU (memC (sibMB M c i j nn sg code) j sg cnt) S := by
  have hA : ∀ M0 : ByteArray, FrameExcept M0 (memA M0 i j nn sg code)
      ([(12288 + i * 32, 12288 + i * 32 + 32)] ++ [(4000, 4000 + 32)] ++
        [(12288 + j * 32, 12288 + j * 32 + 32)]) := fun M0 =>
    ((FrameExcept.mstore _ _ _).trans (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)
  have hB : ∀ (M0 : ByteArray) (k bv : Nat), FrameExcept M0 (memB M0 i j k bv)
      ([(49120 + k * 32, 49120 + k * 32 + 32)] ++ [(51200 + i, 51200 + i + 1)]) := fun M0 k bv =>
    (FrameExcept.mstore _ _ _).trans (frame_mstore8 _ _ _)
  have hC : ∀ M0 : ByteArray, FrameExcept M0 (memC M0 j sg cnt)
      ([(51200 + j, 51200 + j + 1)] ++ [(4032, 4032 + 32)] ++
        [(49120 + (1 + cnt) * 32, 49120 + (1 + cnt) * 32 + 32)]) := fun M0 =>
    ((frame_mstore8 _ _ _).trans (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)
  intro x hx
  rw [← hK x hx]
  have hav : ∀ rs : List (Nat × Nat), (∀ r ∈ rs, 4000 ≤ r.1) →
      Avoids rs (KS + 32 * x) (KS + 32 * x + 32) := fun rs h r hr => by
    have := h r hr; simp only [KS]; omega
  have hge : ∀ (rs : List (Nat × Nat)) (r : Nat × Nat), r ∈ rs → (∀ r ∈ rs, 4000 ≤ r.1) →
      4000 ≤ r.1 := fun _ r hr h => h r hr
  unfold sibMB
  split
  · rw [(hC _).word (hav _ (by simp; omega)), (hA _).word (hav _ (by simp; omega))]
  · rw [(hC _).word (hav _ (by simp; omega)), (hB _ _ _).word (hav _ (by simp; omega)),
      (hA _).word (hav _ (by simp; omega))]

/-- One visit of the loop head (`p < 272`): `p = 136` refills `KS` with the second block. -/
theorem sib_visit {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (htail : tail.length ≤ 960) {M : ByteArray} (hrc : RC1Table M)
    {cd : ByteArray} {p : Nat} (hp : p < 272) (hK : KSU M (permN (if p ≤ 136 then 1 else 2) (S0 cd)))
    (i sg : Nat) :
    ∃ M1, KSU M1 (permN (p / 136 + 1) (S0 cd)) ∧
      FrameExcept M M1 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] ∧
      Reach (headSt s ret tail p i sg M) (nokSt s ret tail p i sg M1)
        (48 + if p = 136 then 32706 else 0) := by
  by_cases h136 : p = 136
  · subst h136
    obtain ⟨M2, h2, f2, r2⟩ := sib_rpre hs htail M i sg
    have hK2 : KS1 M2 (permN 1 (S0 cd)) := ks1_of_flip hK h2
    obtain ⟨M3, h3, f3, c3⟩ := kf1_call hs (ret := 8722)
      (tail := [wd 136, wd i, wd sg, wd ret] ++ tail)
      (hr.callee (by simp [Stack.sib, Stack.kf1, Stack.leaf]) (by simp only [isValidJumpDest_lit])
        (by norm_num)) M2
      (fun a ha => by
        rw [f2.word (by simp only [avoids_cons, avoids_nil, and_true, KS, RC1]; omega)]
        exact hrc a ha)
    rw [call_iff] at c3
    have hK3 : KS1 M3 (permN 2 (S0 cd)) := by
      rw [permN_succ']
      exact h3 _ (MlDsaOpt44.Proofs.permN_size (MlDsaOpt44.Proofs.seedState_size _ _) 1) hK2
    obtain ⟨M4, h4, f4, r4⟩ := sib_rpost hs htail M3 i sg
    refine ⟨M4, ksu_of_flip hK3 h4, ?_, ?_⟩
    · refine ((f2.trans f3).trans f4).mono ?_
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h <;> subst h <;> simp
    · exact ((r2.trans c3).trans r4).mono (by norm_num [Gas.kf1])
  · refine ⟨M, ?_, FrameExcept.refl _ _, ?_⟩
    · have : (if p ≤ 136 then 1 else 2) = p / 136 + 1 := by split <;> omega
      rwa [this] at hK
    · rw [if_neg h136]
      exact (sib_nok hs htail M p i sg hp h136).mono (by omega)

/-! ## The scan -/

theorem zeroPoly_get (t : Nat) : Fips204.zeroPoly[t]! = (0 : Int) := by
  simp only [Fips204.zeroPoly, getElem!_def, Array.getElem?_replicate]
  split <;> rename_i h <;> [skip; rfl]
  split at h <;> simp_all

/-- Positions at or above the index are still empty. -/
theorem ballFold_high (bs : ByteArray) :
    ∀ k t, (ballFold P bs k).2 ≤ t → (ballFold P bs k).1[t]! = 0
  | 0, t, _ => by rw [ballFold_zero P]; exact zeroPoly_get t
  | k + 1, t, ht => by
    have ih := ballFold_high bs k
    rw [ballFold_succ] at ht ⊢
    unfold ballStep at ht ⊢
    by_cases hc : (ballFold P bs k).2 < 256 ∧ bs[8 + k]!.toNat ≤ (ballFold P bs k).2
    · rw [if_pos hc] at ht ⊢
      simp only at ht
      simp only [ballSet]
      rw [getElem!_set!, getElem!_set!, if_neg (fun h => by omega), if_neg (fun h => by omega)]
      exact ih t (by omega)
    · rw [if_neg hc] at ht ⊢; exact ih t ht

/-- Once all `τ` coefficients are placed the scan stops changing. -/
theorem ballFold_stop (bs : ByteArray) (k : Nat) (hk : 256 ≤ (ballFold P bs k).2) :
    ∀ d, ballFold P bs (k + d) = ballFold P bs k
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc, ballFold_succ, ballFold_stop bs k hk d]
    unfold ballStep; rw [if_neg (fun h => by omega)]

/-- Cost potential at the loop head (position `p`, index `i`): the second block is still
to be squeezed while `p ≤ 136`. -/
def pot (p i : Nat) : Nat := 158 * (272 - p) + 329 * (256 - i) + 43 + if p ≤ 136 then 32706 else 0

/-! Potential steps of the scan, stated with only the bounds they need (the
in-place `unfold pot; split_ifs <;> omega` saw the whole loop context). -/

theorem pot_visit {k : Nat} (i : Nat) (hk : k < 264) :
    (48 + if 8 + k = 136 then 32706 else 0) + pot (8 + k + 1) i + 110 ≤ pot (8 + k) i := by
  unfold pot; split_ifs <;> omega

theorem pot_accA {k i : Nat} (hk : k < 264) (hi : i < 256) :
    (48 + if 8 + k = 136 then 32706 else 0) + 286 + 153 ≤ pot (8 + k) i := by
  unfold pot; split_ifs <;> omega

theorem pot_accC {k i : Nat} (hk : k < 264) (hi : i < 256) :
    (48 + if 8 + k = 136 then 32706 else 0) + 286 + 143 + pot (8 + (k + 1)) (i + 1) ≤
      pot (8 + k) i := by
  unfold pot; split_ifs <;> omega

section
/- Keep `KSU` folded while elaborating the recursion: matching its pattern
variables against the discriminants otherwise unfolds `word` down to the
memory bytes before failing (16 s). -/
attribute [local irreducible] KSU

set_option maxHeartbeats 1000000 in
theorem sib_loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (htail : tail.length ≤ 960)
    (hsized : 2897 ≤ s.activeWords.toNat) {cd : ByteArray} (hcd : Z0 ≤ cd.size)
    (m : ByteArray) (hrc : RC1Table m) :
    ∀ n k M, n = 264 - k → k ≤ 264 → (ballFold P (cStream cd) k).2 < 256 →
      SInv m M (ballFold P (cStream cd) k).1 (ballFold P (cStream cd) k).2 →
      KSU M (permN (if 8 + k ≤ 136 then 1 else 2) (S0 cd)) →
      ∃ M' k', k' ≤ 264 ∧
        SInv m M' (ballFold P (cStream cd) k').1 (ballFold P (cStream cd) k').2 ∧
        ballFold P (cStream cd) 264 = ballFold P (cStream cd) k' ∧
        Reach (headSt s ret tail (8 + k) (ballFold P (cStream cd) k).2
            (le64 (cStream cd) 0 / 2 ^ ((ballFold P (cStream cd) k).2 - 196)) M)
          (callState s ret (wd (if (ballFold P (cStream cd) 264).2 < 256 then 0 else 1) :: tail) M')
          (pot (8 + k) (ballFold P (cStream cd) k).2)
  | 0, k, M, hn, hk, hlt, hinv, _ => by
    have hk264 : k = 264 := by omega
    subst hk264
    refine ⟨M, 264, le_rfl, hinv, rfl, ?_⟩
    rw [if_pos hlt]
    exact (sib_fail hs htail M hr.jumpdest hr.small _ _).mono (by unfold pot; omega)
  | n + 1, k, M, hn, hk, hlt, hinv, hK => by
    obtain ⟨hsz, hi1, hi2, -⟩ := ballFold_inv P (cStream cd) k
    simp only [tau_eq] at hi1
    have hhigh := ballFold_high (cStream cd) k
    have hsucc := ballFold_succ P (cStream cd) k
    rcases hF : ballFold P (cStream cd) k with ⟨c, i⟩
    rw [hF] at hsz hi1 hi2 hhigh hsucc hlt hinv
    simp only at hsz hi1 hi2 hhigh hlt hinv ⊢
    -- the visit (and the refill at `p = 136`)
    obtain ⟨M1, hK1, hf1, hV⟩ := sib_visit hs hr htail (rc1_of_frame hrc hinv.frame) (p := 8 + k)
      (by omega) hK i (le64 (cStream cd) 0 / 2 ^ (i - 196))
    have hinv1 := sinv_frameKS hinv hi2 hf1
    have hj := ksu_stream_byte hcd (p := 8 + k) (by omega) hK1
    have hsigns : le64 (cStream cd) 0 / 2 ^ (i - 196) < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans (le64_lt _ 0) (by norm_num))
    have hj256 : (cStream cd)[8 + k]!.toNat < 256 := UInt8.toNat_lt _
    have hKn : ∀ M2 : ByteArray, KSU M2 (permN ((8 + k) / 136 + 1) (S0 cd)) →
        KSU M2 (permN (if 8 + (k + 1) ≤ 136 then 1 else 2) (S0 cd)) := fun M2 h => by
      have : (if 8 + (k + 1) ≤ 136 then 1 else 2) = (8 + k) / 136 + 1 := by split <;> omega
      rwa [this]
    have hvc : (48 + if 8 + k = 136 then 32706 else 0) + pot (8 + k + 1) i + 110 ≤ pot (8 + k) i :=
      pot_visit i (by omega)
    by_cases hacc : (cStream cd)[8 + k]!.toNat ≤ i
    · -- accept
      have hst : ballFold P (cStream cd) (k + 1) =
          (ballSet P (cStream cd) c i (cStream cd)[8 + k]!.toNat, i + 1) := by
        rw [hsucc]; unfold ballStep; rw [if_pos ⟨hlt, hacc⟩]
      have hsg1 : Fips204.bit (cStream cd) (i - 196) ≤ 1 := by unfold Fips204.bit; omega
      have hset : ballSet P (cStream cd) c i (cStream cd)[8 + k]!.toNat =
          (c.set! i c[(cStream cd)[8 + k]!.toNat]!).set! (cStream cd)[8 + k]!.toNat
            (sgnOf (Fips204.bit (cStream cd) (i - 196))) := by
        unfold ballSet ballSign sgnOf
        rw [show i + P.tau - 256 = i - 196 by simp only [tau_eq]; omega]
      have hsg := sign_bit (cStream cd) (i - 196) (by omega)
      generalize Fips204.bit (cStream cd) (i - 196) = sg at hsg1 hset hsg
      generalize (cStream cd)[8 + k]!.toNat = j at hj hj256 hacc hst hset
      have hcode : UInt256.ofNat (sg * 2) - UInt256.ofNat 1 =
          UInt256.ofNat (if sg = 1 then 1 else 2 ^ 256 - 1) := by
        rcases (by omega : sg = 0 ∨ sg = 1) with h | h <;> subst h <;> decide
      have hcode' : (if sg = 1 then 1 else 2 ^ 256 - 1) < 2 ^ 256 := by split <;> norm_num
      have hnn : word M1 4000 = negCount c := hinv1.nneg
      have hnn' : negCount c ≤ 256 := by rw [negCount_eq]; exact cntTo_le c 256
      obtain ⟨hkf, hcntB, hinv'⟩ := sinv_accept (nn := negCount c)
        (code := if sg = 1 then 1 else 2 ^ 256 - 1) hinv1 hsz hi1 hlt hacc hhigh hsg1 rfl rfl
      have hAB : Reach (nokSt s ret tail (8 + k) i (le64 (cStream cd) 0 / 2 ^ (i - 196)) M1)
          (callState s 8879 (wd (byteAt M1 (IDX + j)) :: wd sg :: wd j :: wd (8 + k + 1) :: wd i ::
            wd (le64 (cStream cd) 0 / 2 ^ (i - 196)) :: wd ret :: tail)
            (sibMB M1 c i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1))) 286 := by
        by_cases hk0 : byteAt M1 (IDX + j) = 0
        · have hMB : sibMB M1 c i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1) =
              memA M1 i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1) := by
            unfold sibMB; rw [if_pos hk0]
          rw [hMB, hk0]
          exact (sib_accA0 hs htail hsized M1 (8 + k) i _ (by omega) hlt j hj hacc sg hsg hsg1
            _ hnn hnn' _ hcode hcode' hk0).mono (by omega)
        · obtain ⟨hk40, hbv⟩ := hkf hk0
          have hMB : sibMB M1 c i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1) =
              memB (memA M1 i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1)) i j
                (byteAt M1 (IDX + j)) (baseOf c j) := by
            unfold sibMB; rw [if_neg hk0]
          rw [hMB]
          exact (sib_accA1 hs htail hsized M1 (8 + k) i _ (by omega) hlt j hj hacc sg hsg hsg1
            _ hnn hnn' _ hcode hcode' (byteAt M1 (IDX + j)) rfl (by omega) (by omega)).trans
            (sib_accB hs htail hsized _ _ i _ j sg _ hlt hacc (by omega) _ hbv
              (by have := baseOf_le c j (by omega); omega))
      have hdiv : le64 (cStream cd) 0 / 2 ^ (i - 196) / 2 = le64 (cStream cd) 0 / 2 ^ (i + 1 - 196) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (i - 196).succ = i + 1 - 196 by omega]
      rw [← hset] at hinv'
      have hvA : (48 + if 8 + k = 136 then 32706 else 0) + 286 + 153 ≤ pot (8 + k) i :=
        pot_accA (by omega) (by omega)
      by_cases hlast : i + 1 < 256
      · have hKC := ksu_scan hK1 c (i := i) (j := j) (nn := negCount c) (sg := sg)
          (code := if sg = 1 then 1 else 2 ^ 256 - 1) (cnt := i - 196)
        obtain ⟨M', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd m hrc n
          (k + 1) _ (by omega) (by omega) (by rw [hst]; exact hlast) (by rw [hst]; exact hinv')
          (hKn _ hKC)
        rw [hst] at hreach
        try simp only at hreach
        refine ⟨M', k', hk', hinvF, hfold, ?_⟩
        have hC := sib_accC (ret := ret) hs htail hsized
          (sibMB M1 c i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1)) (8 + k + 1) i
          (le64 (cStream cd) 0 / 2 ^ (i - 196)) j sg (byteAt M1 (IDX + j)) hlast (by omega) hsg1 hsigns
          (i - 196) hcntB (by omega)
        rw [hdiv, show 8 + k + 1 = 8 + (k + 1) by omega] at hC
        have hvC : (48 + if 8 + k = 136 then 32706 else 0) + 286 + 143 + pot (8 + (k + 1)) (i + 1) ≤
            pot (8 + k) i :=
          pot_accC (by omega) (by omega)
        exact (((hV.trans hAB).trans hC).trans hreach).mono hvC
      · have hD := sib_accD hs htail hsized
          (sibMB M1 c i j (negCount c) sg (if sg = 1 then 1 else 2 ^ 256 - 1)) hr.jumpdest hr.small
          (8 + k + 1) i (le64 (cStream cd) 0 / 2 ^ (i - 196)) j sg (byteAt M1 (IDX + j)) (by omega)
          (by omega) hsg1 hsigns (i - 196) hcntB (by omega)
        have hfold : ballFold P (cStream cd) 264 = ballFold P (cStream cd) (k + 1) := by
          have := ballFold_stop (cStream cd) (k + 1) (by rw [hst]; simp only; omega) (264 - (k + 1))
          rwa [show k + 1 + (264 - (k + 1)) = 264 by omega] at this
        refine ⟨_, k + 1, by omega, by rw [hst]; exact hinv', hfold, ?_⟩
        rw [hfold, hst, if_neg (by simp only; omega)]
        exact ((hV.trans hAB).trans hD).mono hvA
    · -- reject
      have hst : ballFold P (cStream cd) (k + 1) = (c, i) := by
        rw [hsucc]; unfold ballStep; rw [if_neg (fun h => hacc h.2)]
      obtain ⟨M', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd m hrc n
        (k + 1) M1 (by omega) (by omega) (by rw [hst]; exact hlt) (by rw [hst]; exact hinv1)
        (hKn _ hK1)
      rw [hst] at hreach
      try simp only at hreach
      refine ⟨M', k', hk', hinvF, hfold, ?_⟩
      have hR := sib_reject (ret := ret) hs htail hsized M1 (8 + k) i
        (le64 (cStream cd) 0 / 2 ^ (i - 196)) (by omega) _ hj (by omega) hj256 hlt
      rw [show 8 + k + 1 = 8 + (k + 1) by omega] at hR
      exact ((hV.trans hR).trans hreach).mono (by
        have : 8 + k + 1 = 8 + (k + 1) := by omega
        rw [this] at hvc; omega)

end

/-- The final invariant is `CRep`. -/
theorem crep_of_sinv {m M : ByteArray} {c : Fips204.Poly} (h : SInv m M c 256) : CRep M c := by
  obtain ⟨-, hcw, hnneg, -, ⟨f, finj, fmem, fslot⟩, -, -⟩ := h
  have hget : ∀ s, s < 60 → ((List.range 60).map f)[s]! = f s := fun s hs => by
    rw [getElem!_pos ((List.range 60).map f) s (by simp; omega)]
    simp
  refine ⟨hcw, hnneg, (List.range 60).map f, by simp [tau_eq], ?_, fun p => ?_, fun s hs => ?_⟩
  · exact List.Nodup.map_on (fun x hx y hy e => finj x y (by simpa using hx) (by simpa using hy) e)
      List.nodup_range
  · rw [← fmem p]; simp [List.mem_map, List.mem_range]
  · simp only [tau_eq] at hs
    rw [hget s hs]; exact (fslot s hs).1

theorem bases_le {m M : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i) (s : Nat)
    (hs : s < 60) : word M (BASES + 32 * s) ≤ 6112 := by
  obtain ⟨-, -, -, -, ⟨f, -, fmem, fslot⟩, -, hfree⟩ := h
  by_cases hsn : s < i - 196
  · rw [(fslot s hsn).1]
    have := baseOf_le c (f s) ((fmem (f s)).1 ⟨s, hsn, rfl⟩).1
    omega
  · rw [hfree s (by omega) hs]; omega

end Ball

open Ball in
theorem sib_call_proof {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (hrc : RC1Table m)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hz : SibFresh m) :
    ∃ m', (∀ c, cOf s.executionEnv.calldata = some c → CRep m' c) ∧
      (∀ i, i < P.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800), (CW, CW + 8192), (BASES, BASES + 2048),
        (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (okC s.executionEnv.calldata)] m' Gas.sib := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.sib, Stack.kf1, Stack.leaf] at this; omega
  have hsized : 2897 ≤ s.activeWords.toNat := hs.sized
  have hcd' : Z0 ≤ s.executionEnv.calldata.size := by unfold Z0; unfold HDR at hcd; omega
  -- the absorption prologue
  obtain ⟨M1, h1, f1, r1⟩ := sib_zero hs (ret := ret) htail m
  obtain ⟨M2, h2, f2, r2⟩ := sib_absW0 hs (ret := ret) htail M1
  obtain ⟨M3, h3, f3, r3⟩ := sib_absW1 hs (ret := ret) htail M2
  obtain ⟨M4, h4, f4, r4⟩ := sib_pad hs (ret := ret) htail M3
  have hK4 : KS1 M4 (S0 s.executionEnv.calldata) := by
    intro x hx
    rw [h4 x hx, h3 x hx, h2 x hx, h1 x hx, laneOf_ctSeed hcd' hx]
    split_ifs <;> first
      | (exfalso; omega)
      | rfl
      | (rw [MlDsaOpt44.Proofs.rep_cpl_xor _ (by norm_num) (by first | with_reducible exact le64_lt _ _ | norm_num),
          Nat.zero_xor])
  have hav : ∀ a, a < 24 → Avoids [(KS, KS + 800)] (RC1 + 32 * a) (RC1 + 32 * a + 32) := fun a ha => by
    simp only [avoids_cons, avoids_nil, and_true, KS, RC1]; omega
  have hrc4 : RC1Table M4 := fun a ha => by
    rw [f4.word (hav a ha), f3.word (hav a ha), f2.word (hav a ha), f1.word (hav a ha)]
    exact hrc a ha
  obtain ⟨M5, h5, f5, c5⟩ := kf1_call hs (ret := 8615) (tail := [wd ret] ++ tail)
    (hr.callee (by simp [Stack.sib, Stack.kf1, Stack.leaf]) (by simp only [isValidJumpDest_lit])
      (by norm_num)) M4 hrc4
  rw [call_iff] at c5
  have hK5 : KS1 M5 (permN 1 (S0 s.executionEnv.calldata)) :=
    h5 _ (MlDsaOpt44.Proofs.seedState_size _ _) hK4
  obtain ⟨M6, h6, f6, r6⟩ := sib_post hs (ret := ret) htail M5
  have hK6 : KSU M6 (permN 1 (S0 s.executionEnv.calldata)) := ksu_of_flip hK5 h6
  have hsg : 18446744073709551615 &&& word M5 0 = le64 (cStream s.executionEnv.calldata) 0 / 2 ^ (196 - 196) := by
    have k0 := hK5 0 (by omega)
    simp only [KS, Nat.mul_zero, Nat.add_zero] at k0
    rw [k0, show cpl 0 (laneOf (permN 1 (S0 s.executionEnv.calldata)) 0) =
      laneOf (permN 1 (S0 s.executionEnv.calldata)) 0 by unfold cpl; simp [complemented],
      land_rep (MlDsaOpt44.Proofs.laneOf_lt _ _), Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact (le64_cStream hcd' (j := 0) (x := 0) (by omega) (by omega)).symm
  rw [hsg] at r6
  have hfr6 : FrameExcept m M6 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] := by
    refine (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> simp
  -- the scan
  have h0 : SInv m M6 (MlDsaOptCommon.BallScan.ballFold P (cStream s.executionEnv.calldata) 0).1
      (MlDsaOptCommon.BallScan.ballFold P (cStream s.executionEnv.calldata) 0).2 := by
    rw [MlDsaOptCommon.BallScan.ballFold_zero P]; exact sinv_frameKS (sinv_init m hz) (by omega) hfr6
  obtain ⟨M', k', hk', hinv, hfold, hreach⟩ := sib_loop hs hr htail hsized hcd' m hrc 264 0 M6 rfl
    (by omega) (by rw [MlDsaOptCommon.BallScan.ballFold_zero P]; decide) h0
    (by rw [if_pos (by norm_num)]; exact hK6)
  rw [MlDsaOptCommon.BallScan.ballFold_zero P] at hreach
  refine ⟨M', fun c hc => ?_, fun i hi => bases_le hinv i (by simpa [tau_eq] using hi),
    hinv.frame, ?_⟩
  · have hc' : Fips204.sampleInBallOf P (cStream s.executionEnv.calldata) = some c := hc
    rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P] at hc'
    split at hc'
    · exact absurd hc' (by simp)
    · rename_i hge
      simp only [Option.some.injEq] at hc'
      subst hc'
      rw [hfold] at hge ⊢
      have hi2 := (MlDsaOptCommon.BallScan.ballFold_inv P (cStream s.executionEnv.calldata) k').2.2.1
      have h256 : (MlDsaOptCommon.BallScan.ballFold P (cStream s.executionEnv.calldata) k').2 = 256 := by
        omega
      rw [h256] at hinv
      exact crep_of_sinv hinv
  · rw [call_iff, Entry.sib]
    have hflag : flag (okC s.executionEnv.calldata) =
        wd (if (MlDsaOptCommon.BallScan.ballFold P (cStream s.executionEnv.calldata) 264).2 < 256
          then 0 else 1) := by
      show flag (Fips204.sampleInBallOf P (cStream s.executionEnv.calldata)).isSome = _
      rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P]
      by_cases h : (MlDsaOptCommon.BallScan.ballFold P (cStream s.executionEnv.calldata) 264).2 < 256 <;>
        simp [h, flag]
    rw [hflag]
    exact ((((((r1.trans r2).trans r3).trans r4).trans c5).trans r6).trans hreach).mono
      (by unfold pot Gas.sib; simp only [tau_eq, Gas.kf1]; norm_num)

end MlDsaOpt87.Proofs
