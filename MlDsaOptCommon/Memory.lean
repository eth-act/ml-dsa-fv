import MlDsaOptCommon.Basic
set_option warningAsError true
/-!
# Memory lemmas over `byteAt` / `word` / `FrameExcept`

* `activeWordsAfter_of_le`: accesses below `32 * activeWords` never grow
  memory (used by `evm_block` with an `omega` side goal).
* `byteAt_writeBytes`, `word_writeBytes_*`, `word_mstore`, `byteAt_mstore8`:
  read-after-write.
* `word_eq_beNat`: `word` is the big-endian value of 32 `byteAt`s.
* `FrameExcept.*`: reflexivity, transitivity (ranges append), monotonicity
  (more / wider ranges), and the frame of a single write.
* `BytesAt.frame`: transport across a `FrameExcept` whose ranges avoid the
  footprint (`Avoids rs lo hi`).
-/

namespace MlDsaOptCommon

open EvmSemantics
open EvmSemantics.EVM

/-! ## Active words -/

theorem activeWordsAfter_of_le {curr off sz : Nat} (h : off + sz ≤ 32 * curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · have : (off + sz - 1) / 32 + 1 ≤ curr := by omega
    exact Nat.max_eq_left this

/-! ## Bytes -/

theorem byteAt_eq_getD (m : ByteArray) (a : Nat) : byteAt m a = (m[a]?.getD 0).toNat := by
  unfold byteAt
  by_cases h : a < m.size
  · rw [dif_pos h, getElem?_pos m a h, Option.getD_some]
  · rw [dif_neg h, getElem?_neg m a h, Option.getD_none]; rfl

theorem byteAt_lt (m : ByteArray) (a : Nat) : byteAt m a < 256 := by
  unfold byteAt; split
  · exact (m[a]).toNat_lt
  · omega

theorem byteAt_writeBytes (m bytes : ByteArray) (start a : Nat) :
    byteAt (MachineState.writeBytes m bytes start) a =
      if start ≤ a ∧ a < start + bytes.size then byteAt bytes (a - start) else byteAt m a := by
  rw [byteAt_eq_getD, MachineState.writeBytes_getElem?_getD]
  split <;> rw [byteAt_eq_getD]

theorem byteAt_writeBytes_of_not_mem {m bytes : ByteArray} {start a : Nat}
    (h : a < start ∨ start + bytes.size ≤ a) :
    byteAt (MachineState.writeBytes m bytes start) a = byteAt m a := by
  rw [byteAt_writeBytes, if_neg (by omega)]

/-- MSTORE8 writes the low byte. -/
theorem byteAt_mstore8 (m : ByteArray) (a v : Nat) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[UInt8.ofNat (v % 256)]) a) a = v % 256 := by
  have hsize : (ByteArray.mk #[UInt8.ofNat (v % 256)]).size = 1 := rfl
  rw [byteAt_writeBytes, if_pos (by omega), Nat.sub_self, byteAt, dif_pos (by omega)]
  change (UInt8.ofNat (v % 256)).toNat = v % 256
  rw [UInt8.toNat_ofNat', Nat.mod_mod]

/-! ## Words -/

/-- Big-endian value of `w` bytes of `m` from `a`. -/
def beNat (m : ByteArray) (a : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => beNat m a w * 256 + byteAt m (a + w)

theorem bytesToNatPadded_eq_beNat (m : ByteArray) (a w : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded m a w = beNat m a w := by
  induction w with
  | zero => simp [beNat]
  | succ w ih =>
    rw [EvmProof.Bytes.bytesToNatPadded_succ, ih, beNat]
    congr 1
    unfold YulSemantics.EVM.byteFrom
    rw [byteAt_eq_getD, EvmProof.Bytecode.toList_eq_data, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]
    rfl

/-- `word` is the big-endian value of the 32 bytes at `a`. -/
theorem word_eq_beNat (m : ByteArray) (a : Nat) : word m a = beNat m a 32 := by
  unfold word
  rw [EvmProof.Bytes.readWord_toNat, bytesToNatPadded_eq_beNat]

theorem beNat_congr {m m' : ByteArray} {a : Nat} :
    ∀ w, (∀ k, k < w → byteAt m' (a + k) = byteAt m (a + k)) → beNat m' a w = beNat m a w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [beNat]
    rw [beNat_congr w (fun k hk => h k (by omega)), h w (by omega)]

theorem word_congr {m m' : ByteArray} {a : Nat}
    (h : ∀ k, k < 32 → byteAt m' (a + k) = byteAt m (a + k)) : word m' a = word m a := by
  rw [word_eq_beNat, word_eq_beNat, beNat_congr 32 h]

/-- MLOAD / CALLDATALOAD results in `word` form (used by `evm_block`). -/
theorem readWord_eq_word (m : ByteArray) (a : Nat) :
    MachineState.readWord m a = UInt256.ofNat (word m a) :=
  (EvmProof.Word.word_eq_ofNat_toNat _)

theorem word_lt (m : ByteArray) (a : Nat) : word m a < 2 ^ 256 := (MachineState.readWord m a).val.isLt

/-- `word m a % 2^256` (with the modulus as `evm_block` prints it) is `word m a`. -/
theorem word_mod (m : ByteArray) (a : Nat) :
    word m a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      word m a :=
  Nat.mod_eq_of_lt (word_lt m a)

/-- MSTORE then MLOAD at the same address. -/
theorem word_mstore (m : ByteArray) (a v : Nat) (hv : v < 2 ^ 256) :
    word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) a) a = v := by
  unfold word
  rw [EvmProof.Memory.readWord_writeBytes_of_lt _ _ _ (by simpa using hv),
    EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem word_writeBytes_disjoint (m bytes : ByteArray) {start a : Nat}
    (h : a + 32 ≤ start ∨ start + bytes.size ≤ a) :
    word (MachineState.writeBytes m bytes start) a = word m a := by
  unfold word
  rw [EvmProof.Memory.readWord_writeBytes_disjoint m bytes a start h]

theorem natToBytesPadded_size (v w : Nat) : (Data.Bytes.natToBytesPadded v w).size = w := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

/-- MSTORE leaves other aligned words alone. -/
theorem word_mstore_disjoint (m : ByteArray) {a b : Nat} (v : Nat)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) b) a = word m a :=
  word_writeBytes_disjoint m _ (by rw [natToBytesPadded_size]; exact h)

/-! ## Frames -/

/-- `[lo, hi)` avoids every range of `rs`. -/
def Avoids (rs : List (Nat × Nat)) (lo hi : Nat) : Prop := ∀ r ∈ rs, hi ≤ r.1 ∨ r.2 ≤ lo

@[simp] theorem avoids_nil (lo hi : Nat) : Avoids [] lo hi := by simp [Avoids]

@[simp] theorem avoids_cons (r : Nat × Nat) (rs : List (Nat × Nat)) (lo hi : Nat) :
    Avoids (r :: rs) lo hi ↔ (hi ≤ r.1 ∨ r.2 ≤ lo) ∧ Avoids rs lo hi := by
  simp [Avoids]

@[simp] theorem avoids_append (rs rs' : List (Nat × Nat)) (lo hi : Nat) :
    Avoids (rs ++ rs') lo hi ↔ Avoids rs lo hi ∧ Avoids rs' lo hi := by
  simp [Avoids, or_imp, forall_and]

theorem Avoids.mono {rs : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : Avoids rs lo hi)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : Avoids rs lo' hi' := by
  intro r hr; rcases h r hr with h | h <;> omega

theorem FrameExcept.refl (m : ByteArray) (rs : List (Nat × Nat)) : FrameExcept m m rs :=
  fun _ _ => rfl

theorem FrameExcept.trans {m₁ m₂ m₃ : ByteArray} {rs rs' : List (Nat × Nat)}
    (h₁ : FrameExcept m₁ m₂ rs) (h₂ : FrameExcept m₂ m₃ rs') :
    FrameExcept m₁ m₃ (rs ++ rs') := by
  intro a ha
  rw [h₂ a (fun r hr => ha r (List.mem_append_right _ hr)),
    h₁ a (fun r hr => ha r (List.mem_append_left _ hr))]

/-- Weaken a frame: every old range must sit inside some new range. -/
theorem FrameExcept.mono {m m' : ByteArray} {rs rs' : List (Nat × Nat)}
    (h : FrameExcept m m' rs)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.2 ≤ r'.2) : FrameExcept m m' rs' := by
  intro a ha
  apply h a
  intro r hr
  obtain ⟨r', hr', h1, h2⟩ := hsub r hr
  rcases ha r' hr' with h | h <;> omega

theorem FrameExcept.writeBytes (m bytes : ByteArray) (start : Nat) :
    FrameExcept m (MachineState.writeBytes m bytes start) [(start, start + bytes.size)] := by
  intro a ha
  exact byteAt_writeBytes_of_not_mem (by simpa using ha (start, start + bytes.size) (by simp))

theorem FrameExcept.mstore (m : ByteArray) (a v : Nat) :
    FrameExcept m (MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) a) [(a, a + 32)] := by
  have := FrameExcept.writeBytes m (Data.Bytes.natToBytesPadded v 32) a
  rwa [natToBytesPadded_size] at this

theorem FrameExcept.byteAt {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs)
    {a : Nat} (ha : Avoids rs a (a + 1)) : byteAt m' a = byteAt m a :=
  h a (fun r hr => by rcases ha r hr with h | h <;> omega)

theorem FrameExcept.word {m m' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept m m' rs)
    {a : Nat} (ha : Avoids rs a (a + 32)) : word m' a = word m a :=
  word_congr fun k hk => FrameExcept.byteAt h (ha.mono (by omega) (by omega))

theorem BytesAt.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {base : Nat} {b : ByteArray}
    (hb : BytesAt m base b) (h : FrameExcept m m' rs) (ha : Avoids rs base (base + b.size)) :
    BytesAt m' base b := fun i hi => by
  rw [FrameExcept.byteAt h (ha.mono (by omega) (by omega))]; exact hb i hi

/-! ## Word-array stores (loops `for k < n: mstore(base + 32 k, v k)`) -/

/-- Memory after storing `v 0, …, v (n-1)` at `base, base + 32, …`. -/
def storeWords (m : ByteArray) (base : Nat) (v : Nat → Nat) (n : Nat) : ByteArray :=
  (List.range n).foldl
    (fun mm k => MachineState.writeBytes mm (Data.Bytes.natToBytesPadded (v k) 32) (base + k * 32)) m

@[simp] theorem storeWords_zero (m : ByteArray) (base : Nat) (v : Nat → Nat) :
    storeWords m base v 0 = m := rfl

theorem storeWords_succ (m : ByteArray) (base : Nat) (v : Nat → Nat) (n : Nat) :
    storeWords m base v (n + 1) =
      MachineState.writeBytes (storeWords m base v n)
        (Data.Bytes.natToBytesPadded (v n) 32) (base + n * 32) := by
  simp [storeWords, List.range_succ, List.foldl_append]

theorem word_storeWords {m : ByteArray} {base : Nat} {v : Nat → Nat} {i : Nat}
    (hv : v i < 2 ^ 256) : ∀ n, i < n → word (storeWords m base v n) (base + 32 * i) = v i
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [storeWords_succ]
    by_cases hin : i = n
    · subst hin; rw [show base + i * 32 = base + 32 * i by omega, word_mstore _ _ _ hv]
    · rw [word_mstore_disjoint _ _ (by omega)]
      exact word_storeWords hv n (by omega)

theorem FrameExcept.storeWords (m : ByteArray) (base : Nat) (v : Nat → Nat) :
    ∀ n, FrameExcept m (MlDsaOptCommon.storeWords m base v n) [(base, base + 32 * n)]
  | 0 => fun _ _ => rfl
  | n + 1 => by
    rw [storeWords_succ]
    apply FrameExcept.mono
      (FrameExcept.trans (FrameExcept.storeWords m base v n) (FrameExcept.mstore _ _ _))
    intro r hr
    refine ⟨(base, base + 32 * (n + 1)), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

end MlDsaOptCommon
