import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# Byte-level facts used by the top-level proof

`BytesAt` under writes, concatenation and truncation, reading back a stored
byte string with `readPadded`, and comparing two 32-byte words.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open MlDsa44.Proofs.Infra

theorem byteAt_eq_toNat_getElem! (b : ByteArray) (i : Nat) : byteAt b i = b[i]!.toNat := by
  rw [byteAt_eq_getD, EvmProof.Memory.getD0_eq_getElem!]

theorem bytesAt_writeBytes (m bytes : ByteArray) (d : Nat) :
    BytesAt (MachineState.writeBytes m bytes d) d bytes := by
  intro i hi
  rw [byteAt_writeBytes, if_pos (by omega), Nat.add_sub_cancel_left, byteAt_eq_toNat_getElem!]

theorem bytesAt_calldatacopy (m cd : ByteArray) (d src n : Nat) (h : src + n ≤ cd.size) :
    BytesAt (MachineState.writeBytes m (MachineState.readPadded cd src n) d) d
      (cd.extract src (src + n)) := by
  rw [← EvmProof.Bytes.readPadded_eq_extract cd src n h]
  exact bytesAt_writeBytes _ _ _

theorem readPadded_of_bytesAt {m : ByteArray} {p : Nat} {b : ByteArray} (h : BytesAt m p b) :
    MachineState.readPadded m p b.size = b := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hi hi'
    have hib : i < b.size := hi'
    have h1 := EvmProof.Memory.readPadded_getElem?_getD m p b.size i
    rw [EvmProof.Memory.getD0_eq_getElem _ _ hi, if_pos hib] at h1
    rw [h1]
    have h2 := h i hib
    rw [byteAt_eq_getD, getElem!_pos b i hib] at h2
    exact UInt8.toNat_inj.mp h2

theorem bytesAt_append {m : ByteArray} {p : Nat} {a b : ByteArray} :
    BytesAt m p (a ++ b) ↔ BytesAt m p a ∧ BytesAt m (p + a.size) b := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by rw [ByteArray.size_append]; omega)
      rw [this, getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
        getElem!_pos a i hi, ByteArray.getElem_append_left hi]
    · have := h (a.size + i) (by rw [ByteArray.size_append]; omega)
      rw [← Nat.add_assoc] at this
      rw [this, getElem!_pos (a ++ b) _ (by rw [ByteArray.size_append]; omega),
        getElem!_pos b i hi, ByteArray.getElem_append_right (by omega)]
      simp
  · rintro ⟨ha, hb⟩ i hi
    rw [ByteArray.size_append] at hi
    rw [getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega)]
    by_cases hia : i < a.size
    · rw [ByteArray.getElem_append_left hia, ha i hia, getElem!_pos a i hia]
    · have := hb (i - a.size) (by omega)
      rw [show p + a.size + (i - a.size) = p + i by omega] at this
      rw [this, ByteArray.getElem_append_right (by omega), getElem!_pos b _ (by omega)]

theorem _root_.MlDsa44.Proofs.BytesAt.extract {m : ByteArray} {p : Nat} {b : ByteArray} (h : BytesAt m p b) (n : Nat) :
    BytesAt m p (b.extract 0 n) := by
  intro i hi
  have hi2 : i < (b.extract 0 n).size := hi
  rw [ByteArray.size_extract] at hi
  have hib : i < b.size := by omega
  have he : (b.extract 0 n)[i] = b[0 + i] := ByteArray.getElem_extract hi2
  rw [h i hib, getElem!_pos (b.extract 0 n) i hi2, he, getElem!_pos b i hib]
  simp

/-! ## Comparing words -/

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ w, beNat m a w < 256 ^ w
  | 0 => by simp [beNat]
  | w + 1 => by
    simp only [beNat, Nat.pow_succ]
    have := beNat_lt m a w
    have := byteAt_lt m (a + w)
    omega

theorem beNat_inj {m m' : ByteArray} {a a' : Nat} :
    ∀ w, beNat m a w = beNat m' a' w → ∀ k, k < w → byteAt m (a + k) = byteAt m' (a' + k)
  | 0, _ => fun k hk => absurd hk (Nat.not_lt_zero _)
  | w + 1, h => by
    simp only [beNat] at h
    have h1 := byteAt_lt m (a + w)
    have h2 := byteAt_lt m' (a' + w)
    have hlo : byteAt m (a + w) = byteAt m' (a' + w) := by omega
    have hhi : beNat m a w = beNat m' a' w := by omega
    intro k hk
    by_cases hkw : k = w
    · subst hkw; exact hlo
    · exact beNat_inj w hhi k (by omega)

/-- Two words agree iff their 32 bytes do. -/
theorem word_eq_word_iff {m m' : ByteArray} {a a' : Nat} :
    word m a = word m' a' ↔ ∀ k, k < 32 → byteAt m (a + k) = byteAt m' (a' + k) := by
  rw [word_eq_beNat, word_eq_beNat]
  constructor
  · exact beNat_inj 32
  · intro h
    have : ∀ w, w ≤ 32 → beNat m a w = beNat m' a' w := by
      intro w
      induction w with
      | zero => intro; rfl
      | succ w ih => intro hw; simp only [beNat]; rw [ih (by omega), h w (by omega)]
    exact this 32 le_rfl

/-- Words over stored 32-byte strings agree iff the strings do. -/
theorem word_eq_word_iff_of_bytesAt {m m' : ByteArray} {a a' : Nat} {b b' : ByteArray}
    (hb : BytesAt m a b) (hb' : BytesAt m' a' b') (hs : b.size = 32) (hs' : b'.size = 32) :
    word m a = word m' a' ↔ b = b' := by
  rw [word_eq_word_iff]
  constructor
  · intro h
    apply ByteArray.ext_getElem (by omega)
    intro i hi hi'
    have := h i (by omega)
    rw [hb i hi, hb' i hi', getElem!_pos b i hi, getElem!_pos b' i hi'] at this
    exact UInt8.toNat_inj.mp this
  · rintro rfl k hk
    rw [hb k (by omega), hb' k (by omega)]

theorem byteArray_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  change (a.data == b.data) = true ↔ a = b
  rw [beq_iff_eq, ByteArray.ext_iff]

theorem bytesAt_self (b : ByteArray) : BytesAt b 0 b := by
  intro i hi
  rw [Nat.zero_add, byteAt_eq_toNat_getElem!]

theorem byteAt_writeBytes_single (m : ByteArray) (b : UInt8) (a : Nat) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[b]) a) a = b.toNat := by
  rw [byteAt_writeBytes, if_pos (by change a ≤ a ∧ a < a + 1; omega), Nat.sub_self]
  rfl

theorem byteAt_writeBytes_single_ne (m : ByteArray) (b : UInt8) {a x : Nat} (h : x ≠ a) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[b]) a) x = byteAt m x :=
  byteAt_writeBytes_of_not_mem (by change x < a ∨ a + 1 ≤ x; omega)

end MlDsa44.Proofs.Main
