import MlDsaOpt44.Fn.Blk.Bits
/-!
# `blk`: memory facts about the block transformers (WP3)

* `word_flipW`, `word_wb`: read-after-write for the lane flips and the
  candidate/flag stores; `word_candMem`, `frame_candMem`.
* `word_flip6_*`: which words `flip6` changes; `ks_lane`: under `KS4` the
  flipped rate lanes are the plain interleaved lanes.
* `flip6_frame`: flipping again after any change outside `KS` restores `KS`
  byte for byte.
-/

namespace MlDsaOpt44.Proofs.Blk

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem flipv_lt (t : Nat) : 2 ^ 256 - 1 - t < 2 ^ 256 := by
  have : 0 < 2 ^ 256 := by positivity
  omega

theorem word_flipW (M : ByteArray) {a b : Nat} (h : a = b ∨ a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (flipW M a) b = if a = b then 2 ^ 256 - 1 - word M a else word M b := by
  unfold flipW
  split
  · rename_i hab; subst hab; exact word_mstore _ _ _ (flipv_lt _)
  · exact word_mstore_disjoint _ _ (by omega)

theorem word_wb (M : ByteArray) (v : Nat) {a b : Nat} (h : a = b ∨ a + 32 ≤ b ∨ b + 32 ≤ a) :
    word (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (v % 2 ^ 256) 32) a) b =
      if a = b then v % 2 ^ 256 else word M b := by
  split
  · rename_i hab; subst hab; exact word_mstore _ _ _ (Nat.mod_lt _ (by positivity))
  · exact word_mstore_disjoint _ _ (by omega)

/-! ## Candidate stores -/

/-- Candidate word `k < 8` of one iteration, as stored by `candMem`. -/
def cw (k d0 d1 d2 : Nat) : Nat :=
  match k with
  | 0 => c0 d0 d1 d2
  | 1 => c1 d0 d1 d2
  | 2 => c2 d0 d1 d2
  | 3 => c3 d0 d1 d2
  | 4 => c4 d0 d1 d2
  | 5 => c5 d0 d1 d2
  | 6 => c6 d0 d1 d2
  | _ => c7 d0 d1 d2

theorem word_candMem (M : ByteArray) (abp d0 d1 d2 : Nat) {k : Nat} (hk : k < 8) :
    word (candMem M abp d0 d1 d2) (abp + 32 * k) = cw k d0 d1 d2 % 2 ^ 256 := by
  interval_cases k <;> simp (disch := omega) only [candMem, word_wb, if_pos, if_neg, cw]

theorem word_candMem_disjoint (M : ByteArray) (abp d0 d1 d2 : Nat) {a : Nat}
    (h : a + 32 ≤ abp ∨ abp + 256 ≤ a) : word (candMem M abp d0 d1 d2) a = word M a := by
  simp (disch := omega) only [candMem, word_wb, if_neg]

theorem frame_candMem (M : ByteArray) (abp d0 d1 d2 : Nat) :
    FrameExcept M (candMem M abp d0 d1 d2) [(abp, abp + 256)] := by
  intro a ha
  have ha' : a < abp ∨ abp + 256 ≤ a := ha (abp, abp + 256) (by simp)
  simp only [candMem]
  repeat rw [byteAt_writeBytes_of_not_mem (by rw [natToBytesPadded_size]; omega)]

/-! ## Lane flips -/

theorem word_flip6_high (M : ByteArray) {a : Nat} (ha : 672 ≤ a) : word (flip6 M) a = word M a := by
  simp (disch := omega) only [flip6, word_flipW, if_neg]

theorem word_flip6_cpl (M : ByteArray) {x : Nat} (hc : x ∈ complemented) :
    word (flip6 M) (32 * x) = 2 ^ 256 - 1 - word M (32 * x) := by
  have : x = 1 ∨ x = 2 ∨ x = 8 ∨ x = 12 ∨ x = 17 ∨ x = 20 := by simpa [complemented] using hc
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true, Nat.reduceMul]

theorem word_flip6_plain (M : ByteArray) {x : Nat} (hc : x ∉ complemented) :
    word (flip6 M) (32 * x) = word M (32 * x) := by
  have : x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 8 ∧ x ≠ 12 ∧ x ≠ 17 ∧ x ≠ 20 := by simpa [complemented] using hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := this
  simp (disch := omega) only [flip6, word_flipW, if_neg]

theorem laneOf_lt (S : Fips202.SpongeState) (x : Nat) : laneOf S x < 2 ^ 64 := (S[x]!).toNat_lt

/-- Under `KS4`, the flipped rate lanes are the plain interleaved lanes. -/
theorem ks_lane {m : ByteArray} {S : Nat → Fips202.SpongeState} (hKS : KS4 m S) {x : Nat}
    (hx : x < 21) : word (flip6 m) (32 * x) = il fun k => laneOf (S k) x := by
  have h := hKS x (by omega)
  simp only [KS, Nat.zero_add] at h
  by_cases hc : x ∈ complemented
  · rw [word_flip6_cpl m hc, h]
    simp only [cpl, hc, if_true]
    exact not_il fun k _ => laneOf_lt _ _
  · rw [word_flip6_plain m hc, h]
    simp only [cpl, hc, if_false]

/-! ## Restoring `KS` -/

theorem natToBytesPadded_word (m : ByteArray) (a : Nat) :
    Data.Bytes.natToBytesPadded (word m a) 32 = MachineState.readPadded m a 32 := by
  have hw : word m a = Data.Bytes.bytesToBigEndianNat (MachineState.readPadded m a 32) := by
    unfold word; rw [EvmProof.Bytes.readWord_toNat]; rfl
  have := EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat (MachineState.readPadded m a 32)
  rw [EvmProof.Memory.readPadded_size] at this
  rw [hw, this]

theorem byteAt_readPadded (m : ByteArray) (a : Nat) {i : Nat} (hi : i < 32) :
    byteAt (MachineState.readPadded m a 32) i = byteAt m (a + i) := by
  rw [byteAt_eq_getD, byteAt_eq_getD, EvmProof.Memory.readPadded_getElem?_getD, if_pos hi]

theorem flipW_restore {M m : ByteArray} {a : Nat} (hw : word M a = 2 ^ 256 - 1 - word m a)
    (b : Nat) : byteAt (flipW M a) b = if a ≤ b ∧ b < a + 32 then byteAt m b else byteAt M b := by
  unfold flipW
  have hlt := word_lt m a
  have hpos : 0 < 2 ^ 256 := by positivity
  rw [byteAt_writeBytes, natToBytesPadded_size, hw,
    show 2 ^ 256 - 1 - (2 ^ 256 - 1 - word m a) = word m a by omega, natToBytesPadded_word]
  split
  · rename_i h; rw [byteAt_readPadded _ _ (by omega), Nat.add_sub_cancel' h.1]
  · rfl

theorem byteAt_flipW_out (M : ByteArray) {a b : Nat} (h : b < a ∨ a + 32 ≤ b) :
    byteAt (flipW M a) b = byteAt M b :=
  byteAt_writeBytes_of_not_mem (by rw [natToBytesPadded_size]; exact h)

/-- Flipping back after changes away from `KS` restores the original memory there. -/
theorem flip6_frame {m Mf : ByteArray} {rs : List (Nat × Nat)} (hrs : Avoids rs 0 672)
    (hF : FrameExcept (flip6 m) Mf rs) : FrameExcept m (flip6 Mf) rs := by
  intro b hb
  have hw : ∀ a, a + 32 ≤ 672 → word Mf a = word (flip6 m) a := fun a ha =>
    hF.word (hrs.mono (by omega) ha)
  have h640 : word (flipW (flipW (flipW (flipW (flipW Mf 32) 64) 256) 384) 544) 640 =
      2 ^ 256 - 1 - word m 640 := by
    simp (disch := omega) only [word_flipW, if_neg]
    rw [hw 640 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  have h544 : word (flipW (flipW (flipW (flipW Mf 32) 64) 256) 384) 544 =
      2 ^ 256 - 1 - word m 544 := by
    simp (disch := omega) only [word_flipW, if_neg]
    rw [hw 544 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  have h384 : word (flipW (flipW (flipW Mf 32) 64) 256) 384 = 2 ^ 256 - 1 - word m 384 := by
    simp (disch := omega) only [word_flipW, if_neg]
    rw [hw 384 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  have h256 : word (flipW (flipW Mf 32) 64) 256 = 2 ^ 256 - 1 - word m 256 := by
    simp (disch := omega) only [word_flipW, if_neg]
    rw [hw 256 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  have h64 : word (flipW Mf 32) 64 = 2 ^ 256 - 1 - word m 64 := by
    simp (disch := omega) only [word_flipW, if_neg]
    rw [hw 64 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  have h32 : word Mf 32 = 2 ^ 256 - 1 - word m 32 := by
    rw [hw 32 (by omega)]
    simp (disch := omega) only [flip6, word_flipW, if_pos, if_neg, if_true]
  simp only [flip6]
  rw [flipW_restore h640, flipW_restore h544, flipW_restore h384, flipW_restore h256,
    flipW_restore h64, flipW_restore h32]
  split_ifs with c1 c2 c3 c4 c5 c6
  all_goals try rfl
  rw [hF b hb]
  simp only [flip6]
  rw [byteAt_flipW_out _ (by omega), byteAt_flipW_out _ (by omega), byteAt_flipW_out _ (by omega),
    byteAt_flipW_out _ (by omega), byteAt_flipW_out _ (by omega), byteAt_flipW_out _ (by omega)]

end MlDsaOpt44.Proofs.Blk
