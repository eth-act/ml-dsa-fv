import MlDsa44.Spec.Fips204
/-!
# Sponge squeezing facts

Sizes of squeezed output and prefix-stability of `Fips202.squeeze`: squeezing
more blocks than needed and truncating gives the same bytes.
-/

open EvmSemantics.Crypto

namespace MlDsa44.Proofs.Math

theorem foldl_push_size {α : Type} (l : List α) (g : α → UInt8) (acc : ByteArray) :
    (l.foldl (fun b a => b.push (g a)) acc).size = acc.size + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem writeLE64_size (acc : ByteArray) (w : UInt64) : (Keccak.writeLE64 acc w).size = acc.size + 8 := by
  simp [Keccak.writeLE64, foldl_push_size]

theorem stateBytes_size (rate : Nat) (st : Fips202.SpongeState) :
    (Fips202.stateBytes rate st).size = rate / 8 * 8 := by
  unfold Fips202.stateBytes
  suffices ∀ (l : List Nat) (acc : ByteArray), (l.foldl (fun out j => Keccak.writeLE64 out st[j]!) acc).size = acc.size + 8 * l.length by
    simp [this]; omega
  intro l; induction l with
  | nil => simp
  | cons x xs ih => intro acc; simp [ih, writeLE64_size]; omega

theorem squeeze_size' (rate : Nat) (st : Fips202.SpongeState) (blocks : Nat) :
    (Fips202.squeeze rate st blocks).size = blocks * (rate / 8 * 8) := by
  induction blocks generalizing st with
  | zero => simp [Fips202.squeeze]
  | succ n ih => simp [Fips202.squeeze, ih, stateBytes_size, Nat.succ_mul]; omega

theorem squeeze_add (rate : Nat) (st : Fips202.SpongeState) (a b : Nat) :
    ∃ st', Fips202.squeeze rate st (a + b) = Fips202.squeeze rate st a ++ Fips202.squeeze rate st' b := by
  induction a generalizing st with
  | zero => exact ⟨st, by simp [Fips202.squeeze]⟩
  | succ n ih =>
    obtain ⟨st', h⟩ := ih (Keccak.permute st)
    refine ⟨st', ?_⟩
    rw [Nat.add_right_comm]
    simp only [Fips202.squeeze, h, ByteArray.append_assoc]

theorem squeeze_extract (rate : Nat) (st : Fips202.SpongeState) (a b n : Nat) (hab : a ≤ b)
    (hn : n ≤ a * (rate / 8 * 8)) :
    (Fips202.squeeze rate st b).extract 0 n = (Fips202.squeeze rate st a).extract 0 n := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨st', h⟩ := squeeze_add rate st a c
  rw [h, ByteArray.extract_append, squeeze_size']
  have : n - a * (rate / 8 * 8) = 0 := by omega
  simp [this]

theorem squeeze_size_of_rate (rate : Nat) (st : Fips202.SpongeState) (blocks : Nat)
    (hrate : rate = 136 ∨ rate = 168) :
    (Fips202.squeeze rate st blocks).size = blocks * rate := by
  rw [squeeze_size']
  rcases hrate with rfl | rfl <;> rfl

theorem squeeze_extract_shake (rate : Nat) (msg : ByteArray) (n blocks : Nat)
    (hrate : rate = 136 ∨ rate = 168) (hn : n ≤ blocks * rate) :
    (Fips202.squeeze rate (Fips202.absorb rate (Fips202.pad rate 0x1F msg)) blocks).extract 0 n =
      Fips202.shake rate msg n := by
  have h8 : rate / 8 * 8 = rate := by rcases hrate with rfl | rfl <;> rfl
  have hb : n ≤ (n + rate - 1) / rate * rate := by rcases hrate with rfl | rfl <;> omega
  unfold Fips202.shake
  rw [squeeze_extract rate _ (min blocks ((n + rate - 1) / rate)) blocks n (Nat.min_le_left _ _)
      (by rw [h8]; rcases Nat.le_total blocks ((n + rate - 1) / rate) with h | h
          · rw [Nat.min_eq_left h]; exact hn
          · rw [Nat.min_eq_right h]; exact hb),
    squeeze_extract rate _ (min blocks ((n + rate - 1) / rate)) ((n + rate - 1) / rate) n
      (Nat.min_le_right _ _)
      (by rw [h8]; rcases Nat.le_total blocks ((n + rate - 1) / rate) with h | h
          · rw [Nat.min_eq_left h]; exact hn
          · rw [Nat.min_eq_right h]; exact hb)]

end MlDsa44.Proofs.Math
