import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Math.Sponge
set_option warningAsError true
/-!
# Pure facts used by `computeRow_call`

* the seed `readPadded m SEEDA 34` is `ρ ‖ j ‖ i`;
* `RejNTTPoly` reads exactly the six squeezed SHAKE128 blocks;
* `t1[i]` coefficients as 10-bit fields of the calldata;
* the `addmod`/`mulmod` loops agree with `addNTT`/`multiplyNTT` on `Int`.
-/

namespace MlDsa44.Proofs.Row

open EvmSemantics
open EvmSemantics.EVM

/-! ## Bytes -/

theorem byteAt_eq_data (x : ByteArray) (k : Nat) : byteAt x k = (x.data[k]?.getD 0).toNat := by
  unfold byteAt
  split
  · rename_i h
    rw [Array.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rename_i h
    rw [Array.getElem?_eq_none (by simpa using h)]
    rfl

theorem byteArray_eq_of_byteAt {x y : ByteArray} (hs : x.size = y.size)
    (h : ∀ k, k < x.size → byteAt x k = byteAt y k) : x = y := by
  apply ByteArray.ext
  apply Array.ext (by simpa using hs)
  intro k h1 h2
  have := h k (by simpa using h1)
  rw [byteAt_eq_data, byteAt_eq_data, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2] at this
  exact UInt8.toNat_inj.mp this

theorem nat_min_eq (x y : Nat) : Nat.min x y = min x y := rfl

theorem size_readPadded (m : ByteArray) (a n : Nat) :
    (MachineState.readPadded m a n).size = n := by
  unfold MachineState.readPadded
  simp only [nat_min_eq, ByteArray.size_append, ByteArray.size_extract]
  change _ + (Array.replicate _ _).size = n
  simp only [Array.size_replicate]
  omega

theorem byteAt_readPadded (m : ByteArray) (a n k : Nat) (hk : k < n) :
    byteAt (MachineState.readPadded m a n) k = byteAt m (a + k) := by
  unfold MachineState.readPadded
  simp only [nat_min_eq]
  rw [byteAt_eq_data, byteAt_eq_data, ByteArray.data_append, ByteArray.data_extract]
  simp only [Array.getElem?_append, Array.size_extract, Array.getElem?_extract,
    ByteArray.size_data]
  rw [Array.getElem?_replicate]
  by_cases h : a + k < m.size
  · rw [if_pos (by omega), if_pos (by omega), show min a m.size + k = a + k by omega]
  · rw [if_neg (by omega), if_pos (by omega),
      Array.getElem?_eq_none (by simpa using (show m.size ≤ a + k by omega))]
    rfl

/-- The SHAKE128 input of `RejNTTPoly`: `ρ ‖ j ‖ i`. -/
theorem readPadded_seed {M rho : ByteArray} {i j : Nat} (hrs : rho.size = 32)
    (hrho : BytesAt M SEEDA rho) (hj : byteAt M (SEEDA + 32) = j)
    (hi : byteAt M (SEEDA + 33) = i) (hj4 : j < 256) (hi4 : i < 256) :
    MachineState.readPadded M SEEDA 34 =
      rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i] := by
  have hsz : (ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i]).size = 2 := rfl
  apply byteArray_eq_of_byteAt (by rw [size_readPadded, ByteArray.size_append, hrs, hsz])
  intro k hk
  rw [size_readPadded] at hk
  rw [byteAt_readPadded _ _ _ _ hk, byteAt_eq_data (rho ++ _), ByteArray.data_append,
    Array.getElem?_append]
  by_cases hk32 : k < 32
  · rw [if_pos (by simpa [hrs] using hk32), hrho k (by omega),
      Array.getElem?_eq_getElem (by simpa [hrs] using hk32)]
    simp [ByteArray.getElem_eq_getElem_data, hrs, hk32]
  · rw [if_neg (by simpa [hrs] using hk32)]
    simp only [ByteArray.size_data, hrs]
    have : k = 32 ∨ k = 33 := by omega
    rcases this with rfl | rfl
    · simp [hj, Nat.mod_eq_of_lt hj4]
    · simp [hi, Nat.mod_eq_of_lt hi4]

/-- `RejNTTPoly(x)` reads exactly six squeezed SHAKE128 blocks. -/
theorem rejNTTPoly_eq_squeeze (x : ByteArray) :
    Fips204.rejNTTPoly x =
      Fips204.rejNTTPolyOf
        (Fips202.squeeze 168 (Fips202.absorb 168 (Fips202.pad 168 0x1F x)) 6) := by
  unfold Fips204.rejNTTPoly Fips204.G Fips202.shake128
  rw [← Math.squeeze_extract_shake 168 x Fips204.rejNTTPolyLimit 6 (Or.inr rfl)
    (by decide)]
  congr 1
  conv_rhs => rw [← ByteArray.extract_zero_size (b := Fips202.squeeze _ _ _)]
  rw [Math.squeeze_size_of_rate _ _ _ (Or.inr rfl)]
  rfl

theorem size_squeeze6 (st : Fips202.SpongeState) :
    (Fips202.squeeze 168 st 6).size = Fips204.rejNTTPolyLimit :=
  Math.squeeze_size_of_rate _ _ _ (Or.inr rfl)

/-- `MSTORE8` of `v` at `a`. -/
theorem byteAt_mstore8_self (m : ByteArray) (a v : Nat) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[UInt8.ofNat v]) a) a = v % 256 := by
  have hsize : (ByteArray.mk #[UInt8.ofNat v]).size = 1 := rfl
  rw [Infra.byteAt_writeBytes, if_pos (by omega), Nat.sub_self, byteAt, dif_pos (by omega)]
  change (UInt8.ofNat v).toNat = v % 256
  simp

theorem byteAt_mstore8_other (m : ByteArray) {a b : Nat} (v : Nat) (h : b ≠ a) :
    byteAt (MachineState.writeBytes m (ByteArray.mk #[UInt8.ofNat v]) a) b = byteAt m b :=
  Infra.byteAt_writeBytes_of_not_mem (by
    have hsize : (ByteArray.mk #[UInt8.ofNat v]).size = 1 := rfl
    omega)

theorem frame_mstore8 (m : ByteArray) (a v : Nat) :
    FrameExcept m (MachineState.writeBytes m (ByteArray.mk #[UInt8.ofNat v]) a) [(a, a + 1)] :=
  Infra.FrameExcept.writeBytes m _ a

/-! ## `t1` -/

theorem bitsToInteger_lt (v : ByteArray) (s : Nat) : ∀ c, Fips204.bitsToInteger v s c < 2 ^ c
  | 0 => by simp [Fips204.bitsToInteger]
  | c + 1 => by
    have ih := bitsToInteger_lt v s c
    unfold Fips204.bitsToInteger at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    have hb : Fips204.bit v (s + c) ≤ 1 := by
      unfold Fips204.bit; have := Nat.mod_lt (v[(s + c) / 8]!.toNat / 2 ^ ((s + c) % 8)) (by decide : 0 < 2); omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ]
    have : Fips204.bit v (s + c) * 2 ^ c ≤ 2 ^ c := by
      calc _ ≤ 1 * 2 ^ c := Nat.mul_le_mul_right _ hb
        _ = 2 ^ c := Nat.one_mul _
    omega

theorem bitlen_facts : Fips204.bitlen (Fips204.q - 1) - Fips204.d = 10 ∧
    Fips204.bitlen 1023 = 10 := by
  decide

/-- The coefficients of `t1[i] · 2^d` as 10-bit calldata fields. -/
theorem t1_scaled (cd : ByteArray) {i : Nat} (hi : i < 4) :
    ((Fips204.pkDecode (cd.extract 0 1312)).2[i]!).map (· * 2 ^ Fips204.d) =
      (Array.range 256).map fun t =>
        ((Fips204.bitsToInteger (cd.extract (32 + 320 * i) (32 + 320 * i + 320)) (t * 10) 10 *
          2 ^ 13 : Nat) : Int) := by
  obtain ⟨h2, h1⟩ := bitlen_facts
  have hx : (cd.extract 0 1312).extract (32 + 32 * 10 * i) (32 + 32 * 10 * (i + 1)) =
      cd.extract (32 + 320 * i) (32 + 320 * i + 320) := by
    rw [ByteArray.extract_extract]
    congr 1 <;> omega
  simp only [Fips204.pkDecode, h2]
  rw [getElem!_pos _ i (by simp [Fips204.k]; omega)]
  simp only [Array.getElem_map, Array.getElem_range, Fips204.simpleBitUnpack, hx,
    Array.map_map]
  apply Array.ext (by simp)
  intro t _ _
  simp [Fips204.d, h1]

theorem bits10_scaled_lt (v : ByteArray) (t : Nat) :
    Fips204.bitsToInteger v (t * 10) 10 * 2 ^ 13 < Fips204.q := by
  have := bitsToInteger_lt v (t * 10) 10
  unfold Fips204.q; omega

/-! ## Pointwise arithmetic -/

theorem getElem!_range_map {α : Type} [Inhabited α] (f : Nat → α) {t : Nat} (ht : t < 256) :
    ((Array.range 256).map f)[t]! = f t := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

theorem acc_step (x y z : Nat) (a b : Int) (hy : (y : Int) = a)
    (hz : (z : Int) = b) :
    (((x + y * z % Fips204.q) % Fips204.q : Nat) : Int) =
      ((x : Int) + a * b % (Fips204.q : Int)) % (Fips204.q : Int) := by
  subst hy hz
  push_cast
  rfl

theorem sub_step (x y z : Nat) :
    (((x + (Fips204.q - y * z % Fips204.q)) % Fips204.q : Nat) : Int) =
      ((x : Int) - (y : Int) * (z : Int) % (Fips204.q : Int)) % (Fips204.q : Int) := by
  have hr : y * z % Fips204.q < Fips204.q := Nat.mod_lt _ (by unfold Fips204.q; omega)
  rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub hr.le]
  have : ((y : Int) * (z : Int)) % (Fips204.q : Int) = ((y * z % Fips204.q : Nat) : Int) := by
    push_cast; rfl
  rw [this]
  generalize (y * z % Fips204.q : Nat) = r at hr ⊢
  rw [show (x : Int) + ((Fips204.q : Int) - r) = ((x : Int) - r) + (Fips204.q : Int) by ring,
    Int.add_emod_right]

end MlDsa44.Proofs.Row
