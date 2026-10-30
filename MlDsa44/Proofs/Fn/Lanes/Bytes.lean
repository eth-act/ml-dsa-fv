import MlDsa44.Proofs.Infra
import YulEvmCompiler.BytesLemmas
/-!
# Byte-level helpers for the lane codecs

* `readLE64_toNat`: `Keccak.readLE64` as the little-endian value of 8 `byteAt`s;
  `readLE64_congr`: it only depends on those bytes.
* `writeLE64_pad_getElem`: the bytes of `writeLE64 .empty w ++ 24 zeros`.
* `beNat_add`, `word_div_eq_beNat8`: the top 8 bytes of a word.
* `byteAt_natToBytesPadded`: big-endian bytes of an MSTOREd word.
* `xorBlock_size`, `xorBlock_getElem!`: lanes of `Fips202.xorBlock`.
-/

namespace MlDsa44.Proofs.Lanes

open EvmSemantics
open EvmSemantics.EVM

theorem or_shl_eq_add {a k : Nat} (b : Nat) (h : a < 2 ^ k) : a ||| b <<< k = a + b * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]; omega

theorem shl_mod {b k : Nat} (hb : b < 256) (hk : k ≤ 56) :
    b <<< k % 18446744073709551616 = b <<< k := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  calc b * 2 ^ k < 256 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
    _ ≤ 256 * 2 ^ 56 := Nat.mul_le_mul_left _ this
    _ = 18446744073709551616 := by norm_num

theorem toNat_byte (m : ByteArray) (a : Nat) :
    (if h : a < m.size then m[a].toUInt64 else 0 : UInt64).toNat = byteAt m a := by
  unfold byteAt; split <;> simp

/-- `readLE64` is the little-endian value of the 8 bytes at `p` (zero past the end). -/
theorem readLE64_toNat (m : ByteArray) (p : Nat) : (Crypto.Keccak.readLE64 m p).toNat =
    byteAt m p + byteAt m (p + 1) * 256 + byteAt m (p + 2) * 65536 +
      byteAt m (p + 3) * 16777216 + byteAt m (p + 4) * 4294967296 +
      byteAt m (p + 5) * 1099511627776 + byteAt m (p + 6) * 281474976710656 +
      byteAt m (p + 7) * 72057594037927936 := by
  have h0 := Infra.byteAt_lt m p
  have h1 := Infra.byteAt_lt m (p + 1)
  have h2 := Infra.byteAt_lt m (p + 2)
  have h3 := Infra.byteAt_lt m (p + 3)
  have h4 := Infra.byteAt_lt m (p + 4)
  have h5 := Infra.byteAt_lt m (p + 5)
  have h6 := Infra.byteAt_lt m (p + 6)
  have h7 := Infra.byteAt_lt m (p + 7)
  simp only [Crypto.Keccak.readLE64, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl, UInt64.toNat_or, UInt64.toNat_shiftLeft, toNat_byte,
    Nat.reduceAdd, Nat.reduceMul, UInt64.reduceToNat, UInt64.reduceOfNat, Nat.reducePow,
    Nat.reduceMod, Nat.add_zero, Nat.zero_or]
  simp (disch := omega) only [shl_mod]
  simp (disch := omega) only [or_shl_eq_add, Nat.shiftLeft_zero]
  omega

theorem readLE64_congr {m m' : ByteArray} {p : Nat}
    (h : ∀ k, k < 8 → byteAt m' (p + k) = byteAt m (p + k)) :
    Crypto.Keccak.readLE64 m' p = Crypto.Keccak.readLE64 m p := by
  apply UInt64.toNat_inj.mp
  rw [readLE64_toNat, readLE64_toNat, h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  have := h 0 (by omega)
  simp only [Nat.add_zero] at this
  rw [this]

/-! ## Byte reversal (the `bswap64` sum) -/

theorem bswap_sum_eq (x : Nat) :
    ((List.range 8).map fun i => x / 256 ^ i % 256 * 256 ^ (7 - i)).sum =
      x % 256 * 72057594037927936 + x / 256 % 256 * 281474976710656 +
        x / 65536 % 256 * 1099511627776 + x / 16777216 % 256 * 4294967296 +
        x / 4294967296 % 256 * 16777216 + x / 1099511627776 % 256 * 65536 +
        x / 281474976710656 % 256 * 256 + x / 72057594037927936 % 256 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append, Nat.reducePow, Nat.reduceSub,
    Nat.div_one, Nat.mul_one]
  omega

/-- Byte reversal of a big-endian 8-byte value is its little-endian reading. -/
theorem bswap_sum_be (X b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256)
    (h7 : b7 < 256)
    (hX : X = b0 * 72057594037927936 + b1 * 281474976710656 + b2 * 1099511627776 +
      b3 * 4294967296 + b4 * 16777216 + b5 * 65536 + b6 * 256 + b7) :
    ((List.range 8).map fun i => X / 256 ^ i % 256 * 256 ^ (7 - i)).sum =
      b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 + b4 * 4294967296 + b5 * 1099511627776 +
        b6 * 281474976710656 + b7 * 72057594037927936 := by
  rw [bswap_sum_eq]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ : X % 256 = b7 ∧ X / 256 % 256 = b6 ∧
      X / 65536 % 256 = b5 ∧ X / 16777216 % 256 = b4 ∧ X / 4294967296 % 256 = b3 ∧
      X / 1099511627776 % 256 = b2 ∧ X / 281474976710656 % 256 = b1 ∧
      X / 72057594037927936 % 256 = b0 :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  simp only [e0, e1, e2, e3, e4, e5, e6, e7]
  clear e0 e1 e2 e3 e4 e5 e6 e7 hX
  omega

/-- Byte `i` of the MSTORE image of `bswap64 x << 192` (as `storeLE64` writes it). -/
theorem bswap_store_byte (x i : Nat) (hi : i < 32) :
    ((List.range 8).map fun k => x / 256 ^ k % 256 * 256 ^ (7 - k)).sum *
        6277101735386680763835789423207666416102355444464034512896 / 256 ^ (31 - i) % 256 =
      if i < 8 then x / 256 ^ i % 256 else 0 := by
  rw [bswap_sum_eq]
  have h0 := Nat.mod_lt x (show 256 > 0 by omega)
  have h1 := Nat.mod_lt (x / 256) (show 256 > 0 by omega)
  have h2 := Nat.mod_lt (x / 65536) (show 256 > 0 by omega)
  have h3 := Nat.mod_lt (x / 16777216) (show 256 > 0 by omega)
  have h4 := Nat.mod_lt (x / 4294967296) (show 256 > 0 by omega)
  have h5 := Nat.mod_lt (x / 1099511627776) (show 256 > 0 by omega)
  have h6 := Nat.mod_lt (x / 281474976710656) (show 256 > 0 by omega)
  have h7 := Nat.mod_lt (x / 72057594037927936) (show 256 > 0 by omega)
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceLT, ↓reduceIte,
    Nat.pow_zero, Nat.div_one] <;>
  · generalize x % 256 = d0 at *
    generalize x / 256 % 256 = d1 at *
    generalize x / 65536 % 256 = d2 at *
    generalize x / 16777216 % 256 = d3 at *
    generalize x / 4294967296 % 256 = d4 at *
    generalize x / 1099511627776 % 256 = d5 at *
    generalize x / 281474976710656 % 256 = d6 at *
    generalize x / 72057594037927936 % 256 = d7 at *
    omega

/-! ## Big-endian words -/

theorem beNat_add (m : ByteArray) (a w : Nat) :
    ∀ k, Infra.beNat m a (w + k) = Infra.beNat m a w * 256 ^ k + Infra.beNat m (a + w) k
  | 0 => by simp [Infra.beNat]
  | k + 1 => by
    rw [← Nat.add_assoc, Infra.beNat, beNat_add m a w k, Infra.beNat, Nat.pow_succ,
      Nat.add_assoc a w k, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem beNat_lt (m : ByteArray) (a : Nat) : ∀ k, Infra.beNat m a k < 256 ^ k
  | 0 => by simp [Infra.beNat]
  | k + 1 => by
    rw [Infra.beNat, Nat.pow_succ]
    have h1 := beNat_lt m a k
    have h2 := Infra.byteAt_lt m (a + k)
    generalize 256 ^ k = P at *
    have : (Infra.beNat m a k + 1) * 256 ≤ P * 256 := Nat.mul_le_mul_right _ h1
    omega

/-- The top 8 bytes of the word at `p`. -/
theorem word_div_eq_beNat8 (m : ByteArray) (p : Nat) :
    word m p / 2 ^ 192 = Infra.beNat m p 8 := by
  rw [Infra.word_eq_beNat, show (32 : Nat) = 8 + 24 from rfl, beNat_add,
    show (2 : Nat) ^ 192 = 256 ^ 24 by norm_num, Nat.add_comm,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (beNat_lt m (p + 8) 24),
    Nat.zero_add]

/-- Byte `i` of a 32-byte big-endian MSTORE image. -/
theorem byteAt_natToBytesPadded (v i : Nat) (hi : i < 32) :
    byteAt (Data.Bytes.natToBytesPadded v 32) i = v / 256 ^ (31 - i) % 256 := by
  rw [Infra.byteAt_eq_getD, YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  simp

/-! ## `writeLE64` -/

/-- The 32-byte image stored by `storeLE64`: little-endian bytes of `x`, then zeros. -/
theorem writeLE64_pad_eq (x : Nat) (hx : x < 2 ^ 64) :
    Crypto.Keccak.writeLE64 .empty (UInt64.ofNat x) ++ ByteArray.mk (Array.replicate 24 0) =
      ByteArray.mk ((List.range 32).map
        fun i => if i < 8 then UInt8.ofNat (x / 256 ^ i) else 0).toArray := by
  simp only [Crypto.Keccak.writeLE64, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl, Nat.reduceAdd, Nat.reduceMul]
  apply ByteArray.ext
  simp [ByteArray.push, List.range_succ]
  have hand : ∀ n : Nat, n &&& 255 = n % 256 := fun n => Nat.and_two_pow_sub_one_eq_mod n 8
  have hx' : x % 18446744073709551616 = x := Nat.mod_eq_of_lt hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt8.toNat_and, UInt64.toNat_shiftRight, hx', hand, Nat.shiftRight_eq_div_pow]

theorem writeLE64_pad_size (x : Nat) (hx : x < 2 ^ 64) :
    (Crypto.Keccak.writeLE64 .empty (UInt64.ofNat x) ++
      ByteArray.mk (Array.replicate 24 0)).size = 32 := by
  rw [writeLE64_pad_eq x hx]; simp [ByteArray.size]

theorem writeLE64_pad_getElem (x : Nat) (hx : x < 2 ^ 64) (i : Nat) (hi : i < 32) :
    (Crypto.Keccak.writeLE64 .empty (UInt64.ofNat x) ++
        ByteArray.mk (Array.replicate 24 0))[i]!.toNat =
      if i < 8 then x / 256 ^ i % 256 else 0 := by
  have hi' := hi
  rw [← writeLE64_pad_size x hx] at hi'
  rw [getElem!_pos _ i hi']
  simp only [writeLE64_pad_eq x hx, ByteArray.getElem_eq_data_getElem, List.getElem_toArray,
    List.getElem_map, List.getElem_range]
  split <;> simp

/-! ## `Fips202.xorBlock` -/

theorem xorBlock_fold_size (f : Nat → UInt64) (A : Array UInt64) (n : Nat) :
    ((List.range n).foldl (fun st j => st.set! j (st[j]! ^^^ f j)) A).size = A.size := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.set!,
      Array.size_setIfInBounds, ih]

theorem xorBlock_fold_getElem (f : Nat → UInt64) (A : Array UInt64) :
    ∀ n, n ≤ A.size → ∀ i,
      ((List.range n).foldl (fun st j => st.set! j (st[j]! ^^^ f j)) A)[i]! =
        if i < n then A[i]! ^^^ f i else A[i]!
  | 0, _, i => by simp
  | n + 1, hn, i => by
    have ih := xorBlock_fold_getElem f A n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.set!,
      getElem!_def, Array.getElem?_setIfInBounds, xorBlock_fold_size]
    by_cases hin : n = i
    · subst hin
      rw [if_pos rfl, if_pos (by omega), ih, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg hin, ← getElem!_def, ih]
      by_cases h : i < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

end MlDsa44.Proofs.Lanes
