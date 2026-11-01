import MlDsaOpt44.Fn.Kf4.Model
/-!
# Bit-interleaved words

`il u` puts bit `b` of slot `k` at bit `4b + k` (`Layout.lean`). Here:

* `testBit_il`: the bits of `il u`;
* `W f`: the interleaved word of four `UInt64` slots, and the homomorphism
  lemmas `W_xor`, `W_and`, `W_or`, `W_not`, `W_rot`: every word operation of
  `Ops256` acts slot-wise as the corresponding `Ops64` operation.
-/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open MlDsaOptCommon

/-! ## `spread` and `il` by recursion -/

/-- `spread` by recursion on the number of bits. -/
def spreadR : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => v % 2 + 16 * spreadR n (v / 2)

theorem sum_map_mul16 (l : List Nat) (f : Nat → Nat) :
    (l.map fun b => 16 * f b).sum = 16 * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem spread_sum (n v : Nat) :
    ((List.range n).map fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)).sum = spreadR n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have h : ((fun b => v / 2 ^ b % 2 * 2 ^ (4 * b)) ∘ Nat.succ) =
        fun b => 16 * (v / 2 / 2 ^ b % 2 * 2 ^ (4 * b)) := by
      funext b
      simp only [Function.comp, Nat.div_div_eq_div_mul, Nat.succ_eq_add_one]
      rw [show 2 * 2 ^ b = 2 ^ (b + 1) by rw [Nat.pow_succ, Nat.mul_comm],
        show 4 * (b + 1) = 4 * b + 4 by ring, Nat.pow_add]
      ring
    rw [h, sum_map_mul16, ih]
    simp [spreadR]

/-- Interleaving by recursion: one nibble (one bit of each slot) at a time. -/
def ilR : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, u => u 0 % 2 + 2 * (u 1 % 2) + 4 * (u 2 % 2) + 8 * (u 3 % 2) +
      16 * ilR n (fun k => u k / 2)

theorem ilR_eq (n : Nat) (u : Nat → Nat) :
    spreadR n (u 0) + 2 * spreadR n (u 1) + 4 * spreadR n (u 2) + 8 * spreadR n (u 3) =
      ilR n u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    simp only [spreadR, ilR]
    rw [← ih]
    ring

theorem il_eq (u : Nat → Nat) : il u = ilR 64 u := by
  unfold il spread
  rw [spread_sum, spread_sum, spread_sum, spread_sum, ilR_eq]

theorem ilR_lt (n : Nat) (u : Nat → Nat) : ilR n u < 2 ^ (4 * n) := by
  induction n generalizing u with
  | zero => simp [ilR]
  | succ n ih =>
    have := ih (fun k => u k / 2)
    have h0 := Nat.mod_lt (u 0) (show 2 > 0 by omega)
    have h1 := Nat.mod_lt (u 1) (show 2 > 0 by omega)
    have h2 := Nat.mod_lt (u 2) (show 2 > 0 by omega)
    have h3 := Nat.mod_lt (u 3) (show 2 > 0 by omega)
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, Nat.pow_add]
    simp only [ilR]
    omega

theorem il_lt (u : Nat → Nat) : il u < 2 ^ 256 := by
  rw [il_eq]; exact ilR_lt 64 u

theorem testBit_nibble (b0 b1 b2 b3 : Nat) (h0 : b0 < 2) (h1 : b1 < 2) (h2 : b2 < 2)
    (h3 : b3 < 2) (j : Nat) (hj : j < 4) :
    (b0 + 2 * b1 + 4 * b2 + 8 * b3).testBit j =
      (if j = 0 then b0 else if j = 1 then b1 else if j = 2 then b2 else b3).testBit 0 := by
  interval_cases b0 <;> interval_cases b1 <;> interval_cases b2 <;> interval_cases b3 <;>
    interval_cases j <;> decide

theorem testBit_ilR (n : Nat) (u : Nat → Nat) (j : Nat) :
    (ilR n u).testBit j = (decide (j < 4 * n) && (u (j % 4)).testBit (j / 4)) := by
  induction n generalizing u j with
  | zero => simp [ilR]
  | succ n ih =>
    simp only [ilR]
    have h0 := Nat.mod_lt (u 0) (show 2 > 0 by omega)
    have h1 := Nat.mod_lt (u 1) (show 2 > 0 by omega)
    have h2 := Nat.mod_lt (u 2) (show 2 > 0 by omega)
    have h3 := Nat.mod_lt (u 3) (show 2 > 0 by omega)
    have hlow : u 0 % 2 + 2 * (u 1 % 2) + 4 * (u 2 % 2) + 8 * (u 3 % 2) < 2 ^ 4 := by omega
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlow]
    split
    · rename_i hj
      rw [testBit_nibble _ _ _ _ h0 h1 h2 h3 j hj]
      have hj4 : j / 4 = 0 := by omega
      have hjm : j % 4 = j := by omega
      rw [hj4, hjm, show decide (j < 4 * (n + 1)) = true by simp; omega, Bool.true_and]
      simp only [Nat.testBit_zero]
      interval_cases j <;> simp
    · rename_i hj
      rw [ih, Nat.testBit_div_two]
      have hm : (j - 4) % 4 = j % 4 := by omega
      have hd : (j - 4) / 4 + 1 = j / 4 := by omega
      rw [hm, hd]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem testBit_il (u : Nat → Nat) (j : Nat) :
    (il u).testBit j = (decide (j < 256) && (u (j % 4)).testBit (j / 4)) := by
  rw [il_eq, testBit_ilR]

theorem il_congr {u v : Nat → Nat} (h : ∀ k, k < 4 → u k = v k) : il u = il v := by
  unfold il
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-! ## Bitwise operations act slot-wise -/

theorem il_xor (u v : Nat → Nat) : il u ^^^ il v = il fun k => u k ^^^ v k := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_il]
  cases decide (j < 256) <;> simp

theorem il_and (u v : Nat → Nat) : il u &&& il v = il fun k => u k &&& v k := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, testBit_il]
  cases decide (j < 256) <;> simp

theorem il_or (u v : Nat → Nat) : il u ||| il v = il fun k => u k ||| v k := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_or, testBit_il]
  cases decide (j < 256) <;> simp

theorem il_not (u : Nat → Nat) (hu : ∀ k, k < 4 → u k < 2 ^ 64) :
    2 ^ 256 - 1 - il u = il fun k => 2 ^ 64 - 1 - u k := by
  apply Nat.eq_of_testBit_eq; intro j
  have hl := il_lt u
  rw [show 2 ^ 256 - 1 - il u = 2 ^ 256 - (il u + 1) by omega, Nat.testBit_two_pow_sub_succ hl,
    testBit_il, testBit_il]
  by_cases hj : j < 256
  · have hk := hu (j % 4) (by omega)
    rw [show 2 ^ 64 - 1 - u (j % 4) = 2 ^ 64 - (u (j % 4) + 1) by omega,
      Nat.testBit_two_pow_sub_succ hk]
    simp only [hj, decide_true, Bool.true_and, show j / 4 < 64 by omega]
  · simp [hj]

/-- The rotation `DUP1 PUSH 4n SHL SWAP1 PUSH (256−4n) SHR OR` of an interleaved word. -/
theorem il_rot (u : Nat → Nat) (hu : ∀ k, k < 4 → u k < 2 ^ 64) {n : Nat} (h0 : 0 < n)
    (h64 : n < 64) :
    (il u >>> (256 - 4 * n) ||| il u <<< (4 * n)) % 2 ^ 256 =
      il fun k => u k <<< n % 2 ^ 64 ||| u k >>> (64 - n) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_il, testBit_il, testBit_il]
  by_cases hj : j < 256
  · have hk := hu (j % 4) (by omega)
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hjn : j ≥ 4 * n
    · have e1 : (j - 4 * n) % 4 = j % 4 := by omega
      have e2 : (j - 4 * n) / 4 = j / 4 - n := by omega
      have e3 : (u (j % 4)).testBit (64 - n + j / 4) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) (by omega)))
      simp only [hj, decide_true, Bool.true_and, hjn, e1, e2, e3,
        show ¬ (256 - 4 * n + j < 256) by omega, decide_false, Bool.false_and, Bool.false_or,
        Bool.or_false, show j / 4 < 64 by omega, show j / 4 ≥ n by omega, show j - 4 * n < 256 by omega]
    · have e1 : (256 - 4 * n + j) % 4 = j % 4 := by omega
      have e2 : (256 - 4 * n + j) / 4 = 64 - n + j / 4 := by omega
      simp only [hj, decide_true, Bool.true_and, hjn, e1, e2, decide_false, Bool.false_and,
        Bool.or_false, Bool.false_or, Bool.and_false, show 256 - 4 * n + j < 256 by omega,
        show ¬ (j / 4 ≥ n) by omega]
  · simp [hj]

/-! ## Four `UInt64` slots as one interleaved word -/

/-- The interleaved word of the four slots `f 0, …, f 3`. -/
def W (f : Nat → UInt64) : UInt256 := UInt256.ofNat (il fun k => (f k).toNat)

theorem W_congr {f g : Nat → UInt64} (h : ∀ k, k < 4 → f k = g k) : W f = W g := by
  unfold W; rw [il_congr (fun k hk => by rw [h k hk])]

theorem W_xor (f g : Nat → UInt64) : UInt256.xor (W f) (W g) = W fun k => f k ^^^ g k := by
  unfold W; rw [ofNat_xor, il_xor]; simp only [UInt64.toNat_xor]

theorem W_and (f g : Nat → UInt64) : UInt256.land (W f) (W g) = W fun k => f k &&& g k := by
  unfold W; rw [ofNat_land, il_and]; simp only [UInt64.toNat_and]

theorem W_or (f g : Nat → UInt64) : UInt256.lor (W f) (W g) = W fun k => f k ||| g k := by
  unfold W; rw [ofNat_lor, il_or]; simp only [UInt64.toNat_or]

theorem W_not (f : Nat → UInt64) : UInt256.lnot (W f) = W fun k => ~~~ f k := by
  unfold W
  rw [ofNat_not, Nat.mod_eq_of_lt (il_lt _), il_not _ (fun k _ => (f k).toNat_lt)]
  simp only [UInt64.toNat_not, UInt64.size]
  rfl

theorem toNat_rotl64 (x : UInt64) {n : Nat} (h0 : 0 < n) (h64 : n < 64) :
    (EvmSemantics.Crypto.Keccak.rotl64 x n).toNat = x.toNat <<< n % 2 ^ 64 ||| x.toNat >>> (64 - n) := by
  unfold EvmSemantics.Crypto.Keccak.rotl64
  rw [if_neg (by omega), UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
  have hn : (UInt64.ofNat n).toNat % 64 = n := by rw [UInt64.toNat_ofNat']; omega
  have hn' : (UInt64.ofNat (64 - n)).toNat % 64 = 64 - n := by rw [UInt64.toNat_ofNat']; omega
  rw [hn, hn']

theorem W_rot (f : Nat → UInt64) {n : Nat} (h0 : 0 < n) (h64 : n < 64) :
    rot256 (W f) n = W fun k => EvmSemantics.Crypto.Keccak.rotl64 (f k) n := by
  unfold rot256 W
  rw [ofNat_shr _ (by omega), ofNat_shl _ (by omega), ofNat_lor, Nat.mod_eq_of_lt (il_lt _),
    ← ofNat_mod, il_rot _ (fun k _ => (f k).toNat_lt) h0 h64]
  simp only [toNat_rotl64 _ h0 h64]

/-! ## The model pieces commute with `W` -/

@[simp] theorem Ops256_xor (a b : UInt256) : Ops256.xor a b = UInt256.xor a b := rfl
@[simp] theorem Ops256_and (a b : UInt256) : Ops256.and a b = UInt256.land a b := rfl
@[simp] theorem Ops256_or (a b : UInt256) : Ops256.or a b = UInt256.lor a b := rfl
@[simp] theorem Ops256_not (a : UInt256) : Ops256.not a = UInt256.lnot a := rfl
@[simp] theorem Ops256_rot (a : UInt256) (n : Nat) : Ops256.rot a n = rot256 a n := rfl
@[simp] theorem Ops64_xor (a b : UInt64) : Ops64.xor a b = a ^^^ b := rfl
@[simp] theorem Ops64_and (a b : UInt64) : Ops64.and a b = a &&& b := rfl
@[simp] theorem Ops64_or (a b : UInt64) : Ops64.or a b = a ||| b := rfl
@[simp] theorem Ops64_not (a : UInt64) : Ops64.not a = ~~~ a := rfl
@[simp] theorem Ops64_rot (a : UInt64) (n : Nat) :
    Ops64.rot a n = EvmSemantics.Crypto.Keccak.rotl64 a n := rfl

theorem colC_W (f0 f1 f2 f3 f4 : Nat → UInt64) :
    colC Ops256 (W f0) (W f1) (W f2) (W f3) (W f4) =
      W fun k => colC Ops64 (f0 k) (f1 k) (f2 k) (f3 k) (f4 k) := by
  simp only [colC, Ops256_xor, Ops64_xor, W_xor]

theorem dL_W (f g : Nat → UInt64) : dL Ops256 (W f) (W g) = W fun k => dL Ops64 (f k) (g k) := by
  simp only [dL, Ops256_xor, Ops64_xor, Ops256_rot, Ops64_rot, W_xor, W_rot _ (show 0 < 1 by omega) (show 1 < 64 by omega)]

theorem dR_W (f g : Nat → UInt64) : dR Ops256 (W f) (W g) = W fun k => dR Ops64 (f k) (g k) := by
  simp only [dR, Ops256_xor, Ops64_xor, Ops256_rot, Ops64_rot, W_xor, W_rot _ (show 0 < 1 by omega) (show 1 < 64 by omega)]

theorem bv_W (f g : Nat → UInt64) {r : Nat} (h0 : 0 < r) (h64 : r < 64) :
    bv Ops256 (W f) (W g) r = W fun k => bv Ops64 (f k) (g k) r := by
  simp only [bv, Ops256_xor, Ops64_xor, Ops256_rot, Ops64_rot, W_xor, W_rot _ h0 h64]

theorem bv0_W (f g : Nat → UInt64) : bv0 Ops256 (W f) (W g) = W fun k => bv0 Ops64 (f k) (g k) := by
  simp only [bv0, Ops256_xor, Ops64_xor, W_xor]

end MlDsaOpt44.Proofs.Kf4
