import MlDsaOpt44.Math.SpongeBits
import MlDsa44.Proofs.Math.Sponge
set_option warningAsError true
/-!
# Byte-level facts about the FIPS 202 sponge driver

Lanes of `xorBlock`, bytes of `pad`, `stateBytes`, `squeeze`, and the
`absorb` fold block by block (adapted from the reference proof's
`Math/Shake/Bytes.lean` and `Fn/Lanes/Bytes.lean`, restated over the
artifact-independent `byteAt` / `le64`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44

theorem le64_eq (b : ByteArray) (a : Nat) : le64 b a =
    byteAt b a + byteAt b (a + 1) * 256 + byteAt b (a + 2) * 65536 +
      byteAt b (a + 3) * 16777216 + byteAt b (a + 4) * 4294967296 +
      byteAt b (a + 5) * 1099511627776 + byteAt b (a + 6) * 281474976710656 +
      byteAt b (a + 7) * 72057594037927936 := by
  unfold le64
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  norm_num

theorem le64_lt (b : ByteArray) (a : Nat) : le64 b a < 2 ^ 64 := by
  have h0 := byteAt_lt b a
  have h1 := byteAt_lt b (a + 1)
  have h2 := byteAt_lt b (a + 2)
  have h3 := byteAt_lt b (a + 3)
  have h4 := byteAt_lt b (a + 4)
  have h5 := byteAt_lt b (a + 5)
  have h6 := byteAt_lt b (a + 6)
  have h7 := byteAt_lt b (a + 7)
  rw [le64_eq]; omega

theorem le64_congr {b b' : ByteArray} {a a' : Nat}
    (h : ∀ k, k < 8 → byteAt b' (a' + k) = byteAt b (a + k)) : le64 b' a' = le64 b a := by
  rw [le64_eq, le64_eq, show a' = a' + 0 from rfl, h 0 (by omega), h 1 (by omega), h 2 (by omega),
    h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  rfl

private theorem or_shl_eq_add {a k : Nat} (b : Nat) (h : a < 2 ^ k) : a ||| b <<< k = a + b * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]; omega

private theorem shl_mod {b k : Nat} (hb : b < 256) (hk : k ≤ 56) :
    b <<< k % 18446744073709551616 = b <<< k := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  calc b * 2 ^ k < 256 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
    _ ≤ 256 * 2 ^ 56 := Nat.mul_le_mul_left _ this
    _ = 18446744073709551616 := by norm_num

private theorem toNat_byte (m : ByteArray) (a : Nat) :
    (if h : a < m.size then m[a].toUInt64 else 0 : UInt64).toNat = byteAt m a := by
  unfold byteAt; split <;> simp

/-- `readLE64` is `le64`. -/
theorem readLE64_toNat (m : ByteArray) (p : Nat) : (Keccak.readLE64 m p).toNat = le64 m p := by
  have h0 := byteAt_lt m p
  have h1 := byteAt_lt m (p + 1)
  have h2 := byteAt_lt m (p + 2)
  have h3 := byteAt_lt m (p + 3)
  have h4 := byteAt_lt m (p + 4)
  have h5 := byteAt_lt m (p + 5)
  have h6 := byteAt_lt m (p + 6)
  have h7 := byteAt_lt m (p + 7)
  rw [le64_eq]
  simp only [Keccak.readLE64, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [List.range', List.foldl, UInt64.toNat_or, UInt64.toNat_shiftLeft, toNat_byte,
    Nat.reduceAdd, Nat.reduceMul, UInt64.reduceToNat, UInt64.reduceOfNat, Nat.reducePow,
    Nat.reduceMod, Nat.add_zero, Nat.zero_or]
  simp (disch := omega) only [shl_mod]
  simp (disch := omega) only [or_shl_eq_add, Nat.shiftLeft_zero]
  omega

/-! ## Byte arrays -/

theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  unfold byteAt
  by_cases h : i < a.size
  · rw [if_pos h, dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h,
      ByteArray.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : i - a.size < b.size
    · rw [dif_pos (by rw [ByteArray.size_append]; omega), dif_pos h2,
        ByteArray.getElem_append_right (by omega)]
    · rw [dif_neg (by rw [ByteArray.size_append]; omega), dif_neg h2]

theorem byteAt_eq_getElem! (b : ByteArray) (i : Nat) : byteAt b i = b[i]!.toNat := by
  rw [byteAt_eq_getD, getElem!_def]
  cases b[i]? <;> rfl

theorem byteAt_set! (b : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (hi : i < b.size) :
    byteAt (b.set! i v) j = if i = j then v.toNat else byteAt b j := by
  rw [byteAt_eq_getElem!, byteAt_eq_getElem!, ByteArray.getElem!_set! _ _ _ _ hi]
  split <;> rfl

theorem byteAt_replicate (n i : Nat) : byteAt (ByteArray.mk (Array.replicate n 0)) i = 0 := by
  unfold byteAt
  split
  · change (Array.replicate n (0 : UInt8))[i].toNat = 0
    rw [Array.getElem_replicate]; rfl
  · rfl

theorem byteAt_extract (b : ByteArray) (lo hi i : Nat) (hi' : hi ≤ b.size) :
    byteAt (b.extract lo hi) i = if i < hi - lo then byteAt b (lo + i) else 0 := by
  unfold byteAt
  have hs : (b.extract lo hi).size = hi - lo := by simp [ByteArray.size_extract]; omega
  by_cases h : i < hi - lo
  · rw [dif_pos (by omega), if_pos h, dif_pos (by omega), ByteArray.getElem_extract]
  · rw [dif_neg (by omega), if_neg h]

/-! ## Padding -/

theorem pad_size (rate : Nat) (msg : ByteArray) (hr : 0 < rate) :
    (Fips202.pad rate 0x1F msg).size = (msg.size / rate + 1) * rate := by
  unfold Fips202.pad
  simp only [ByteArray.size_append, ByteArray.size_set!]
  change msg.size + (Array.replicate (rate - msg.size % rate) (0 : UInt8)).size = _
  rw [Array.size_replicate]
  have := Nat.mod_add_div msg.size rate
  have := Nat.mod_lt msg.size hr
  rw [Nat.add_mul, Nat.one_mul]
  have : rate * (msg.size / rate) = msg.size / rate * rate := Nat.mul_comm _ _
  omega

theorem byteAt_pad_lt (rate : Nat) (msg : ByteArray) (i : Nat) (hi : i < msg.size) :
    byteAt (Fips202.pad rate 0x1F msg) i = byteAt msg i := by
  unfold Fips202.pad
  simp only
  rw [byteAt_append, if_pos hi]

/-- Byte `i` of the final (padded) block. -/
theorem byteAt_pad_last (rate : Nat) (msg : ByteArray) (hr : 0 < rate) (i : Nat) (hi : i < rate) :
    byteAt (Fips202.pad rate 0x1F msg) (msg.size / rate * rate + i) =
      if i < msg.size % rate then byteAt msg (msg.size / rate * rate + i)
      else (if i = msg.size % rate then 31 else 0) ||| (if i = rate - 1 then 128 else 0) := by
  have hmd := Nat.mod_add_div msg.size rate
  have hml := Nat.mod_lt msg.size hr
  have hc : rate * (msg.size / rate) = msg.size / rate * rate := Nat.mul_comm _ _
  unfold Fips202.pad
  simp only
  rw [byteAt_append]
  by_cases h : i < msg.size % rate
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]
    have hp : 0 < rate - msg.size % rate := by omega
    have hsz0 : ((ByteArray.mk (Array.replicate (rate - msg.size % rate) 0))).size =
        rate - msg.size % rate := by
      change (Array.replicate _ (0 : UInt8)).size = _; rw [Array.size_replicate]
    have hsz1 : ((ByteArray.mk (Array.replicate (rate - msg.size % rate) 0)).set! 0 0x1F).size =
        rate - msg.size % rate := by rw [ByteArray.size_set!, hsz0]
    rw [byteAt_set! _ _ _ _ (by rw [hsz1]; omega), byteAt_set! _ _ _ _ (by rw [hsz0]; omega),
      byteAt_replicate]
    rw [ByteArray.getElem!_set! _ _ _ _ (by rw [hsz0]; omega)]
    have hz : ((ByteArray.mk (Array.replicate (rate - msg.size % rate) 0))[rate -
        msg.size % rate - 1]!) = 0 := by
      have := byteAt_replicate (rate - msg.size % rate) (rate - msg.size % rate - 1)
      rw [byteAt_eq_getElem!] at this
      exact UInt8.toNat_inj.mp this
    have hk : msg.size / rate * rate + i - msg.size = i - msg.size % rate := by omega
    rw [hk, hz]
    split_ifs <;> first | rfl | omega

/-- Bytes of a single padded block (`msg.size < rate`). -/
theorem byteAt_pad1 (rate : Nat) (msg : ByteArray) (hm : msg.size < rate) (i : Nat) (hi : i < rate) :
    byteAt (Fips202.pad rate 0x1F msg) i =
      if i < msg.size then byteAt msg i
      else (if i = msg.size then 31 else 0) ||| (if i = rate - 1 then 128 else 0) := by
  have := byteAt_pad_last rate msg (by omega) i hi
  rwa [Nat.div_eq_of_lt hm, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hm] at this

/-! ## `xorBlock` -/

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

theorem xorBlock_size (rate : Nat) (b : ByteArray) (off : Nat) (st : Fips202.SpongeState) :
    (Fips202.xorBlock rate b off st).size = st.size :=
  xorBlock_fold_size _ st _

theorem laneOf_xorBlock {rate : Nat} (b : ByteArray) (off : Nat) {st : Fips202.SpongeState}
    (hst : st.size = 25) (hr : rate / 8 ≤ 25) (x : Nat) :
    laneOf (Fips202.xorBlock rate b off st) x =
      if x < rate / 8 then laneOf st x ^^^ le64 b (off + 8 * x) else laneOf st x := by
  unfold laneOf Fips202.xorBlock
  rw [xorBlock_fold_getElem _ st (rate / 8) (by omega) x]
  split
  · rw [UInt64.toNat_xor, readLE64_toNat]
  · rfl

theorem emptyState_size : Fips202.emptyState.size = 25 := by
  simp [Fips202.emptyState]

theorem laneOf_emptyState (x : Nat) : laneOf Fips202.emptyState x = 0 := by
  unfold laneOf Fips202.emptyState
  by_cases h : x < 25
  · rw [getElem!_pos _ x (by simp [h])]; simp
  · rw [getElem!_neg _ x (by simp; omega)]; rfl

theorem laneOf_lt (S : Fips202.SpongeState) (x : Nat) : laneOf S x < 2 ^ 64 :=
  (S[x]!).toNat_lt

/-! ## The permutation keeps 25 lanes -/

private theorem foldl_foldl_set_size {α β : Type} (l1 : List α) (l2 : List β) (f : α → β → Nat)
    (g : Array UInt64 → α → β → UInt64) (A : Array UInt64) :
    (l1.foldl (fun B a => l2.foldl (fun B a' => B.set! (f a a') (g B a a')) B) A).size = A.size := by
  induction l1 generalizing A with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    clear ih
    induction l2 generalizing A with
    | nil => rfl
    | cons a' l' ih' => rw [List.foldl_cons, ih', Array.set!, Array.size_setIfInBounds]

theorem round_size (A : Array UInt64) (rc : UInt64) : (Keccak.round A rc).size = 25 := by
  unfold Keccak.round
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [Array.set!, Array.size_setIfInBounds, foldl_foldl_set_size]
  simp

theorem permute_size {A : Array UInt64} (h : A.size = 25) : (Keccak.permute A).size = 25 := by
  unfold Keccak.permute
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize List.range' 0 24 1 = l
  induction l generalizing A with
  | nil => exact h
  | cons a l ih => rw [List.foldl_cons]; exact ih (round_size _ _)

theorem permN_size {A : Array UInt64} (h : A.size = 25) : ∀ n, (permN n A).size = 25
  | 0 => h
  | n + 1 => by
    unfold permN; rw [Function.iterate_succ_apply']; exact permute_size (permN_size h n)

theorem permN_succ (n : Nat) (A : Fips202.SpongeState) :
    permN (n + 1) A = Keccak.permute (permN n A) := by
  unfold permN; rw [Function.iterate_succ_apply']

/-! ## Squeezing -/

/-- Byte `k` of the little-endian encoding of `w`. -/
def lb (w : UInt64) (k : Nat) : Nat := w.toNat / 256 ^ k % 256

private theorem lb_toUInt8 (w : UInt64) (k : Nat) (hk : k < 8) :
    ((w >>> UInt64.ofNat (8 * k)) &&& 255).toUInt8.toNat = lb w k := by
  unfold lb
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h1 : (UInt64.ofNat (8 * k)).toNat % 64 = 8 * k := by
    simp only [UInt64.toNat_ofNat']; omega
  rw [h1, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem byteAt_push (b : ByteArray) (x : UInt8) (i : Nat) :
    byteAt (b.push x) i = if i < b.size then byteAt b i else if i = b.size then x.toNat else 0 := by
  have : b.push x = b ++ ByteArray.mk #[x] := by
    apply ByteArray.ext; simp [ByteArray.push]
  rw [this, byteAt_append]
  split
  · rfl
  · by_cases h : i = b.size
    · subst h; rw [if_pos rfl, Nat.sub_self]; rfl
    · rw [if_neg h]; unfold byteAt; rw [dif_neg]; change ¬ (i - b.size < 1); omega

theorem byteAt_writeLE64 (acc : ByteArray) (w : UInt64) (i : Nat) :
    byteAt (Keccak.writeLE64 acc w) i =
      if i < acc.size then byteAt acc i else if i < acc.size + 8 then lb w (i - acc.size) else 0 := by
  simp only [Keccak.writeLE64, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  have hl : List.range' 0 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil, byteAt_push, ByteArray.size_push]
  rw [lb_toUInt8 w 0 (by omega), lb_toUInt8 w 1 (by omega), lb_toUInt8 w 2 (by omega),
    lb_toUInt8 w 3 (by omega), lb_toUInt8 w 4 (by omega), lb_toUInt8 w 5 (by omega),
    lb_toUInt8 w 6 (by omega), lb_toUInt8 w 7 (by omega)]
  by_cases h0 : i < acc.size
  · simp [h0, show i < acc.size + 1 by omega, show i < acc.size + 1 + 1 by omega,
      show i < acc.size + 1 + 1 + 1 by omega, show i < acc.size + 1 + 1 + 1 + 1 by omega,
      show i < acc.size + 1 + 1 + 1 + 1 + 1 by omega,
      show i < acc.size + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show i < acc.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  · obtain ⟨k, rfl⟩ : ∃ k, i = acc.size + k := ⟨i - acc.size, by omega⟩
    rw [if_neg h0, Nat.add_sub_cancel_left]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem byteAt_stateBytes_fold (L : Array UInt64) :
    ∀ n i, byteAt ((List.range n).foldl (fun out j => Keccak.writeLE64 out L[j]!) .empty) i =
      if i < 8 * n then lb L[i / 8]! (i % 8) else 0
  | 0, i => by simp [byteAt_eq_getD]
  | n + 1, i => by
    have hsz : ((List.range n).foldl (fun out j => Keccak.writeLE64 out L[j]!) .empty).size =
        8 * n := by
      have := MlDsa44.Proofs.Math.stateBytes_size (8 * n) L
      unfold Fips202.stateBytes at this
      rw [show 8 * n / 8 = n by omega] at this
      omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, byteAt_writeLE64, hsz,
      byteAt_stateBytes_fold L n i]
    by_cases h : i < 8 * n
    · rw [if_pos h, if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h2 : i < 8 * n + 8
      · rw [if_pos h2, if_pos (by omega), show i / 8 = n by omega, show i % 8 = i - 8 * n by omega]
      · rw [if_neg h2, if_neg (by omega)]

theorem byteAt_stateBytes (rate : Nat) (L : Array UInt64) (i : Nat) :
    byteAt (Fips202.stateBytes rate L) i = if i < 8 * (rate / 8) then lb L[i / 8]! (i % 8) else 0 :=
  byteAt_stateBytes_fold L (rate / 8) i

theorem le64_stateBytes (rate : Nat) (L : Array UInt64) {x : Nat} (hx : x < rate / 8) :
    le64 (Fips202.stateBytes rate L) (8 * x) = laneOf L x := by
  have hw := (L[x]!).toNat_lt
  rw [le64_eq]
  simp only [byteAt_stateBytes, show 8 * x < 8 * (rate / 8) by omega,
    show 8 * x + 1 < 8 * (rate / 8) by omega, show 8 * x + 2 < 8 * (rate / 8) by omega,
    show 8 * x + 3 < 8 * (rate / 8) by omega, show 8 * x + 4 < 8 * (rate / 8) by omega,
    show 8 * x + 5 < 8 * (rate / 8) by omega, show 8 * x + 6 < 8 * (rate / 8) by omega,
    show 8 * x + 7 < 8 * (rate / 8) by omega, if_true,
    show 8 * x / 8 = x by omega, show (8 * x + 1) / 8 = x by omega, show (8 * x + 2) / 8 = x by omega,
    show (8 * x + 3) / 8 = x by omega, show (8 * x + 4) / 8 = x by omega,
    show (8 * x + 5) / 8 = x by omega, show (8 * x + 6) / 8 = x by omega,
    show (8 * x + 7) / 8 = x by omega,
    show 8 * x % 8 = 0 by omega, show (8 * x + 1) % 8 = 1 by omega, show (8 * x + 2) % 8 = 2 by omega,
    show (8 * x + 3) % 8 = 3 by omega, show (8 * x + 4) % 8 = 4 by omega,
    show (8 * x + 5) % 8 = 5 by omega, show (8 * x + 6) % 8 = 6 by omega,
    show (8 * x + 7) % 8 = 7 by omega, lb, laneOf]
  generalize (L[x]!).toNat = w at hw ⊢
  norm_num
  omega

/-- Byte `rate · j + i` of `squeeze` is byte `i` of the `j`-th squeezed state. -/
theorem byteAt_squeeze (rate : Nat) (hr8 : rate / 8 * 8 = rate) :
    ∀ (B : Nat) (st : Fips202.SpongeState) (j i : Nat), j < B → i < rate →
      byteAt (Fips202.squeeze rate st B) (rate * j + i) =
        byteAt (Fips202.stateBytes rate (Keccak.permute^[j] st)) i
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | B + 1, st, j, i, hj, hi => by
    rw [Fips202.squeeze, byteAt_append, MlDsa44.Proofs.Math.stateBytes_size, hr8]
    rcases j with _ | j
    · rw [Nat.mul_zero, Nat.zero_add, if_pos hi]; rfl
    · rw [if_neg (by rw [Nat.mul_succ]; omega),
        show rate * (j + 1) + i - rate = rate * j + i by rw [Nat.mul_succ]; omega,
        byteAt_squeeze rate hr8 B _ j i (by omega) hi, Function.iterate_succ_apply]

/-- Lane `17 j + x` of a SHAKE256 output is lane `x` of the `j`-th squeezed state. -/
theorem le64_shake256 (msg : ByteArray) {n j x : Nat} (hx : x < 17) (hn : 8 * (17 * j + x) + 8 ≤ n) :
    le64 (Fips202.shake 136 msg n) (8 * (17 * j + x)) =
      laneOf (Keccak.permute^[j] (Fips202.absorb 136 (Fips202.pad 136 0x1F msg))) x := by
  unfold Fips202.shake
  have hsz := MlDsa44.Proofs.Math.squeeze_size' 136 (Fips202.absorb 136 (Fips202.pad 136 0x1F msg))
    ((n + 136 - 1) / 136)
  have hB : j < (n + 136 - 1) / 136 := by omega
  rw [← le64_stateBytes 136 _ (by omega : x < 136 / 8)]
  apply le64_congr
  intro k hk
  rw [byteAt_extract _ _ _ _ (by rw [hsz]; omega), if_pos (by omega), Nat.zero_add,
    show 8 * (17 * j + x) + k = 136 * j + (8 * x + k) by omega,
    byteAt_squeeze 136 rfl _ _ j (8 * x + k) hB (by omega)]

/-! ## Absorbing -/

/-- The state after absorbing the first `b` blocks of `padded`. -/
def absorbPre (rate : Nat) (padded : ByteArray) (b : Nat) : Fips202.SpongeState :=
  (List.range b).foldl (fun st i => Fips202.absorbBlock rate padded st (i * rate))
    Fips202.emptyState

theorem absorbPre_zero (rate : Nat) (padded : ByteArray) :
    absorbPre rate padded 0 = Fips202.emptyState := rfl

theorem absorbPre_succ (rate : Nat) (padded : ByteArray) (b : Nat) :
    absorbPre rate padded (b + 1) =
      Keccak.permute (Fips202.xorBlock rate padded (b * rate) (absorbPre rate padded b)) := by
  simp [absorbPre, List.range_succ, List.foldl_append, Fips202.absorbBlock]

theorem absorbPre_size (rate : Nat) (padded : ByteArray) : ∀ b, (absorbPre rate padded b).size = 25
  | 0 => emptyState_size
  | b + 1 => by rw [absorbPre_succ]; exact permute_size (by rw [xorBlock_size, absorbPre_size])

theorem absorb_eq (rate : Nat) (padded : ByteArray) (n : Nat) (hr : 0 < rate)
    (hsize : padded.size = n * rate) :
    Fips202.absorb rate padded = absorbPre rate padded n := by
  unfold Fips202.absorb absorbPre
  rw [hsize, Nat.mul_div_cancel _ hr]

end MlDsaOpt44.Proofs
