import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Math.Sponge
set_option warningAsError true
/-!
# Byte-level facts for the SHAKE sponge driver

* `byteAt` of `++`, `push`, `set!`, `readPadded`;
* `readLE64_congr`, `xorBlock_congr`: lane reads depend only on the bytes read;
* `byteAt_writeLE64`, `byteAt_stateBytes`: little-endian lane bytes (`lb`);
* `squeeze_succ`: `squeeze` one block at a time from the end;
* `pad_size`, `byteAt_pad_lt`, `byteAt_pad_last`: bytes of `Fips202.pad rate 0x1F`;
* `absorb_split`: the last absorbed block separated from the full blocks.
-/

namespace MlDsa44.Proofs.Shake

open EvmSemantics
open EvmSemantics.Crypto

theorem byteAt_eq_getElem! (b : ByteArray) (i : Nat) : byteAt b i = b[i]!.toNat := by
  rw [Infra.byteAt_eq_getD, getElem!_def]
  cases b[i]? <;> rfl

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

theorem byteAt_set! (b : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (hi : i < b.size) :
    byteAt (b.set! i v) j = if i = j then v.toNat else byteAt b j := by
  rw [byteAt_eq_getElem!, byteAt_eq_getElem!, ByteArray.getElem!_set! _ _ _ _ hi]
  split <;> rfl

theorem byteAt_replicate (n i : Nat) : byteAt (ByteArray.mk (Array.replicate n 0)) i = 0 := by
  unfold byteAt
  split
  · rename_i h
    change (Array.replicate n (0 : UInt8))[i].toNat = 0
    rw [Array.getElem_replicate]; rfl
  · rfl

theorem byteAt_readPadded (m : ByteArray) (p n i : Nat) :
    byteAt (MachineState.readPadded m p n) i = if i < n then byteAt m (p + i) else 0 := by
  rw [Infra.byteAt_eq_getD, EvmProof.Memory.readPadded_getElem?_getD]
  split
  · rw [Infra.byteAt_eq_getD]
  · rfl

/-! ## Lane reads -/

theorem toNat_byte (m : ByteArray) (a : Nat) :
    (if h : a < m.size then m[a].toUInt64 else 0 : UInt64).toNat = byteAt m a := by
  unfold byteAt; split <;> simp

theorem readLE64_congr {b b' : ByteArray} {p p' : Nat}
    (h : ∀ k, k < 8 → byteAt b' (p' + k) = byteAt b (p + k)) :
    Keccak.readLE64 b' p' = Keccak.readLE64 b p := by
  simp only [Keccak.readLE64, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  apply List.foldl_ext
  intro w k hk
  rw [List.mem_range'] at hk
  have hk8 : k < 8 := by omega
  have : (if h : p' + k < b'.size then b'[p' + k].toUInt64 else 0 : UInt64) =
      (if h : p + k < b.size then b[p + k].toUInt64 else 0 : UInt64) := by
    apply UInt64.toNat_inj.mp
    rw [toNat_byte, toNat_byte, h k hk8]
  rw [this]

theorem xorBlock_congr {rate : Nat} {b b' : ByteArray} {o o' : Nat} (st : Array UInt64)
    (h : ∀ i, i < rate / 8 * 8 → byteAt b' (o' + i) = byteAt b (o + i)) :
    Fips202.xorBlock rate b' o' st = Fips202.xorBlock rate b o st := by
  unfold Fips202.xorBlock
  apply List.foldl_ext
  intro A j hj
  rw [List.mem_range] at hj
  rw [readLE64_congr (b := b) (p := o + 8 * j) (fun k hk => by
    have := h (8 * j + k) (by omega)
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)]

/-! ## Lane writes -/

/-- Byte `k` of the little-endian encoding of `w`. -/
def lb (w : UInt64) (k : Nat) : Nat := w.toNat / 256 ^ k % 256

theorem lb_toUInt8 (w : UInt64) (k : Nat) (hk : k < 8) :
    ((w >>> UInt64.ofNat (8 * k)) &&& 255).toUInt8.toNat = lb w k := by
  unfold lb
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h1 : (UInt64.ofNat (8 * k)).toNat % 64 = 8 * k := by
    simp only [UInt64.toNat_ofNat']; omega
  rw [h1, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

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

theorem writeLE64_size (acc : ByteArray) (w : UInt64) :
    (Keccak.writeLE64 acc w).size = acc.size + 8 := Math.writeLE64_size acc w

theorem byteAt_stateBytes_fold (L : Array UInt64) :
    ∀ n i, byteAt ((List.range n).foldl (fun out j => Keccak.writeLE64 out L[j]!) .empty) i =
      if i < 8 * n then lb L[i / 8]! (i % 8) else 0
  | 0, i => by simp [Infra.byteAt_eq_getD]
  | n + 1, i => by
    have hsz : ((List.range n).foldl (fun out j => Keccak.writeLE64 out L[j]!) .empty).size =
        8 * n := by
      have := Math.stateBytes_size (8 * n) L
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

theorem squeeze_succ (rate : Nat) :
    ∀ (b : Nat) (st : Fips202.SpongeState), Fips202.squeeze rate st (b + 1) =
      Fips202.squeeze rate st b ++ Fips202.stateBytes rate (Keccak.permute^[b] st)
  | 0, st => by simp [Fips202.squeeze, ByteArray.empty_append, ByteArray.append_empty]
  | b + 1, st => by
    rw [Fips202.squeeze, squeeze_succ rate b (Keccak.permute st), Fips202.squeeze,
      ByteArray.append_assoc, Function.iterate_succ_apply]

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

/-! ## Absorb -/

/-- The state after absorbing the first `b` blocks of `padded`. -/
def absorbPre (rate : Nat) (padded : ByteArray) (b : Nat) : Fips202.SpongeState :=
  (List.range b).foldl (fun st i => Fips202.absorbBlock rate padded st (i * rate))
    Fips202.emptyState

theorem absorbPre_succ (rate : Nat) (padded : ByteArray) (b : Nat) :
    absorbPre rate padded (b + 1) =
      Keccak.permute (Fips202.xorBlock rate padded (b * rate) (absorbPre rate padded b)) := by
  simp [absorbPre, List.range_succ, List.foldl_append, Fips202.absorbBlock]

theorem absorb_eq (rate : Nat) (padded : ByteArray) (n : Nat) (hr : 0 < rate)
    (hsize : padded.size = (n + 1) * rate) :
    Fips202.absorb rate padded = absorbPre rate padded (n + 1) := by
  unfold Fips202.absorb absorbPre
  rw [hsize, Nat.mul_div_cancel _ hr]

end MlDsa44.Proofs.Shake
