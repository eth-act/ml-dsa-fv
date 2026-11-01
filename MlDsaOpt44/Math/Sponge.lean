import MlDsaOpt44.Fn.Fix.Defs
import MlDsaOpt44.Math.SpongeSeed
set_option warningAsError true
/-!
# Sponge meaning of the SIMD Keccak states

* `aI_seedState`: RejNTTPoly over the six squeezed blocks of a seed state is
  `Fips204.rejNTTPoly` of the seed; with `MlDsaOpt44.Math.SpongeSeed`
  (`seedState`, `aSeed`, `laneOf_aSeed`, `ginitWord_eq`, `ginit_group`).
* `lane_pack4_cand`, `flagBit_flagWord`, `pending_of_blocks`: what five
  `blk` calls leave in `ABUF` / `FL` is `Pending` for every slot.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44

theorem aI_seedState {seed : ByteArray} (h : seed.size < 168) :
    aI (seedState 168 seed) = Fips204.rejNTTPoly seed := by
  unfold aI Fips204.rejNTTPoly Fips204.G Fips202.shake128
  rw [← MlDsa44.Proofs.Math.squeeze_extract_shake 168 seed Fips204.rejNTTPolyLimit 6
    (Or.inr rfl) (by decide), absorb_single (by norm_num) h]
  congr 1
  have hs := MlDsa44.Proofs.Math.squeeze_size' 168 (Keccak.permute (seedState 168 seed)) 6
  rw [show Fips204.rejNTTPolyLimit = (Fips202.squeeze 168 (Keccak.permute (seedState 168 seed)) 6).size
    by rw [hs]; rfl]
  exact (ByteArray.extract_zero_size).symm

/-! ## `blk` outputs as pending slots -/

theorem cand_lt (S : Fips202.SpongeState) (i : Nat) : cand S i < 2 ^ 23 := by
  have h0 : sbyte S (3 * i) < 256 := Nat.mod_lt _ (by norm_num)
  have h1 : sbyte S (3 * i + 1) < 256 := Nat.mod_lt _ (by norm_num)
  have h2 : sbyte S (3 * i + 2) % 128 < 128 := Nat.mod_lt _ (by norm_num)
  unfold cand; omega

private theorem lane_pack4' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem lane_pack4_cand (S : Nat → Fips202.SpongeState) (i : Nat) {s : Nat} (hs : s < 4) :
    lane (pack4 fun k => cand (S k) i) s = cand (S s) i :=
  lane_pack4' (fun k _ => Nat.lt_trans (cand_lt _ _) (by norm_num)) hs

theorem testBit_orList_map {f : Nat → Nat} {P : Nat → Bool} {j : Nat} :
    ∀ (l : List Nat), (∀ i, i ∈ l → (f i).testBit j = P i) → ∀ acc,
      (List.foldl (· ||| ·) acc (l.map f)).testBit j = (acc.testBit j || l.any P)
  | [], _, acc => by simp
  | i :: l, h, acc => by
    rw [List.map_cons, List.foldl_cons,
      testBit_orList_map l (fun i' hi' => h i' (List.mem_cons_of_mem _ hi')),
      Nat.testBit_or, h i (List.mem_cons_self ..), List.any_cons, Bool.or_assoc]

theorem flagBit_eq (w s : Nat) : flagBit w s = if w.testBit (64 * s + 23) then 1 else 0 := by
  unfold flagBit; exact bit_eq w _

theorem testBit_lane (w s j : Nat) (hj : j < 64) : (lane w s).testBit j = w.testBit (64 * s + j) := by
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm]

theorem testBit23 {c : Nat} (hc : c < 2 ^ 23) :
    (c + 2 ^ 23 - Fips204.q).testBit 23 = decide (Fips204.q ≤ c) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  unfold Fips204.q
  constructor <;> intro h <;> omega

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a, a ∈ l → p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem testBit_flagLanes (S : Nat → Fips202.SpongeState) (g i : Nat) {s : Nat} (hs : s < 4) :
    (pack4 fun k => cand (S k) (8 * g + i) + 2 ^ 23 - Fips204.q).testBit (64 * s + 23) =
      decide (Fips204.q ≤ cand (S s) (8 * g + i)) := by
  have hv : ∀ k, k < 4 → cand (S k) (8 * g + i) + 2 ^ 23 - Fips204.q < 2 ^ 64 := fun k _ => by
    have := cand_lt (S k) (8 * g + i); omega
  rw [← testBit_lane _ _ _ (show 23 < 64 by norm_num), lane_pack4' hv hs]
  exact testBit23 (cand_lt _ _)

theorem flagBit_flagWord (S : Nat → Fips202.SpongeState) (g : Nat) {s : Nat} (hs : s < 4) :
    flagBit (flagWord S g) s =
      if (List.range 8).any (fun i => decide (Fips204.q ≤ cand (S s) (8 * g + i))) then 1 else 0 := by
  have key := testBit_orList_map
    (f := fun i => pack4 fun k => cand (S k) (8 * g + i) + 2 ^ 23 - Fips204.q)
    (P := fun i => decide (Fips204.q ≤ cand (S s) (8 * g + i))) (j := 64 * s + 23) (List.range 8)
    (fun i _ => testBit_flagLanes S g i hs) 0
  rw [Nat.zero_testBit, Bool.false_or] at key
  rw [flagBit_eq]
  exact congrArg (fun b : Bool => if b = true then 1 else 0) key

/-- Five `blk` outputs, block `b` made from the slot states `St b`, make slot
`sl` pending when its states are the permutations of `I`. -/
theorem pending_of_blocks {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState} {sl : Nat}
    (hsl : sl < 4) {I : Fips202.SpongeState} (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I)
    (hA : ∀ b, b < 5 → ∀ i, i < 56 → word m (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i)
    (hF : ∀ b, b < 5 → ∀ g, g < 7 → word m (FL + 224 * b + 32 * g) = flagWord (St b) g)
    (h6 : word m HAVE6 = 0) {S : Nat → Fips202.SpongeState} (hS : S sl = permN 5 I) :
    Pending m S sl I := by
  refine ⟨⟨fun t ht => ?_, fun g hg => ?_⟩, fun _ => hS, fun h => absurd h6 h⟩
  · have hb : t / 56 < 5 := by omega
    rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
      hA _ hb _ (Nat.mod_lt _ (by norm_num)), lane_pack4_cand _ _ hsl, hSt _ hb]
    rfl
  · have hb : g / 7 < 5 := by omega
    rw [show FL + 32 * g = FL + 224 * (g / 7) + 32 * (g % 7) by omega,
      hF _ hb _ (Nat.mod_lt _ (by norm_num)), flagBit_flagWord _ _ hsl, hSt _ hb]
    rw [any_congr_mem (q := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) fun i hi => by
      rw [List.mem_range] at hi
      unfold candI
      rw [show (8 * g + i) / 56 = g / 7 by omega, show (8 * g + i) % 56 = 8 * (g % 7) + i by omega]]

/-- `pending_of_blocks` when every slot's states are the permutations of its seed. -/
theorem pending_of_blocks' {m : ByteArray} {I : Nat → Fips202.SpongeState}
    (hA : ∀ b, b < 5 → ∀ i, i < 56 → word m (ABUF + 1792 * b + 32 * i) =
      pack4 fun k => cand (permN (b + 1) (I k)) i)
    (hF : ∀ b, b < 5 → ∀ g, g < 7 → word m (FL + 224 * b + 32 * g) =
      flagWord (fun k => permN (b + 1) (I k)) g)
    (h6 : word m HAVE6 = 0) : ∀ sl, sl < 4 → Pending m (fun k => permN 5 (I k)) sl (I sl) :=
  fun _ hsl => pending_of_blocks (St := fun b k => permN (b + 1) (I k)) hsl (fun _ _ => rfl) hA hF h6 rfl

end MlDsaOpt44.Proofs
