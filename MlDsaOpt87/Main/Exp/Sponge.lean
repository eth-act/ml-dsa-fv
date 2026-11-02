import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Fix
import MlDsaOpt87.Fn.Group.Seed
import MlDsaOpt87.Math
import MlDsaOpt44.Math.SpongeG234
import MlDsaOpt44.Math.Sponge
set_option warningAsError true
/-!
# Sponge facts of the ExpandA groups (ML-DSA-87, v4)

Restored from the v3 proofs (`Main/S5/Sponge.lean` of commit `c4b1ee3`) and
the ML-DSA-44 v4 mixed group (`MlDsaOpt44/Main/Ex/Round.lean`):

* `ginitWord_eq`, `ks4_ginit`: the state ML-DSA-87's `ginit` (no c̃ lanes)
  builds from fresh / kept slots;
* `HBlocks`: the heads of the squeezed blocks of a group (`blk` × 4, `blkh`),
  `HBlocks.slotHead`: the `gfix` precondition.
-/

namespace MlDsaOpt87.Proofs.Exp

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs

/-! ## `ginit` -/

theorem ginitWord_eq {m cd : ByteArray} (hrho : Rho1At m cd)
    {keep amult cmult kmask l4 : Nat} {L cur : Nat → Nat} {x : Nat}
    (ha : amult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hks : word m (KS + 32 * x) &&& keep = il fun k => if kmask.testBit k then cur k else 0)
    (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true → amult.testBit k = false ∧ L k = 0) :
    ginitWord m keep amult cmult l4 x =
      il fun k => if kmask.testBit k then cur k else
        cpl x (freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x) := by
  have hd0 : (if x < 4 then word m (RHO1 + 32 * x) * amult % 2 ^ 256 else 0) =
      il fun k => if x < 4 then (if amult.testBit k then le64 cd (8 * x) else 0) else 0 := by
    by_cases hx : x < 4
    · rw [if_pos hx, hrho x hx, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd1 : (if x = 4 then l4 else 0) = il fun k => if x = 4 then L k else 0 := by
    by_cases hx : x = 4
    · rw [if_pos hx, hl4]; exact il_congr fun k _ => by rw [if_pos hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by rw [if_neg hx]]
  have hd3 : (if x = 20 then spread (2 ^ 63) * amult % 2 ^ 256 else 0) =
      il fun k => if x = 20 ∧ amult.testBit k = true then 2 ^ 63 else 0 := by
    by_cases hx : x = 20
    · rw [if_pos hx, spread_mul _ ha, Nat.mod_eq_of_lt (il_lt _)]
      exact il_congr fun k _ => by simp [hx]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  have hd4 : (if x ∈ complemented then 2 ^ 256 - 1 - keep else 0) =
      il fun k => if x ∈ complemented ∧ kmask.testBit k = false then M64 else 0 := by
    by_cases hx : x ∈ complemented
    · rw [if_pos hx, hkeep, ones_sub_il (fun k _ => by split <;> simp [M64])]
      exact il_congr fun k _ => by
        cases hkk : kmask.testBit k <;> simp [hx, M64]
    · rw [if_neg hx, il_eq_zero fun k _ => by simp [hx]]
  unfold ginitWord
  simp only
  rw [hd0, hd1, hd3, hd4, hks, il_xor, il_xor, il_xor, il_or]
  apply il_congr
  intro k hk
  cases hkk : kmask.testBit k
  · have hf := freshLane_lt (amult := amult) (cmult := 0) (ρ := fun x => le64 cd (8 * x))
      (c := fun _ => 0) (k := k) (x := x) (le64_lt _ _) (by norm_num) (hL k hk)
    rw [cpl_eq hf]
    simp only [Bool.false_eq_true, if_false, Nat.or_zero]
    unfold freshLane
    simp only [Nat.zero_testBit, Bool.false_eq_true, if_false, and_false, Nat.xor_zero, ite_self]
    by_cases hx : x ∈ complemented
    · simp only [hx, true_and, if_true]
    · simp only [hx, false_and, if_false, Nat.xor_zero]
  · obtain ⟨h1, h3⟩ := hdisj k hk hkk
    simp only [h1, h3, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false, and_false,
      Nat.xor_zero, ite_self, Nat.zero_or]

/-- The state ML-DSA-87's `ginit` builds: kept slots (`kmask`) carry `S`, fresh
slots the states whose lanes are their `freshLane`s (no c̃ lanes). -/
theorem ks4_ginit {m m' cd : ByteArray} {keep amult cmult kmask l4 : Nat} {L : Nat → Nat}
    {S I : Nat → Fips202.SpongeState} (hrho : Rho1At m cd) (ha : amult < 16)
    (hkeep : keep = il fun k => if kmask.testBit k then M64 else 0) (hl4 : l4 = il L)
    (hand : ∀ x, x < 25 → word m (KS + 32 * x) &&& keep =
      il fun k => if kmask.testBit k then cpl x (laneOf (S k) x) else 0)
    (hL : ∀ k, k < 4 → L k < 2 ^ 64)
    (hdisj : ∀ k, k < 4 → kmask.testBit k = true → amult.testBit k = false ∧ L k = 0)
    (hkept : ∀ k, k < 4 → kmask.testBit k = true → I k = S k)
    (hfresh : ∀ k, k < 4 → kmask.testBit k = false → ∀ x, x < 25 →
      freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x = laneOf (I k) x)
    (hm' : ∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) :
    KS4 m' I := by
  intro x hx
  rw [hm' x hx, ginitWord_eq hrho ha hkeep hl4 (hand x hx) hL hdisj]
  apply il_congr; intro k hk
  cases hkk : kmask.testBit k
  · simp only [Bool.false_eq_true, if_false]; rw [hfresh k hk hkk x hx]
  · simp only [if_true]; rw [hkept k hk hkk]

theorem freshLane_aSeed' {cd : ByteArray} (hcd : 32 ≤ cd.size) {amult : Nat} {L : Nat → Nat}
    {k r col : Nat} (hr : r < 256) (hcol : col < 256)
    (ha : amult.testBit k = true) (hL : L k = col + 256 * r + 0x1F0000) {x : Nat} (hx : x < 25) :
    freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x =
      laneOf (seedState 168 (aSeed cd r col)) x :=
  freshLane_aSeed hcd (fun _ _ => rfl) hr hcol ha (Nat.zero_testBit k) hL hx

theorem freshLane_zero' {cd : ByteArray} {amult : Nat} {L : Nat → Nat} {k : Nat}
    (ha : amult.testBit k = false) (hL : L k = 0) (x : Nat) :
    freshLane amult 0 (fun x => le64 cd (8 * x)) (fun _ => 0) L k x = laneOf Fips202.emptyState x :=
  freshLane_zero ha (Nat.zero_testBit k) hL x

/-! ## `KS4`, block heads -/

theorem KS4.congr {m : ByteArray} {S S' : Nat → Fips202.SpongeState} (h : KS4 m S)
    (hS : ∀ k, k < 4 → S k = S' k) : KS4 m S' := fun x hx => by
  rw [h x hx]; exact il_congr fun k hk => by rw [hS k hk]

theorem KS4.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (h : KS4 m S) (hf : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S := fun x hx => by
  rw [word_frame hf ha (a := KS + 32 * x) (by omega) (by omega)]; exact h x hx

theorem pack4_congr {v w : Nat → Nat} (h : ∀ k, k < 4 → v k = w k) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem flagWord_congr {F G : Nat → Fips202.SpongeState} (h : ∀ k, k < 4 → F k = G k) (g : Nat) :
    flagWord F g = flagWord G g := by
  unfold flagWord
  have e : ((List.range 8).map fun i => pack4 fun k => cand (F k) (8 * g + i) + 2 ^ 23 - Fips204.q) =
      (List.range 8).map fun i => pack4 fun k => cand (G k) (8 * g + i) + 2 ^ 23 - Fips204.q :=
    List.map_congr_left fun i _ => pack4_congr fun k hk => by rw [h k hk]
  rw [e]

theorem sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-- The heads of blocks `0 … n − 1` of a SIMD group at `ABUF` / `FL`, block `b`
made from the slot states `St b` (the first 256 candidates, 32 flag words). -/
def HBlocks (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) (n : Nat) : Prop :=
  ∀ b, b < n →
    (∀ i, i < 56 → b * 56 + i < 256 → word m (ABUF + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i) ∧
    (∀ g, g < 7 → b * 7 + g < 32 → word m (FL + 224 * b + 32 * g) = flagWord (St b) g)

theorem HBlocks.zero (m : ByteArray) (St : Nat → Nat → Fips202.SpongeState) : HBlocks m St 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem HBlocks.frame {m m' : ByteArray} {St : Nat → Nat → Fips202.SpongeState} {n : Nat}
    {rs : List (Nat × Nat)} (h : HBlocks m St n) (hf : FrameExcept m m' rs)
    (ha : Avoids rs ABUF (ABUF + 1792 * n)) (hb : Avoids rs FL (FL + 224 * n)) : HBlocks m' St n :=
  fun b hbn => ⟨fun i hi hh => by
      rw [word_frame hf ha (a := ABUF + 1792 * b + 32 * i) (by omega) (by omega)]; exact (h b hbn).1 i hi hh,
    fun g hg hh => by
      rw [word_frame hf hb (a := FL + 224 * b + 32 * g) (by omega) (by omega)]; exact (h b hbn).2 g hg hh⟩

/-- Five block heads make slot `sl` a `gfix` slot. -/
theorem HBlocks.slotHead {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState}
    (h : HBlocks m St 5) {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState}
    (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I) : SlotHead m sl I := by
  refine ⟨fun t ht => ?_, fun g hg => ?_⟩
  · have hb : t / 56 < 5 := by omega
    rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
      (h _ hb).1 _ (Nat.mod_lt _ (by norm_num)) (by omega), MlDsaOpt44.Proofs.lane_pack4_cand _ _ hsl,
      hSt _ hb]
    rfl
  · have hb : g / 7 < 5 := by omega
    rw [show FL + 32 * g = FL + 224 * (g / 7) + 32 * (g % 7) by omega,
      (h _ hb).2 _ (Nat.mod_lt _ (by norm_num)) (by omega), flagBit_flagWord _ _ hsl, hSt _ hb]
    rw [any_congr_mem (q := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) fun i hi => by
      rw [List.mem_range] at hi
      unfold candI
      rw [show (8 * g + i) / 56 = g / 7 by omega, show (8 * g + i) % 56 = 8 * (g % 7) + i by omega]]

end MlDsaOpt87.Proofs.Exp
