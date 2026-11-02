import MlDsaOpt65.Main.Exp.Bound
import MlDsaOpt65.Main.Exp.Round
import MlDsaOpt65.Main.Mu.Spec
import MlDsaOpt44.Main.Mu.Lemmas
set_option warningAsError true
/-!
# Group 8's slot states and μ's sponge in slot 2 (ML-DSA-65, v4)

Group 8 runs `A[5][4]` in slot 0, the c̃ stream in slot 1 and μ's SHAKE256
in slot 2 (slot 3 empty). μ has `muN cd = ⌊(66 + |M|)/136⌋ + 1` padded blocks:
`mub0` absorbs block 0 before the first `kf4`, `mub k` (long messages) absorbs
block `k < min(N, 5)` after the `k`-th `kf4`, or squeezes μ into `MU` when
block `k − 1` was the last (`k = N`); short messages (`N = 1`) squeeze μ by an
inline `cext` after the first `kf4`.

* `muT cd b`: slot 2 before `kf4` number `b + 1` (on both paths);
  `muT_absorb`: `permute (muT b) = absorbPre (b + 1)` while `b < N`;
* `Sb cd b` / `St cd b`: the four slots before / after `kf4` number `b + 1`;
* `le64_muOf_St`: when `N = b + 1 ≤ 5`, slot 2 of `St b` squeezes μ.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsa44

namespace Exp

/-- μ's padded SHAKE256 input `pad(tr ‖ 0 ‖ 0 ‖ M)`. -/
abbrev muP (cd : ByteArray) : ByteArray := padMu cd

/-- Number of 136-byte blocks of `muP`. -/
def muN (cd : ByteArray) : Nat := (66 + mlenOf cd) / 136 + 1

/-- Slot 2 before `kf4` number `b + 1`. -/
def muT (cd : ByteArray) : Nat → Fips202.SpongeState
  | 0 => Fips202.xorBlock 136 (muP cd) 0 Fips202.emptyState
  | b + 1 => if b + 1 < muN cd ∧ b + 1 < 5 then
      Fips202.xorBlock 136 (muP cd) (136 * (b + 1)) (Keccak.permute (muT cd b))
    else Keccak.permute (muT cd b)

/-- Group 8's slots after `ginit`: `A[5][4]`'s seed, c̃'s seed, two empty slots. -/
def I8 (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedState 168 (aSeed cd 5 4) else if k = 1 then seedState 136 (ctOf cd)
  else Fips202.emptyState

/-- The slots before `kf4` number `b + 1`. -/
def Sb (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 2 then muT cd b else permN b (I8 cd k)

/-- The slots after `kf4` number `b + 1` (what `blk b` extracts). -/
def St (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := Keccak.permute (Sb cd b k)

theorem muT_succ (cd : ByteArray) (b : Nat) : muT cd (b + 1) =
    if b + 1 < muN cd ∧ b + 1 < 5 then
      Fips202.xorBlock 136 (muP cd) (136 * (b + 1)) (Keccak.permute (muT cd b))
    else Keccak.permute (muT cd b) := rfl

theorem muT_size (cd : ByteArray) : ∀ b, (muT cd b).size = 25
  | 0 => by unfold muT; rw [xorBlock_size, emptyState_size]
  | b + 1 => by
    unfold muT
    split
    · rw [xorBlock_size]; exact permute_size (muT_size cd b)
    · exact permute_size (muT_size cd b)

theorem I8_size (cd : ByteArray) (k : Nat) : (I8 cd k).size = 25 := by
  unfold I8; split_ifs <;> first | exact seedState_size _ _ | exact emptyState_size

theorem Sb_sized (cd : ByteArray) (b : Nat) : Sized4 (Sb cd b) := fun k _ => by
  unfold Sb; split
  · exact muT_size cd b
  · exact permN_size (I8_size cd k) b

theorem St_sized (cd : ByteArray) (b : Nat) : Sized4 (St cd b) := fun k hk =>
  permute_size (Sb_sized cd b k hk)

theorem St_ne2 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k ≠ 2) : St cd b k = permN (b + 1) (I8 cd k) := by
  unfold St Sb; rw [if_neg hk, permN_succ]

theorem St_two (cd : ByteArray) (b : Nat) : St cd b 2 = Keccak.permute (muT cd b) := by
  unfold St Sb; rw [if_pos rfl]

theorem Sb_zero (cd : ByteArray) : Sb cd 0 = fun k => if k = 2 then muT cd 0 else I8 cd k := by
  funext k; unfold Sb; rfl

/-- `mub (b + 1)` absorbs block `b + 1`. -/
theorem Sb_succ_abs (cd : ByteArray) {b : Nat} (h : b + 1 < muN cd ∧ b + 1 < 5) (k : Nat) :
    Sb cd (b + 1) k = if k = 2 then
      Fips202.xorBlock 136 (muP cd) (136 * (b + 1)) (St cd b 2) else St cd b k := by
  by_cases hk : k = 2
  · subst hk; unfold Sb; simp only [if_true]; rw [St_two, muT_succ, if_pos h]
  · rw [if_neg hk, St_ne2 cd b hk]; unfold Sb; rw [if_neg hk]

/-- No absorption: the slots before the next `kf4` are the slots after this one. -/
theorem Sb_succ_keep (cd : ByteArray) {b : Nat} (h : ¬ (b + 1 < muN cd ∧ b + 1 < 5)) (k : Nat) :
    Sb cd (b + 1) k = St cd b k := by
  by_cases hk : k = 2
  · subst hk; rw [St_two]; unfold Sb; simp only [if_true]; rw [muT_succ, if_neg h]
  · rw [St_ne2 cd b hk]; unfold Sb; rw [if_neg hk]

/-! ## μ's blocks -/

theorem muMsg_size (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size = 66 + mlenOf cd := by
  have := S6Mu.muMsgW_size cd hcd
  unfold S6Mu.muMsgW at this; rw [this]; unfold mlenOf HDR; rfl

theorem muP_size (cd : ByteArray) (hcd : HDR ≤ cd.size) : (muP cd).size = muN cd * 136 := by
  unfold muP padMu muN
  rw [pad_size 136 _ (by norm_num), muMsg_size cd hcd]

theorem muT_eq (cd : ByteArray) : ∀ b, b < muN cd → b ≤ 4 →
    muT cd b = Fips202.xorBlock 136 (muP cd) (b * 136) (absorbPre 136 (muP cd) b)
  | 0, _, _ => by unfold muT; rfl
  | b + 1, hb, hb4 => by
    rw [muT_succ, if_pos ⟨hb, by omega⟩, muT_eq cd b (by omega) (by omega), ← absorbPre_succ]
    congr 1; ring

theorem muT_absorb (cd : ByteArray) {b : Nat} (hb : b < muN cd) (hb4 : b ≤ 4) :
    Keccak.permute (muT cd b) = absorbPre 136 (muP cd) (b + 1) := by
  rw [muT_eq cd b hb hb4, absorbPre_succ]

/-- When `N = b + 1`, slot 2 of `St b` is μ's absorbed state. -/
theorem le64_muOf_St (cd : ByteArray) (hcd : HDR ≤ cd.size) {b : Nat} (hN : muN cd = b + 1)
    (hb4 : b ≤ 4) {x : Nat} (hx : x < 8) :
    laneOf (St cd b 2) x = le64 (muOf cd) (8 * x) := by
  rw [St_two, muT_absorb cd (by omega) hb4, S6Mu.le64_muOf_absorb cd hx, show S6Mu.muPad cd = muP cd from rfl,
    absorb_eq 136 (muP cd) (b + 1) (by norm_num) (by rw [muP_size cd hcd, hN])]

/-- `mub0`'s bytes are block 0 of `muP` (padded iff it is the only block). -/
theorem le64_mu0Bytes (cd : ByteArray) (hcd : HDR ≤ cd.size) {x : Nat} (hx : x < 17) :
    le64 (mu0Bytes (trOf cd) cd) (8 * x) = le64 (muP cd) (8 * x) := by
  unfold mu0Bytes
  split
  · rfl
  · rename_i h
    unfold muP padMu muIn
    rw [le64_pad_full _ (by rw [muMsg_size cd hcd]; unfold mlenOf at *; omega)]

theorem muPadded_eq (cd : ByteArray) : muPadded (trOf cd) cd = muP cd := rfl

/-- Slot 2 after `mub0`. -/
theorem laneOf_muT0 (cd : ByteArray) (x : Nat) :
    laneOf (muT cd 0) x = laneOf Fips202.emptyState x ^^^
      (if x < 17 then le64 (muP cd) (8 * x) else 0) := by
  unfold muT
  rw [laneOf_xorBlock _ _ emptyState_size (by norm_num), laneOf_emptyState]
  split <;> simp_all

/-- Slot 2 after `mub (b + 1)` absorbs. -/
theorem laneOf_absorb (cd : ByteArray) (S : Fips202.SpongeState) (hS : S.size = 25) (b x : Nat) :
    laneOf (Fips202.xorBlock 136 (muP cd) (136 * (b + 1)) S) x = laneOf S x ^^^
      (if x < 17 then le64 (muP cd) (136 * (b + 1) + 8 * x) else 0) := by
  rw [laneOf_xorBlock _ _ hS (by norm_num)]
  split <;> simp_all

theorem muN_short {cd : ByteArray} : muN cd = 1 ↔ mlenOf cd ≤ 69 := by
  unfold muN; omega

end Exp

end MlDsaOpt65.Proofs
