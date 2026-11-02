import MlDsaOptGlam44.Main.Alt.Defs
import MlDsaOptGlam44.Main.Win.Math
set_option warningAsError true
/-!
# μ's slot in the long-message schedule's last group

μ's padded input `padMu` has `nbMu = P / 136 + 1` blocks (`P = 66 + |M|`). Slot 1
of the last group absorbs block `b` before its `b`-th squeeze while `b < nbMu`
(`mub0` for block 0, `mub` for blocks `1 … 4`) and then keeps permuting:
`muT b` is the slot state the `(b+1)`-th `kf4` sees, `Sb b` / `St b` the four
slots before / after it. `mub` at `k = nbMu` extracts μ (`le64_muOf_St`).
-/

namespace MlDsaOptGlam44.Proofs.Alt

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs
open MlDsaOptGlam44.Proofs.Ex

/-- `P = 66 + |M|`, the length of `tr ‖ 0 ‖ 0 ‖ M`. -/
theorem muIn_size (cd : ByteArray) :
    (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)).size = 66 + mlenOf cd := by
  rw [ByteArray.size_append, ByteArray.size_append, trOf_size,
    show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
  unfold msgOf mlenOf
  simp [ByteArray.size_extract]
  omega

/-- The number of blocks of `padMu`. -/
def nbMu (cd : ByteArray) : Nat := (66 + mlenOf cd) / 136 + 1

theorem padMu_size (cd : ByteArray) : (padMu cd).size = nbMu cd * 136 := by
  unfold padMu nbMu
  rw [pad_size _ _ (by norm_num), muIn_size]

/-- μ's slot (slot 1) before `kf4` number `b + 1`: `mub0` absorbed block 0,
`mub (b + 1)` absorbs block `b + 1` while `b + 1 < min(nbMu, 5)`. -/
def muT (cd : ByteArray) : Nat → Fips202.SpongeState
  | 0 => Fips202.xorBlock 136 (padMu cd) 0 Fips202.emptyState
  | b + 1 => if b + 1 < nbMu cd ∧ b + 1 < 5 then
      Fips202.xorBlock 136 (padMu cd) (136 * (b + 1)) (Keccak.permute (muT cd b))
    else Keccak.permute (muT cd b)

/-- The last group's slots after `ginit`: c̃'s seed, μ (empty), `A[3][3]`, `A[3][2]`. -/
def IK (cd : ByteArray) (k : Nat) : Fips202.SpongeState :=
  if k = 0 then seedState 136 (ctOf cd) else if k = 1 then Fips202.emptyState
  else if k = 2 then seedA cd 3 3 else seedA cd 3 2

/-- The slots before `kf4` number `b + 1`. -/
def Sb (cd : ByteArray) (b k : Nat) : Fips202.SpongeState :=
  if k = 1 then muT cd b else permN b (IK cd k)

/-- The slots after `kf4` number `b + 1` (what `blk b` extracts). -/
def St (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := Keccak.permute (Sb cd b k)

theorem muT_succ (cd : ByteArray) (b : Nat) : muT cd (b + 1) =
    if b + 1 < nbMu cd ∧ b + 1 < 5 then
      Fips202.xorBlock 136 (padMu cd) (136 * (b + 1)) (Keccak.permute (muT cd b))
    else Keccak.permute (muT cd b) := rfl

theorem muT_size (cd : ByteArray) : ∀ b, (muT cd b).size = 25
  | 0 => by unfold muT; rw [xorBlock_size, emptyState_size]
  | b + 1 => by
    unfold muT
    split
    · rw [xorBlock_size]; exact permute_size (muT_size cd b)
    · exact permute_size (muT_size cd b)

theorem IK_size (cd : ByteArray) (k : Nat) : (IK cd k).size = 25 := by
  unfold IK seedA; split_ifs <;> first | exact seedState_size _ _ | exact emptyState_size

theorem Sb_sized (cd : ByteArray) (b : Nat) : Sized4 (Sb cd b) := fun k _ => by
  unfold Sb; split
  · exact muT_size cd b
  · exact permN_size (IK_size cd k) b

theorem St_sized (cd : ByteArray) (b : Nat) : Sized4 (St cd b) := fun k hk =>
  permute_size (Sb_sized cd b k hk)

theorem St_ne1 (cd : ByteArray) (b : Nat) {k : Nat} (hk : k ≠ 1) : St cd b k = permN (b + 1) (IK cd k) := by
  unfold St Sb; rw [if_neg hk, permN_succ]

theorem St_one (cd : ByteArray) (b : Nat) : St cd b 1 = Keccak.permute (muT cd b) := by
  unfold St Sb; rw [if_pos rfl]

/-- `mub (b + 1)` absorbs block `b + 1`. -/
theorem Sb_succ_abs (cd : ByteArray) {b : Nat} (h : b + 1 < nbMu cd ∧ b + 1 < 5) (k : Nat) :
    Sb cd (b + 1) k = if k = 1 then
      Fips202.xorBlock 136 (padMu cd) (136 * (b + 1)) (St cd b 1) else St cd b k := by
  by_cases hk : k = 1
  · subst hk; unfold Sb; simp only [if_true]; rw [St_one, muT_succ, if_pos h]
  · rw [if_neg hk, St_ne1 cd b hk]; unfold Sb; rw [if_neg hk]

/-- No absorption: the slots before the next `kf4` are the slots after this one. -/
theorem Sb_succ_keep (cd : ByteArray) {b : Nat} (h : ¬ (b + 1 < nbMu cd ∧ b + 1 < 5)) (k : Nat) :
    Sb cd (b + 1) k = St cd b k := by
  by_cases hk : k = 1
  · subst hk; rw [St_one]; unfold Sb; simp only [if_true]; rw [muT_succ, if_neg h]
  · rw [St_ne1 cd b hk]; unfold Sb; rw [if_neg hk]

theorem muT_eq (cd : ByteArray) : ∀ b, b < nbMu cd → b ≤ 4 →
    muT cd b = Fips202.xorBlock 136 (padMu cd) (b * 136) (absorbPre 136 (padMu cd) b)
  | 0, _, _ => by unfold muT; rfl
  | b + 1, hb, hb4 => by
    rw [muT_succ, if_pos ⟨hb, by omega⟩, muT_eq cd b (by omega) (by omega), ← absorbPre_succ]
    congr 1; ring

theorem muT_absorb (cd : ByteArray) {b : Nat} (hb : b < nbMu cd) (hb4 : b ≤ 4) :
    Keccak.permute (muT cd b) = absorbPre 136 (padMu cd) (b + 1) := by
  rw [muT_eq cd b hb hb4, absorbPre_succ]

/-- μ's lanes are those of the absorbed state. -/
theorem le64_muOf_nb {cd : ByteArray} {x : Nat} (hx : x < 8) :
    le64 (muOf cd) (8 * x) = laneOf (absorbPre 136 (padMu cd) (nbMu cd)) x := by
  unfold muOf Fips204.H Fips202.shake256
  have := le64_shake256 (trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)) (n := 64) (j := 0)
    (by omega : x < 17) (by omega)
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this, Function.iterate_zero_apply]
  exact congrArg (fun S => laneOf S x) (absorb_eq 136 _ (nbMu cd) (by norm_num) (padMu_size cd))

/-- When `nbMu = b + 1`, slot 1 of `St b` is μ's absorbed state. -/
theorem le64_muOf_St (cd : ByteArray) {b : Nat} (hN : nbMu cd = b + 1) (hb4 : b ≤ 4) {x : Nat}
    (hx : x < 8) : laneOf (St cd b 1) x = le64 (muOf cd) (8 * x) := by
  rw [St_one, muT_absorb cd (by omega) hb4, le64_muOf_nb hx, hN]

/-- Slot 1 after `mub (b + 1)` absorbs. -/
theorem laneOf_absorb (cd : ByteArray) (S : Fips202.SpongeState) (hS : S.size = 25) (b x : Nat) :
    laneOf (Fips202.xorBlock 136 (padMu cd) (136 * (b + 1)) S) x = laneOf S x ^^^
      (if x < 17 then le64 (padMu cd) (136 * (b + 1) + 8 * x) else 0) := by
  rw [laneOf_xorBlock _ _ hS (by norm_num)]
  split <;> simp_all

/-- Slot 1 after `mub0`. -/
theorem laneOf_muT0 (cd : ByteArray) (x : Nat) :
    laneOf (muT cd 0) x = laneOf Fips202.emptyState x ^^^
      (if x < 17 then le64 (padMu cd) (8 * x) else 0) := by
  unfold muT
  rw [laneOf_xorBlock _ _ emptyState_size (by norm_num), laneOf_emptyState]
  split <;> simp_all

end MlDsaOptGlam44.Proofs.Alt
