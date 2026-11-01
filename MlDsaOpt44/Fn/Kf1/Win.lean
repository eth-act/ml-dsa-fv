import MlDsaOpt44.Fn.Kf1.Model
/-!
# `kf1`: words versus lanes on bit windows

`WinU lo hi w u`: the word `w` agrees with the replicated lane `rep u` on the
bit window `[lo, hi)` (bit `i` of `w` is bit `i mod 64` of `u`). Bitwise
operations keep windows, a left shift by `d` is a rotation by `d` on the window
shifted up by `d` (the decaying windows of `scripts/opt_keccak.py`).

`win_round`: one round of the word model on words valid on `[l, 256)` computes
the lane mirror `roundL` on `[l + 63, 256)` (theta's `SHL 1`, then rho by a left
shift of at most 62); three rounds from full windows leave `[189, 256) ⊇
[192, 256)` (`decay_windows(3, -1)`), which `rerep_toNat` re-replicates.
-/

namespace MlDsaOpt44.Proofs.Kf1

open EvmSemantics
open EvmSemantics.Crypto.Keccak

/-- `w` agrees with `rep u` on bits `[lo, hi)`. -/
def WinU (lo hi : Nat) (w : UInt256) (u : UInt64) : Prop :=
  ∀ i, lo ≤ i → i < hi → i < 256 → w.toNat.testBit i = u.toNat.testBit (i % 64)

theorem WinU.mono {lo hi lo' hi' : Nat} {w : UInt256} {u : UInt64} (h : WinU lo hi w u)
    (hl : lo ≤ lo') (hh : hi' ≤ hi) : WinU lo' hi' w u :=
  fun i h1 h2 h3 => h i (by omega) (by omega) h3

theorem WinU.xor {l h : Nat} {a b : UInt256} {u v : UInt64} (ha : WinU l h a u)
    (hb : WinU l h b v) : WinU l h (a.xor b) (u ^^^ v) := by
  intro i h1 h2 h3
  rw [EvmProof.Word.word_toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    ha i h1 h2 h3, hb i h1 h2 h3]

theorem WinU.land {l h : Nat} {a b : UInt256} {u v : UInt64} (ha : WinU l h a u)
    (hb : WinU l h b v) : WinU l h (UInt256.land a b) (u &&& v) := by
  intro i h1 h2 h3
  rw [EvmProof.Word.word_toNat_land, UInt64.toNat_and, Nat.testBit_and, Nat.testBit_and,
    ha i h1 h2 h3, hb i h1 h2 h3]

theorem WinU.lor {l h : Nat} {a b : UInt256} {u v : UInt64} (ha : WinU l h a u)
    (hb : WinU l h b v) : WinU l h (UInt256.lor a b) (u ||| v) := by
  intro i h1 h2 h3
  rw [EvmProof.Word.word_toNat_lor, UInt64.toNat_or, Nat.testBit_or, Nat.testBit_or,
    ha i h1 h2 h3, hb i h1 h2 h3]

theorem toNat_lnot (a : UInt256) : (UInt256.lnot a).toNat = 2 ^ 256 - (a.toNat + 1) := by
  have := a.val.isLt
  unfold UInt256.lnot
  rw [EvmProof.Word.word_toNat_ofNat]
  simp only [UInt256.size] at this ⊢
  change (2 ^ 256 - 1 - a.val.val) % 2 ^ 256 = 2 ^ 256 - (a.val.val + 1)
  omega

theorem WinU.lnot {l h : Nat} {a : UInt256} {u : UInt64} (ha : WinU l h a u) :
    WinU l h (UInt256.lnot a) (~~~u) := by
  intro i h1 h2 h3
  have hu := u.toNat_lt
  have hav : a.toNat < 2 ^ 256 := a.val.isLt
  rw [toNat_lnot, UInt64.toNat_not, show UInt64.size - 1 - u.toNat = 2 ^ 64 - (u.toNat + 1) by
      simp only [UInt64.size]; omega,
    Nat.testBit_two_pow_sub_succ hav, Nat.testBit_two_pow_sub_succ hu, ha i h1 h2 h3]
  simp [h3, Nat.mod_lt i (by decide : 64 > 0)]

theorem rotl64_testBit (u : UInt64) {n k : Nat} (hn : n < 64) (hk : k < 64) :
    (rotl64 u n).toNat.testBit k = u.toNat.testBit ((k + 64 - n) % 64) := by
  unfold rotl64
  split
  · subst n; congr 1; omega
  · have hu := u.toNat_lt
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
      UInt64.toNat_ofNat', Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.mod_eq_of_lt (show n % 2 ^ 64 < 64 by omega),
      Nat.mod_eq_of_lt (show (64 - n) % 2 ^ 64 < 64 by omega), Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 64 - n < 2 ^ 64)]
    by_cases hkn : n ≤ k
    · have h1 : u.toNat.testBit (64 - n + k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [h1, Bool.or_false, show (k + 64 - n) % 64 = k - n by omega]
      simp [hk, hkn]
    · rw [show (k + 64 - n) % 64 = 64 - n + k by omega]
      simp [hkn]

theorem rotl64_zero (u : UInt64) : rotl64 u 0 = u := by simp [rotl64]

theorem WinU.shl {l h : Nat} {a : UInt256} {u : UInt64} (d : Nat) (hd : d < 64)
    (ha : WinU l h a u) : WinU (l + d) (h + d) (a.shiftLeft (UInt256.ofNat d)) (rotl64 u d) := by
  intro i h1 h2 h3
  rw [EvmProof.Word.shiftLeft_toNat _ (by omega), Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    rotl64_testBit u hd (Nat.mod_lt i (by decide)), ha (i - d) (by omega) (by omega) (by omega)]
  simp only [h3, decide_true, Bool.true_and, show d ≤ i by omega]
  congr 1; omega

/-! ## The round -/

theorem win_C {l h : Nat} {A : Nat → UInt256} {s : Nat → UInt64}
    (hA : ∀ j, j < 25 → WinU l h (A j) (s j)) {x : Nat} (hx : x < 5) :
    WinU l h (Cw A x) (CL s x) :=
  (hA _ (by omega)).xor ((hA _ (by omega)).xor ((hA _ (by omega)).xor
    ((hA _ (by omega)).xor (hA _ (by omega)))))

theorem win_sh1 {l h : Nat} {a : UInt256} {u : UInt64} (ha : WinU l h a u) :
    WinU (l + 1) h (sh1 a) (rotl64 u 1) :=
  (ha.shl 1 (by decide)).mono le_rfl (by omega)

theorem win_D {l h : Nat} {C : Nat → UInt256} {Cl : Nat → UInt64}
    (hC : ∀ x, x < 5 → WinU l h (C x) (Cl x)) {x : Nat} (hx : x < 5) :
    WinU (l + 1) h (Dw C x) (DL Cl x) := by
  have m : ∀ x, x < 5 → WinU (l + 1) h (C x) (Cl x) := fun x hx =>
    (hC x hx).mono (by omega) le_rfl
  interval_cases x
  · exact (win_sh1 (hC 1 (by decide))).xor (m 4 (by decide))
  · exact (win_sh1 (hC 2 (by decide))).xor (m 0 (by decide))
  · exact (win_sh1 (hC 3 (by decide))).xor (m 1 (by decide))
  · exact (m 2 (by decide)).xor (win_sh1 (hC 4 (by decide)))
  · exact (win_sh1 (hC 0 (by decide))).xor (m 3 (by decide))

theorem win_shl {l : Nat} {a : UInt256} {u : UInt64} (d : Nat) (hd : d ≤ 62)
    (ha : WinU (l + 1) 256 a u) :
    WinU (l + 63) 256 (a.shiftLeft (UInt256.ofNat d)) (rotl64 u d) :=
  (ha.shl d (by omega)).mono (by omega) (by omega)

theorem win_shf {l : Nat} {a : UInt256} {u : UInt64} (ha : WinU (l + 1) 256 a u)
    {j : Nat} (hj : j < 25) :
    WinU (l + 63) 256 (shf j a) (rotl64 u rotOff[j]!) := by
  interval_cases j
  · rw [show rotOff[0]! = 0 from rfl, rotl64_zero]; exact ha.mono (by omega) le_rfl
  · exact win_shl 1 (by decide) ha
  · exact win_shl 62 (by decide) ha
  · exact win_shl 28 (by decide) ha
  · exact win_shl 27 (by decide) ha
  · exact win_shl 36 (by decide) ha
  · exact win_shl 44 (by decide) ha
  · exact win_shl 6 (by decide) ha
  · exact win_shl 55 (by decide) ha
  · exact win_shl 20 (by decide) ha
  · exact win_shl 3 (by decide) ha
  · exact win_shl 10 (by decide) ha
  · exact win_shl 43 (by decide) ha
  · exact win_shl 25 (by decide) ha
  · exact win_shl 39 (by decide) ha
  · exact win_shl 41 (by decide) ha
  · exact win_shl 45 (by decide) ha
  · exact win_shl 15 (by decide) ha
  · exact win_shl 21 (by decide) ha
  · exact win_shl 8 (by decide) ha
  · exact win_shl 18 (by decide) ha
  · exact win_shl 2 (by decide) ha
  · exact win_shl 61 (by decide) ha
  · exact win_shl 56 (by decide) ha
  · exact win_shl 14 (by decide) ha

theorem win_B {l : Nat} {A D : Nat → UInt256} {s Dl : Nat → UInt64}
    (hA : ∀ j, j < 25 → WinU l 256 (A j) (s j)) (hD : ∀ x, x < 5 → WinU (l + 1) 256 (D x) (Dl x))
    {j : Nat} (hj : j < 25) : WinU (l + 63) 256 (Bw A D j) (BL s Dl j) :=
  win_shf ((hD _ (Nat.mod_lt j (by decide))).xor ((hA j hj).mono (by omega) le_rfl)) hj

theorem win_chi {l h : Nat} {B : Nat → UInt256} {Bl : Nat → UInt64}
    (hB : ∀ k, k < 5 → WinU l h (B k) (Bl k)) {j : Nat} (hj : j < 25) :
    WinU l h (chiW j B) (chiL j Bl) := by
  have h0 := hB 0 (by decide)
  have h1 := hB 1 (by decide)
  have h2 := hB 2 (by decide)
  have h3 := hB 3 (by decide)
  have h4 := hB 4 (by decide)
  interval_cases j <;> simp only [chiW, chiL] <;>
    repeat' with_reducible first
      | exact h0 | exact h1 | exact h2 | exact h3 | exact h4
      | apply WinU.xor | apply WinU.lor | apply WinU.land | apply WinU.lnot

theorem srcLane_lt {y k : Nat} (hk : k < 5) : srcLane y k < 25 := by
  unfold srcLane; have := Nat.mod_lt (k + 3 * y) (show 5 > 0 by decide); omega

/-- One round of the word model computes the lane mirror on the shrunken window. -/
theorem win_round {l : Nat} {A : Nat → UInt256} {s : Nat → UInt64}
    (hA : ∀ j, j < 25 → WinU l 256 (A j) (s j)) {rc : UInt256} {rcl : UInt64}
    (hrc : WinU 0 256 rc rcl) {j : Nat} (hj : j < 25) :
    WinU (l + 63) 256 (roundW A rc j) (roundL s rcl j) := by
  have hD : ∀ x, x < 5 → WinU (l + 1) 256 (Dw (Cw A) x) (DL (CL s) x) := fun x hx =>
    win_D (fun x hx => win_C hA hx) hx
  have hchi : ∀ y, WinU (l + 63) 256 (chiW j fun k => Bw A (Dw (Cw A)) (srcLane y k))
      (chiL j fun k => BL s (DL (CL s)) (srcLane y k)) := fun y =>
    win_chi (fun k hk => win_B hA hD (srcLane_lt hk)) hj
  unfold roundW roundL outW outL
  split
  · subst j; exact (hrc.mono (by omega) le_rfl).xor (hchi 0)
  · exact hchi _

/-! ## Replication -/

theorem testBit_rep {n : Nat} (hn : n < 2 ^ 64) {i : Nat} (hi : i < 256) :
    (rep n).testBit i = n.testBit (i % 64) := by
  have e : rep n = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * n + n) + n) + n := by
    simp only [rep, REP, pack4]; ring
  rw [e]
  rw [Nat.testBit_two_pow_mul_add _ hn]
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ hn]
    split
    · rw [show i - 64 = i % 64 by omega]
    · rw [Nat.testBit_two_pow_mul_add _ hn]
      split
      · rw [show i - 64 - 64 = i % 64 by omega]
      · rw [show i - 64 - 64 - 64 = i % 64 by omega]

theorem rep_eq (n : Nat) :
    rep n = 6277101735386680764176071790128604879584176795969512275969 * n := by
  simp only [rep, REP, pack4]; ring

theorem rep_lt {n : Nat} (hn : n < 2 ^ 64) : rep n < 2 ^ 256 := by
  rw [rep_eq]; omega

theorem win_rep (u : UInt64) : WinU 0 256 (UInt256.ofNat (rep u.toNat)) u := by
  intro i _ _ h3
  rw [EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (rep_lt u.toNat_lt),
    testBit_rep u.toNat_lt h3]

theorem rerep_toNat {l : Nat} {o : UInt256} {u : UInt64} (hw : WinU l 256 o u) (hl : l ≤ 192) :
    (rerepW o).toNat = rep u.toNat := by
  have hu := u.toNat_lt
  have ho : o.toNat < 2 ^ 256 := o.val.isLt
  have hx : o.toNat >>> 192 = u.toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight]
    by_cases hi : i < 64
    · rw [hw (192 + i) (by omega) (by omega) (by omega)]
      congr 1; omega
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide) (by omega)))]
  unfold rerepW REPw
  rw [EvmProof.Word.word_toNat_mul, EvmProof.Word.shiftRight_toNat _ (by decide),
    EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : (6277101735386680764176071790128604879584176795969512275969 : Nat) < 2 ^ 256),
    hx, ← rep_eq]
  exact Nat.mod_eq_of_lt (rep_lt hu)

end MlDsaOpt44.Proofs.Kf1
