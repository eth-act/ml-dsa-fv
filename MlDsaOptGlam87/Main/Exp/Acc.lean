import MlDsaOptGlam87.Main.Exp.Sponge
import MlDsaOptGlam87.Fn.Group
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Exp/Acc.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# Accumulation math and boundary predicates of ExpandA (ML-DSA-87, v4)

* `InvE`: what every ExpandA boundary keeps (tables, `ẑ`, `ρ`, zero scratch);
* `ColAt` / `Col3At` / `Row7At`: a column of `A` (all four rows, rows 4–6, or
  row 7 columns 6…3) in the lanes of an 8 KB buffer, when `A` exists;
* `Acc0` / `Acc1`: the accumulator tables as exact lane sums (`accSum`);
* `acc0_p3f4`, `acc0_p3f6`, `acc1_p3f10`, `fin_p3f14`: the fused passes' words
  (`p3f4Word` … `p3f14Word`) as those sums; `accAt_of`: `AccAt` from the sums
  over all seven columns (v3 `Main/S5/Acc.lean`);
* `flags_okA`: the fifteen group flags make `okA`.
-/

namespace MlDsaOptGlam87.Proofs.Exp

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt44.Proofs (pack4_lt lane_pack4 getElem!_map_range)
open MlDsaOptGlam87.Proofs MlDsaOpt87.Proofs

/-! ## Boundary invariant -/

/-- What every ExpandA boundary keeps. -/
structure InvE (cd m : ByteArray) : Prop where
  rc4 : RC4Table m
  rc1 : RC1Table m
  tbl : TblAt m
  zhat : ZHatAt m cd
  rho : Rho1At m cd
  zBases : ZeroOn m BASES (BASES + 2048)
  zIdx : ZeroOn m IDX (IDX + 256)
  zNeg : ZeroOn m NNEG (NNEG + 64)

theorem InvE.frame {cd m m' : ByteArray} {rs : List (Nat × Nat)} (h : InvE cd m)
    (hf : FrameExcept m m' rs) (h1 : Avoids rs RC4 (NNEG + 64)) (h2 : Avoids rs TBL (TBL + 7936))
    (h3 : Avoids rs ZH (IDX + 256)) (h4 : Avoids rs RHO1 (RHO1 + 128)) : InvE cd m' where
  rc4 := RC4Table.frame h.rc4 hf (h1.mono (le_refl _) (by unfold RC4 NNEG; omega))
  rc1 := RC1Table.frame h.rc1 hf (h1.mono (by unfold RC4 RC1; omega) (by unfold RC1 NNEG; omega))
  tbl := TblAt.frame h.tbl hf h2
  zhat := ZHatAt.frame h.zhat hf (h3.mono (le_refl _) (by unfold ZH IDX; omega))
  rho := Rho1At.frame h.rho hf h4
  zBases := ZeroOn.frame h.zBases hf (h3.mono (by unfold ZH BASES; omega) (by unfold BASES IDX; omega))
  zIdx := ZeroOn.frame h.zIdx hf (h3.mono (by unfold ZH IDX; omega) (le_refl _))
  zNeg := ZeroOn.frame h.zNeg hf (h1.mono (by unfold RC4 NNEG; omega) (le_refl _))

/-- `Avoids` for literal layout ranges, `groupFrame` unfolded. -/
macro "exp_av" : tactic => `(tactic| (
  (try simp only [MlDsaOpt87.Proofs.groupFrame, List.cons_append, List.nil_append, List.append_assoc])
  avoids_tac))

/-- Transport `InvE` across a frame of literal layout ranges. -/
macro "inve_frame" h:term:max hf:term:max : term =>
  `(InvE.frame $h $hf (by exp_av) (by exp_av) (by exp_av) (by exp_av))

theorem invE_of_inv4 {cd m : ByteArray} (h : Inv4 cd m) : InvE cd m where
  rc4 := h.rc4
  rc1 := h.rc1
  tbl := h.tbl
  zhat := h.zhat
  rho := h.rho
  zBases := ZeroOn.mono h.zHigh (le_refl _) (by unfold BASES FIN; omega)
  zIdx := ZeroOn.mono h.zHigh (by unfold BASES IDX; omega) (by unfold IDX FIN; omega)
  zNeg := ZeroOn.mono h.zMisc (by unfold MISC NNEG; omega) (by unfold NNEG TBL; omega)

/-! ## Entries of `A` -/

theorem okA_get {cd : ByteArray} (h : okA cd = true) {r s : Nat} (hr : r < 8) (hs : s < 7) :
    (aOf cd r s).isSome = true := by
  unfold okA at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr hr)
  rw [List.all_eq_true] at this
  exact this s (List.mem_range.mpr hs)

theorem aD_lt (cd : ByteArray) (r s : Nat) {t : Nat} (ht : t < 256) :
    ((aD cd r s)[t]!).toNat < 2 ^ 23 := by
  unfold aD
  cases h : aOf cd r s with
  | none => simp [MlDsa.Fips204.zeroPoly, ht]
  | some a =>
    simp only [Option.getD_some]
    have := ((MlDsaOpt87.Proofs.rejNTTPoly_range _ a h).2 t ht)
    have hq : (MlDsa.Fips204.q : Int) = 8380417 := rfl
    omega

theorem aD_of_some {cd : ByteArray} {r s : Nat} {a : Fips204.Poly} (h : aOf cd r s = some a) :
    aD cd r s = a := by
  unfold aD; rw [h]; rfl

theorem gOk_of_okA {cd : ByteArray} (h : okA cd = true) {col rb : Nat} (hcol : col < 7) (hrb : rb < 2) :
    gOk cd 15 col rb = true := by
  unfold gOk
  rw [List.all_eq_true]
  intro r hr
  have := List.mem_range.mp hr
  rw [okA_get h (by omega) hcol, Bool.or_true]

/-! ## Columns in buffers -/

/-- Rows `4 rb … 4 rb + 3` of column `col` in the lanes of the buffer at `dst`. -/
def ColAt (m : ByteArray) (cd : ByteArray) (dst rb col : Nat) : Prop :=
  okA cd = true → ∀ t, t < 256 →
    word m (dst + 32 * t) = pack4 fun r => ((aD cd (4 * rb + r) col)[t]!).toNat

/-- Rows 4–6 of column `col` in lanes 0–2 of the buffer at `dst`. -/
def Col3At (m : ByteArray) (cd : ByteArray) (dst col : Nat) : Prop :=
  okA cd = true → ∀ t, t < 256 → ∀ r, r < 3 →
    lane (word m (dst + 32 * t)) r = ((aD cd (4 + r) col)[t]!).toNat

/-- Row 7, column `6 − k` in lane `k` of `ABUF` (group 14). -/
def Row7At (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true → ∀ t, t < 256 → ∀ k, k < 4 →
    lane (word m (ABUF + 32 * t)) k = ((aD cd 7 (6 - k))[t]!).toNat

theorem ColAt.frame {m m' cd : ByteArray} {rs : List (Nat × Nat)} {dst rb col : Nat}
    (h : ColAt m cd dst rb col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    ColAt m' cd dst rb col := fun hok t ht => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht

theorem Col3At.frame {m m' cd : ByteArray} {rs : List (Nat × Nat)} {dst col : Nat}
    (h : Col3At m cd dst col) (hf : FrameExcept m m' rs) (ha : Avoids rs dst (dst + 8192)) :
    Col3At m' cd dst col := fun hok t ht => by
  rw [word_frame hf ha (a := dst + 32 * t) (by omega) (by omega)]; exact h hok t ht

/-- The post of `group [15, col, rb]` as a column of `ABUF`. -/
theorem colAt_group {m cd : ByteArray} {col rb : Nat} (hcol : col < 7) (hrb : rb < 2)
    (hpost : gOk cd 15 col rb = true →
      ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m (ABUF + 32 * t) =
          pack4 (fun r => if (15 : Nat).testBit r then
            ((aD cd (4 * rb + r) col)[t]!).toNat else junk r t)) :
    ColAt m cd ABUF rb col := fun hok t ht => by
  obtain ⟨junk, -, hw⟩ := hpost (gOk_of_okA hok hcol hrb)
  rw [hw t ht]
  exact pack4_congr fun r hr => by
    rw [if_pos (by interval_cases r <;> decide)]

/-- An `MCOPY` of `ABUF[0, 8192)` to `dst` copies its column facts. -/
theorem colAt_mcopy {m cd : ByteArray} {dst rb col : Nat} (h : ColAt m cd ABUF rb col) :
    ColAt (MachineState.writeBytes m (MachineState.readPadded m ABUF 8192) dst) cd dst rb col :=
  fun hok t ht => by
    rw [word_mcopy _ (by omega) (by omega), show ABUF + (dst + 32 * t - dst) = ABUF + 32 * t by omega]
    exact h hok t ht

theorem col3At_mcopy {m cd : ByteArray} {dst col : Nat} (h : Col3At m cd ABUF col) :
    Col3At (MachineState.writeBytes m (MachineState.readPadded m ABUF 8192) dst) cd dst col :=
  fun hok t ht => by
    rw [word_mcopy _ (by omega) (by omega), show ABUF + (dst + 32 * t - dst) = ABUF + 32 * t by omega]
    exact h hok t ht

/-! ## Accumulator sums -/

theorem accSum_congr {cd m m' : ByteArray} {r t : Nat} :
    ∀ n, (∀ k, k < n → zhLane m' k t = zhLane m k t) → accSum cd m' r t n = accSum cd m r t n
  | 0, _ => rfl
  | n + 1, h => by
    show accSum cd m' r t n + _ * zhLane m' n t = accSum cd m r t n + _ * zhLane m n t
    rw [accSum_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem accSum_le {cd m : ByteArray} {r t : Nat} (ht : t < 256)
    (hz : ∀ k, k < 7 → zhLane m k t < 2 ^ 28) : ∀ n, n ≤ 7 → accSum cd m r t n ≤ n * 2 ^ 51
  | 0, _ => Nat.le_refl _
  | n + 1, hn => by
    have ih := accSum_le (cd := cd) (r := r) ht hz n (by omega)
    have h3 : ((aD cd r n)[t]!).toNat * zhLane m n t < 2 ^ 23 * 2 ^ 28 :=
      Nat.mul_lt_mul'' (aD_lt cd r n ht) (hz n (by omega))
    have e : (n + 1) * 2 ^ 51 = n * 2 ^ 51 + 2 ^ 51 := by ring
    show accSum cd m r t n + _ ≤ _
    omega

/-- Rows 0–3 of `Â ẑ` after the columns `s < n`, in `ACC`. -/
def Acc0 (m : ByteArray) (cd : ByteArray) (n : Nat) : Prop :=
  okA cd = true → ∀ t, t < 256 → word m (ACC + 32 * t) = pack4 fun j => accSum cd m j t n

/-- Rows 4–6 after columns `0 … 3`, row 7 after columns `0 … 2`, in `ACC + 0x2000`. -/
def Acc1 (m : ByteArray) (cd : ByteArray) : Prop :=
  okA cd = true → ∀ t, t < 256 →
    word m (ACC + 8192 + 32 * t) = pack4 fun j => accSum cd m (4 + j) t (if j < 3 then 4 else 3)

theorem Acc0.frame {m m' cd : ByteArray} {rs : List (Nat × Nat)} {n : Nat} (h : Acc0 m cd n)
    (hn : n ≤ 7) (hf : FrameExcept m m' rs) (ha : Avoids rs ACC (ACC + 8192)) (hz : Avoids rs ZH (ZH + 0x4000)) :
    Acc0 m' cd n := fun hok t ht => by
  rw [word_frame hf ha (a := ACC + 32 * t) (by omega) (by omega), h hok t ht]
  exact pack4_congr fun j _ =>
    (accSum_congr n fun k hk => zhLane_frame hf hz (by omega) ht).symm

theorem Acc1.frame {m m' cd : ByteArray} {rs : List (Nat × Nat)} (h : Acc1 m cd)
    (hf : FrameExcept m m' rs) (ha : Avoids rs (ACC + 8192) (ACC + 8192 + 8192))
    (hz : Avoids rs ZH (ZH + 0x4000)) : Acc1 m' cd := fun hok t ht => by
  rw [word_frame hf ha (a := ACC + 8192 + 32 * t) (by omega) (by omega), h hok t ht]
  exact pack4_congr fun j _ =>
    (accSum_congr _ fun k hk => zhLane_frame hf hz (by split at hk <;> omega) ht).symm

/-! ## Lane arithmetic -/

theorem pack4_mul (a : Nat → Nat) (z : Nat) : pack4 a * z = pack4 fun r => a r * z := by
  unfold pack4; ring

theorem pack4_add (a b : Nat → Nat) : pack4 a + pack4 b = pack4 fun r => a r + b r := by
  unfold pack4; ring

theorem zl_eq (m : ByteArray) (j t : Nat) : zl m j t = zhLane m j t := rfl

theorem mul_lt51 {a b : Nat} (ha : a < 2 ^ 23) (hb : b < 2 ^ 28) : a * b < 2 ^ 51 :=
  lt_of_lt_of_le (Nat.mul_lt_mul'' ha hb) (by norm_num)

theorem bz_col {m cd : ByteArray} {b rb j t : Nat} (h : ColAt m cd b rb j) (hok : okA cd = true)
    (ht : t < 256) :
    bz m b j t = pack4 fun r => ((aD cd (4 * rb + r) j)[t]!).toNat * zhLane m j t := by
  unfold bz; rw [h hok t ht, pack4_mul, zl_eq]

theorem and_low3 (w : Nat) : w &&& (2 ^ 192 - 1) = pack4 fun r => if r < 3 then lane w r else 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  unfold pack4 lane
  simp only [show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide,
    show (2 : Nat) < 3 by decide, if_true, show ¬ (3 : Nat) < 3 by decide, if_false]
  norm_num
  omega

theorem bzl_col3 {m cd : ByteArray} {b j t : Nat} (h : Col3At m cd b j) (hok : okA cd = true)
    (ht : t < 256) :
    bzl m b (2 ^ 192 - 1) 0 j t =
      pack4 fun r => (if r < 3 then ((aD cd (4 + r) j)[t]!).toNat else 0) * zhLane m j t := by
  unfold bzl
  rw [and_low3, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, zl_eq]
  have e : (pack4 fun r => if r < 3 then lane (word m (b + 32 * t)) r else 0) =
      pack4 fun r => if r < 3 then ((aD cd (4 + r) j)[t]!).toNat else 0 :=
    pack4_congr fun r _ => by split
                              · rw [h hok t ht r (by omega)]
                              · rfl
  rw [e, Nat.mod_eq_of_lt (pack4_lt fun r _ => by
    split
    · exact lt_trans (aD_lt cd _ _ ht) (by norm_num)
    · norm_num), pack4_mul]

theorem zh_lt {m cd : ByteArray} (hz : ZHatAt m cd) {t : Nat} (ht : t < 256) :
    ∀ k, k < 7 → zhLane m k t < 2 ^ 28 := fun k hk => (hz k hk t ht).1

/-! ## The fused passes -/

/-- `pass3f4`: `ACC` holds the sums over columns `0 … 4` of rows 0–3. -/
theorem acc0_p3f4 {m m' cd : ByteArray} (hz : ZHatAt m cd)
    (h0 : ColAt m cd CW 0 0) (h1 : ColAt m cd HP 0 1) (h2 : ColAt m cd (HP + 8192) 0 2)
    (h3 : ColAt m cd (ACC + 8192) 0 3) (h4 : ColAt m cd ABUF 0 4)
    (hw : ∀ t, t < 256 → word m' (ACC + 32 * t) = p3f4Word m t)
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : Acc0 m' cd 5 := by
  intro hok t ht
  have hzt := zh_lt hz ht
  rw [hw t ht]
  unfold p3f4Word
  rw [bz_col h0 hok ht, bz_col h1 hok ht, bz_col h2 hok ht, bz_col h3 hok ht, bz_col h4 hok ht,
    pack4_add, pack4_add, pack4_add, pack4_add]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (pack4_lt fun r _ => by
    have := mul_lt51 (aD_lt cd r 0 ht) (hzt 0 (by omega))
    have := mul_lt51 (aD_lt cd r 1 ht) (hzt 1 (by omega))
    have := mul_lt51 (aD_lt cd r 2 ht) (hzt 2 (by omega))
    have := mul_lt51 (aD_lt cd r 3 ht) (hzt 3 (by omega))
    have := mul_lt51 (aD_lt cd r 4 ht) (hzt 4 (by omega))
    omega)]
  refine pack4_congr fun j _ => ?_
  rw [accSum_congr 5 fun k hk => hzh k (by omega) t ht]
  simp only [accSum, Nat.zero_add]

/-- `pass3f6`: `ACC` gains columns 5 and 6. -/
theorem acc0_p3f6 {m m' cd : ByteArray} (hz : ZHatAt m cd) (hacc : Acc0 m cd 5)
    (h5 : ColAt m cd CW 0 5) (h6 : ColAt m cd ABUF 0 6)
    (hw : ∀ t, t < 256 → word m' (ACC + 32 * t) = p3f6Word m t)
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : Acc0 m' cd 7 := by
  intro hok t ht
  have hzt := zh_lt hz ht
  rw [hw t ht]
  unfold p3f6Word
  rw [hacc hok t ht, bz_col h5 hok ht, bz_col h6 hok ht, pack4_add, pack4_add]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (pack4_lt fun r _ => by
    have := accSum_le (cd := cd) (r := r) ht hzt 5 (by omega)
    have := mul_lt51 (aD_lt cd r 5 ht) (hzt 5 (by omega))
    have := mul_lt51 (aD_lt cd r 6 ht) (hzt 6 (by omega))
    omega)]
  refine pack4_congr fun j _ => ?_
  rw [accSum_congr 7 fun k hk => hzh k (by omega) t ht]
  simp only [accSum]

/-- `pass3f10`: `ACC + 0x2000` holds rows 4–7 of columns 0–2 and rows 4–6 of column 3. -/
theorem acc1_p3f10 {m m' cd : ByteArray} (hz : ZHatAt m cd)
    (h0 : ColAt m cd CW 1 0) (h1 : ColAt m cd HP 1 1) (h2 : ColAt m cd (HP + 8192) 1 2)
    (h3 : Col3At m cd ABUF 3)
    (hw : ∀ t, t < 256 → word m' (ACC + 8192 + 32 * t) = p3f10Word m t)
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) : Acc1 m' cd := by
  intro hok t ht
  have hzt := zh_lt hz ht
  rw [hw t ht]
  unfold p3f10Word
  rw [bz_col h0 hok ht, bz_col h1 hok ht, bz_col h2 hok ht, bzl_col3 h3 hok ht,
    pack4_add, pack4_add, pack4_add]
  rw [Nat.mod_eq_of_lt (pack4_lt fun r _ => by
    have := mul_lt51 (aD_lt cd (4 * 1 + r) 0 ht) (hzt 0 (by omega))
    have := mul_lt51 (aD_lt cd (4 * 1 + r) 1 ht) (hzt 1 (by omega))
    have := mul_lt51 (aD_lt cd (4 * 1 + r) 2 ht) (hzt 2 (by omega))
    have : (if r < 3 then ((aD cd (4 + r) 3)[t]!).toNat else 0) * zhLane m 3 t < 2 ^ 51 := by
      split
      · exact mul_lt51 (aD_lt cd _ 3 ht) (hzt 3 (by omega))
      · simp
    omega)]
  refine pack4_congr fun j hj => ?_
  rw [accSum_congr _ fun k hk => hzh k (by split at hk <;> omega) t ht]
  rw [show 4 * 1 + j = 4 + j by omega]
  rcases (by omega : j < 3 ∨ j = 3) with h3 | rfl
  · rw [if_pos h3, if_pos h3]; show _ = 0 + _ + _ + _ + _; rw [Nat.zero_add]
  · rw [if_neg (by decide), if_neg (by decide), Nat.zero_mul, Nat.add_zero]
    show _ = 0 + _ + _ + _; rw [Nat.zero_add]

theorem and_high {w n k : Nat} (hw : w < 2 ^ n) (hk : k ≤ n) :
    w &&& (2 ^ n - 2 ^ k) = 2 ^ k * (w / 2 ^ k) := by
  have e : 2 ^ n - 2 ^ k = 2 ^ k * (2 ^ (n - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : j ≥ k
  · rw [show j - k + k = j by omega]
    by_cases hjn : j < n
    · simp [hj, show j - k < n - k by omega]
    · have : w.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this]
  · simp [hj]

theorem or_eq_add {a : Nat} (c : Nat) (h : a < 2 ^ 64) : a ||| 2 ^ 64 * c = a + 2 ^ 64 * c := by
  rw [Nat.or_comm, show 2 ^ 64 * c = c <<< 64 by rw [Nat.shiftLeft_eq, Nat.mul_comm],
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  omega

/-- Lane 3 of the Kronecker product of group 14: `Σ_i w_i · y_{3 − i}` with
`y = (lane 3 of zl, lanes 0–2 of zh)`. -/
theorem kron {w zl zh : Nat} (hw : w < 2 ^ 256) (hzl : zl < 2 ^ 256)
    (ha : ∀ k, k < 4 → lane w k < 2 ^ 23) (hz3 : lane zl 3 < 2 ^ 28)
    (hz : ∀ k, k < 3 → lane zh k < 2 ^ 28) :
    w * (zl / 2 ^ 192 ||| zh * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&& (M64 * 2 ^ 192) =
      2 ^ 192 * (lane w 0 * lane zh 2 + lane w 1 * lane zh 1 + lane w 2 * lane zh 0 +
        lane w 3 * lane zl 3) := by
  have hw' : w = lane w 0 + 2 ^ 64 * lane w 1 + 2 ^ 128 * lane w 2 + 2 ^ 192 * lane w 3 := by
    unfold lane; norm_num at hw ⊢; omega
  have hzl' : zl / 2 ^ 192 = lane zl 3 := by
    unfold lane; norm_num at hzl ⊢; omega
  have hzh' : zh * 2 ^ 64 % 2 ^ 256 = 2 ^ 64 * (lane zh 0 + 2 ^ 64 * lane zh 1 + 2 ^ 128 * lane zh 2) := by
    have e : zh * 2 ^ 64 % 2 ^ 256 = 2 ^ 64 * (zh % 2 ^ 192) := by
      rw [Nat.mul_comm, show (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 192 by norm_num, Nat.mul_mod_mul_left]
    rw [e]
    congr 1
    unfold lane; norm_num; omega
  have h3 : lane zl 3 < 2 ^ 64 := Nat.lt_trans hz3 (by norm_num)
  rw [hzl', hzh', or_eq_add _ h3]
  have hw0 := ha 0 (by omega); have hw1 := ha 1 (by omega)
  have hw2 := ha 2 (by omega); have hw3 := ha 3 (by omega)
  have hz0 := hz 0 (by omega); have hz1 := hz 1 (by omega); have hz2 := hz 2 (by omega)
  generalize lane w 0 = a0 at *
  generalize lane w 1 = a1 at *
  generalize lane w 2 = a2 at *
  generalize lane w 3 = a3 at *
  generalize lane zh 0 = y1 at *
  generalize lane zh 1 = y2 at *
  generalize lane zh 2 = y3 at *
  generalize lane zl 3 = y0 at *
  subst hw'
  have m00 : a0 * y0 < 2 ^ 51 := mul_lt51 hw0 hz3
  have q01 := mul_lt51 hw0 hz0; have q10 := mul_lt51 hw1 hz3
  have q02 := mul_lt51 hw0 hz1; have q11 := mul_lt51 hw1 hz0; have q20 := mul_lt51 hw2 hz3
  have q03 := mul_lt51 hw0 hz2; have q12 := mul_lt51 hw1 hz1; have q21 := mul_lt51 hw2 hz0
  have q30 := mul_lt51 hw3 hz3
  generalize hL : a0 * y0 + 2 ^ 64 * (a0 * y1 + a1 * y0) + 2 ^ 128 * (a0 * y2 + a1 * y1 + a2 * y0) = L
  generalize hK : a0 * y3 + a1 * y2 + a2 * y1 + a3 * y0 = K
  have e : (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3) * (y0 + 2 ^ 64 * (y1 + 2 ^ 64 * y2 +
      2 ^ 128 * y3)) = (L + 2 ^ 192 * K) + 2 ^ 256 * (a1 * y3 + a2 * y2 + a3 * y1 +
        2 ^ 64 * (a2 * y3 + a3 * y2) + 2 ^ 128 * (a3 * y3)) := by
    rw [← hL, ← hK]; ring
  have hLlt : L < 2 ^ 192 := by rw [← hL]; norm_num at m00 q01 q10 q02 q11 q20 ⊢; omega
  have hKlt : K < 2 ^ 64 := by rw [← hK]; norm_num at q03 q12 q21 q30 ⊢; omega
  have hlt : L + 2 ^ 192 * K < 2 ^ 256 := by norm_num at hLlt hKlt ⊢; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
    show M64 * 2 ^ 192 = 2 ^ 256 - 2 ^ 192 by unfold M64; norm_num, and_high hlt (by norm_num)]
  congr 1
  norm_num at hLlt ⊢
  omega

theorem accSum_7_4 (cd m : ByteArray) (r t : Nat) : accSum cd m r t 7 = accSum cd m r t 4 +
    ((aD cd r 4)[t]!).toNat * zhLane m 4 t + ((aD cd r 5)[t]!).toNat * zhLane m 5 t +
    ((aD cd r 6)[t]!).toNat * zhLane m 6 t := rfl

theorem accSum_7_3 (cd m : ByteArray) (r t : Nat) : accSum cd m r t 7 = accSum cd m r t 3 +
    ((aD cd r 3)[t]!).toNat * zhLane m 3 t + ((aD cd r 4)[t]!).toNat * zhLane m 4 t +
    ((aD cd r 5)[t]!).toNat * zhLane m 5 t + ((aD cd r 6)[t]!).toNat * zhLane m 6 t := rfl

/-- The lane arithmetic of `pass3f14` over abstract sums. -/
theorem fin_lane (F : Nat → Nat → Nat) (a : Nat → Nat → Nat) (z : Nat → Nat)
    (h4 : ∀ r, F r 7 = F r 4 + a r 4 * z 4 + a r 5 * z 5 + a r 6 * z 6)
    (h3 : ∀ r, F r 7 = F r 3 + a r 3 * z 3 + a r 4 * z 4 + a r 5 * z 5 + a r 6 * z 6) :
    ∀ j, j < 4 →
      F (4 + j) (if j < 3 then 4 else 3) + (if j < 3 then a (4 + j) 4 else 0) * z 4 +
        (if j < 3 then a (4 + j) 5 else 0) * z 5 + (if j < 3 then a (4 + j) 6 else 0) * z 6 +
        (if j = 3 then a 7 (6 - 0) * z (4 + 2) + a 7 (6 - 1) * z (4 + 1) + a 7 (6 - 2) * z (4 + 0) +
          a 7 (6 - 3) * z 3 else 0) = F (4 * 1 + j) 7 := by
  intro j hj
  rw [show 4 * 1 + j = 4 + j by omega]
  rcases (by omega : j < 3 ∨ j = 3) with h | rfl
  · simp only [h, if_true, show j ≠ 3 by omega, if_false, Nat.add_zero]
    rw [h4]
  · simp only [show ¬ (3 : Nat) < 3 by decide, if_false, if_true, Nat.zero_mul, Nat.add_zero]
    rw [h3]
    simp only [Nat.reduceAdd, Nat.reduceSub]
    ring

/-- `pass3f14`: both accumulator tables hold the sums over all seven columns. -/
theorem fin_p3f14 {m m' cd : ByteArray} (hz : ZHatAt m cd) (hacc0 : Acc0 m cd 7) (hacc1 : Acc1 m cd)
    (h4 : Col3At m cd CW 4) (h5 : Col3At m cd HP 5) (h6 : Col3At m cd (HP + 8192) 6)
    (h7 : Row7At m cd)
    (hw : ∀ t, t < 256 → word m' (ACC + 8192 + 32 * t) = p3f14Word m t)
    (hw0 : ∀ t, t < 256 → word m' (ACC + 32 * t) = word m (ACC + 32 * t))
    (hzh : ∀ k, k < 7 → ∀ t, t < 256 → zhLane m' k t = zhLane m k t) :
    okA cd = true → ∀ g, g < 2 → ∀ t, t < 256 →
      word m' (ACC + 0x2000 * g + 32 * t) = pack4 fun j => accSum cd m' (4 * g + j) t 7 := by
  intro hok g hg t ht
  have hzt := zh_lt hz ht
  have hcg : ∀ j, accSum cd m' (4 * g + j) t 7 = accSum cd m (4 * g + j) t 7 := fun j =>
    accSum_congr 7 fun k hk => hzh k hk t ht
  simp only [hcg]
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    rw [hw0 t ht, hacc0 hok t ht]
  · rw [show ACC + 0x2000 * 1 + 32 * t = ACC + 8192 + 32 * t by omega, hw t ht]
    unfold p3f14Word kron14
    have hl7 := h7 hok t ht
    rw [kron (word_lt _ _) (word_lt _ _) (fun k hk => by rw [hl7 k hk]; exact aD_lt cd _ _ ht)
      (by have := hzt 3 (by omega); exact this)
      (fun k hk => by
        have := hzt (4 + k) (by omega)
        unfold zhLane zhAddr at this
        rwa [show (4 + k) / 4 = 1 by omega, show (4 + k) % 4 = k by omega] at this)]
    rw [hacc1 hok t ht, bzl_col3 h4 hok ht, bzl_col3 h5 hok ht, bzl_col3 h6 hok ht,
      hl7 0 (by omega), hl7 1 (by omega), hl7 2 (by omega), hl7 3 (by omega)]
    have e3 : lane (word m (ZH + 32 * t)) 3 = zhLane m 3 t := rfl
    have e4 : ∀ k, k < 3 → lane (word m (ZH + 8192 + 32 * t)) k = zhLane m (4 + k) t := fun k hk => by
      unfold zhLane zhAddr
      rw [show (4 + k) / 4 = 1 by omega, show (4 + k) % 4 = k by omega]
    rw [e3, e4 0 (by omega), e4 1 (by omega), e4 2 (by omega), pack4_add, pack4_add, pack4_add]
    have hK : ∀ v : Nat → Nat, pack4 v + 2 ^ 192 * ((aD cd 7 (6 - 0))[t]!.toNat * zhLane m (4 + 2) t +
        (aD cd 7 (6 - 1))[t]!.toNat * zhLane m (4 + 1) t + (aD cd 7 (6 - 2))[t]!.toNat * zhLane m (4 + 0) t +
        (aD cd 7 (6 - 3))[t]!.toNat * zhLane m 3 t) =
        pack4 fun j => v j + if j = 3 then ((aD cd 7 (6 - 0))[t]!.toNat * zhLane m (4 + 2) t +
        (aD cd 7 (6 - 1))[t]!.toNat * zhLane m (4 + 1) t + (aD cd 7 (6 - 2))[t]!.toNat * zhLane m (4 + 0) t +
        (aD cd 7 (6 - 3))[t]!.toNat * zhLane m 3 t) else 0 := fun v => by
      unfold pack4; simp only [show (0 : Nat) ≠ 3 by decide, show (1 : Nat) ≠ 3 by decide,
        show (2 : Nat) ≠ 3 by decide, if_false, if_true, Nat.add_zero]; ring
    rw [hK]
    have hb : ∀ j, j < 4 → (accSum cd m (4 + j) t 7) < 2 ^ 64 := fun j _ => by
      have := accSum_le (cd := cd) (r := 4 + j) ht hzt 7 le_rfl; omega
    have hlane := fin_lane (fun r n => accSum cd m r t n) (fun r s => ((aD cd r s)[t]!).toNat)
      (fun k => zhLane m k t) (fun r => accSum_7_4 cd m r t) (fun r => accSum_7_3 cd m r t)
    rw [pack4_congr hlane, Nat.mod_eq_of_lt (pack4_lt fun j hj => by
      have := hb j hj; rwa [show 4 * 1 + j = 4 + j by omega])]

/-! ## `AccAt` -/

theorem sum_range7 (f : Nat → Int) :
    ((List.range 7).map f).sum = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp [List.range_succ]; ring

/-- `AccAt` from the exact lane sums over all seven columns. -/
theorem accAt_of {cd m : ByteArray} (hzh : ZHatAt m cd)
    (hfin : okA cd = true → ∀ g, g < 2 → ∀ t, t < 256 →
      word m (ACC + 0x2000 * g + 32 * t) = pack4 fun j => accSum cd m (4 * g + j) t 7) :
    AccAt m cd := by
  intro hok
  have hle : ∀ r t, t < 256 → accSum cd m r t 7 ≤ 7 * 2 ^ 51 := fun r t ht =>
    accSum_le ht (fun k hk => (hzh k hk t ht).1) 7 le_rfl
  have hlt : ∀ g t, t < 256 → ∀ j, j < 4 → accSum cd m (4 * g + j) t 7 < 2 ^ 64 := fun g t ht j _ => by
    have := hle (4 * g + j) t ht; omega
  refine ⟨fun g hg k hk t ht => ?_, fun r hr t ht => ?_⟩
  · rw [hfin hok g hg t ht, lane_pack4 (hlt g t ht) hk]
    have := hle (4 * g + k) t ht; omega
  · have ha : accAddr r t = ACC + 0x2000 * (r / 4) + 32 * t := rfl
    rw [ha, hfin hok (r / 4) (by omega) t ht, lane_pack4 (hlt (r / 4) t ht) (Nat.mod_lt _ (by norm_num)),
      show 4 * (r / 4) + r % 4 = r by omega]
    have hnn : ∀ s, s < 7 → (((aD cd r s)[t]!).toNat : Int) = (aD cd r s)[t]! := fun s hs => by
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get hok hr hs)
      rw [aD_of_some ha]
      exact Int.toNat_of_nonneg ((MlDsaOpt87.Proofs.rejNTTPoly_range _ a ha).2 t ht).1
    have hm : ∀ s, s < 7 → (zhLane m s t : Int) % (Fips204.q : Int) =
        (zHat cd s)[t]! % (Fips204.q : Int) := fun s hs =>
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (hzh s hs t ht).2
    have hrow : (azRow cd r)[t]! = ((List.range 7).map fun s => (aD cd r s)[t]! * (zHat cd s)[t]!).sum %
        (Fips204.q : Int) := by
      unfold azRow; exact getElem!_map_range 256 t _ ht
    rw [hrow, sum_range7]
    have hsum : (accSum cd m r t 7 : Int) =
        (aD cd r 0)[t]! * (zhLane m 0 t : Int) + (aD cd r 1)[t]! * (zhLane m 1 t : Int) +
        (aD cd r 2)[t]! * (zhLane m 2 t : Int) + (aD cd r 3)[t]! * (zhLane m 3 t : Int) +
        (aD cd r 4)[t]! * (zhLane m 4 t : Int) + (aD cd r 5)[t]! * (zhLane m 5 t : Int) +
        (aD cd r 6)[t]! * (zhLane m 6 t : Int) := by
      rw [← hnn 0 (by omega), ← hnn 1 (by omega), ← hnn 2 (by omega), ← hnn 3 (by omega),
        ← hnn 4 (by omega), ← hnn 5 (by omega), ← hnn 6 (by omega)]
      show ((0 + _ + _ + _ + _ + _ + _ + _ : Nat) : Int) = _
      push_cast; ring
    rw [hsum]
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    exact Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add (Int.ModEq.add
      (Int.ModEq.mul_left _ (hm 0 (by omega))) (Int.ModEq.mul_left _ (hm 1 (by omega))))
      (Int.ModEq.mul_left _ (hm 2 (by omega)))) (Int.ModEq.mul_left _ (hm 3 (by omega))))
      (Int.ModEq.mul_left _ (hm 4 (by omega)))) (Int.ModEq.mul_left _ (hm 5 (by omega))))
      (Int.ModEq.mul_left _ (hm 6 (by omega)))

/-! ## Flags -/

/-- The flag of `group [15, col, rb]`. -/
theorem gOk_15 (cd : ByteArray) (col rb : Nat) : gOk cd 15 col rb = okCol cd rb col 4 := by
  simp only [gOk, okCol, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show Nat.testBit 15 0 = true by decide, show Nat.testBit 15 1 = true by decide,
    show Nat.testBit 15 2 = true by decide, show Nat.testBit 15 3 = true by decide,
    Bool.not_true, Bool.false_or]

/-- The fifteen group flags, in the order the segment ANDs them, make `okA`. -/
theorem flags_okA (cd : ByteArray) (b : Bool) :
    (((((((((((((((b && okCol cd 0 0 4) && okCol cd 0 1 4) && okCol cd 0 2 4) && okCol cd 0 3 4) &&
      okCol cd 0 4 4) && okCol cd 0 5 4) && okCol cd 0 6 4) && okCol cd 1 0 4) && okCol cd 1 1 4) &&
      okCol cd 1 2 4) && okCol cd 1 3 3) && okCol cd 1 4 3) && okCol cd 1 5 3) && okCol cd 1 6 3) &&
      okRow7 cd) = (b && okA cd) := by
  rw [Bool.eq_iff_iff]
  simp only [okCol, okRow7, okA, List.range_succ, List.range_zero, List.nil_append, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.reduceMul, Nat.reduceAdd]
  constructor <;> intro h <;> simp only [h, and_self]

end MlDsaOptGlam87.Proofs.Exp
