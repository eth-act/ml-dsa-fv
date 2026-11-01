import MlDsaOpt44.Fn.Ntt.Defs
/-!
# Lane arithmetic and butterfly semantics for `ntt` / `intt` (WP7)

Every stack word of the kernels holds four 64-bit lanes (`pack4`). The word
operations of a butterfly act lane-wise as long as no lane overflows: `ct_core`,
`gs_core`, `gsS_core`, `premont_core` turn the word expressions of `Defs` into
lane statements (`LOK`), and `ct_step`/`gs_step`/`gsS_step`/`premont_step`
phrase them against the layer models `fwdL`/`invL`. `PassInv` lemmas carry the
per-word invariant through the stores of a loop body.
-/

namespace MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs

/-! ## `pack4` -/

theorem pack4_lt4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) : pack4 v < 2 ^ 256 := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem lane_pack4' {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (pack4 v) k = v k := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold lane pack4
  interval_cases k <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul] <;> omega

theorem pack4_lane {x : Nat} (hx : x < 2 ^ 256) : pack4 (fun k => lane x k) = x := by
  unfold pack4 lane
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  omega

theorem lane_lt (x k : Nat) : lane x k < 2 ^ 64 := Nat.mod_lt _ (by positivity)

theorem pack4_add (a b : Nat → Nat) : pack4 a + pack4 b = pack4 (fun k => a k + b k) := by
  unfold pack4; ring

theorem pack4_mul (z : Nat) (a : Nat → Nat) : z * pack4 a = pack4 (fun k => z * a k) := by
  unfold pack4; ring

theorem pack4_le {a b : Nat → Nat} (h : ∀ k, k < 4 → a k ≤ b k) : pack4 a ≤ pack4 b := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  unfold pack4; omega

theorem pack4_sub {a b : Nat → Nat} (h : ∀ k, k < 4 → b k ≤ a k) :
    pack4 a - pack4 b = pack4 (fun k => a k - b k) := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [pack4]; omega

theorem pack4_div (w : Nat → Nat) : pack4 (fun k => 2 ^ 32 * w k) / 2 ^ 32 = pack4 w := by
  have : pack4 (fun k => 2 ^ 32 * w k) = 2 ^ 32 * pack4 w := by unfold pack4; ring
  rw [this, Nat.mul_div_cancel_left _ (by positivity)]

theorem land_split {a b x y : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (2 ^ 64 * x + a) &&& (2 ^ 64 * y + b) = 2 ^ 64 * (x &&& y) + (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hb)]
  split <;> simp [Nat.testBit_and]

theorem pack4_eq (v : Nat → Nat) : pack4 v = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v 3 + v 2) + v 1) + v 0 := by
  unfold pack4; ring

theorem pack4_land {a b : Nat → Nat} (ha : ∀ k, k < 4 → a k < 2 ^ 64) (hb : ∀ k, k < 4 → b k < 2 ^ 64) :
    pack4 a &&& pack4 b = pack4 (fun k => a k &&& b k) := by
  rw [pack4_eq, pack4_eq, pack4_eq, land_split (ha 0 (by omega)) (hb 0 (by omega)),
    land_split (ha 1 (by omega)) (hb 1 (by omega)), land_split (ha 2 (by omega)) (hb 2 (by omega))]

/-- The lane mask `M32X4`. -/
theorem m32_eq : (26959946660873538060741835960174461801791452538186943042387869433855 : Nat) =
    pack4 (fun _ => 2 ^ 32 - 1) := by
  unfold pack4; norm_num

theorem m32_land {t : Nat → Nat} (ht : ∀ k, k < 4 → t k < 2 ^ 64) :
    (26959946660873538060741835960174461801791452538186943042387869433855 : Nat) &&& pack4 t =
      pack4 (fun k => t k % 2 ^ 32) := by
  rw [m32_eq, pack4_land (fun _ _ => by norm_num) ht]
  congr 1; funext k
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_eq_pack4 (x : UInt256) : x = UInt256.ofNat (pack4 (fun k => lane x.toNat k)) := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [pack4_lane hx, ofNat_toNat]

/-! ## Montgomery reduction, lane-wise -/

/-- Lane Montgomery reduction (`R = 2^32`). -/
def montL (t : Nat) : Nat := (8380417 * (4236238847 * (t % 2 ^ 32) % 2 ^ 32) + t) / 2 ^ 32

theorem montL_dvd (t : Nat) : 2 ^ 32 ∣ 8380417 * (4236238847 * (t % 2 ^ 32) % 2 ^ 32) + t := by
  rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num]
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast [ZMod.natCast_mod]
  have : (1 + 8380417 * 4236238847 : ZMod 4294967296) = 0 := by decide
  linear_combination (t : ZMod 4294967296) * this

theorem montL_mul (t : Nat) :
    montL t * 2 ^ 32 = 8380417 * (4236238847 * (t % 2 ^ 32) % 2 ^ 32) + t :=
  Nat.div_mul_cancel (montL_dvd t)

theorem montL_lt {t c : Nat} (h : t < 2 ^ 32 * c) : montL t < c + 8380417 := by
  have hm := montL_mul t
  have h1 : 4236238847 * (t % 2 ^ 32) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
  by_contra hc
  have : (c + 8380417) * 2 ^ 32 ≤ montL t * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem R_Rinv : R * Rinv = 1 := by decide

theorem montL_cast (t : Nat) : ((montL t : Nat) : F) = (t : F) * Rinv := by
  have hm := congrArg (fun n : Nat => (n : F)) (montL_mul t)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hm
  have hq : (8380417 : F) = 0 := by decide
  rw [hq, zero_mul, zero_add] at hm
  have hR : ((2 : F) ^ 32) = R := by decide
  rw [hR] at hm
  rw [← hm, mul_assoc, R_Rinv, mul_one]

theorem montE_pack4 {t : Nat → Nat} (ht : ∀ k, k < 4 → t k < 2 ^ 63) :
    montE (pack4 t) = pack4 (fun k => montL (t k)) := by
  have ht' : ∀ k, k < 4 → t k < 2 ^ 64 := fun k hk => by have := ht k hk; omega
  unfold montE
  rw [m32_land ht', pack4_mul, m32_land (fun k _ => by
      have : t k % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
      omega), pack4_mul, pack4_add]
  have hl : ∀ k, k < 4 →
      8380417 * (4236238847 * (t k % 2 ^ 32) % 2 ^ 32) + t k < 2 ^ 64 := fun k hk => by
    have := ht k hk
    have : 4236238847 * (t k % 2 ^ 32) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
    omega
  rw [Nat.mod_eq_of_lt (pack4_lt4 hl)]
  have : (fun k => 8380417 * (4236238847 * (t k % 2 ^ 32) % 2 ^ 32) + t k) =
      fun k => 2 ^ 32 * montL (t k) := by
    funext k; rw [← montL_mul, Nat.mul_comm]
  rw [this, pack4_div]

theorem montU_ofNat (t : Nat) : montU (UInt256.ofNat t) = UInt256.ofNat (montE t) := by
  unfold montU montE
  simp only [ofNat_land, ofNat_mul, EvmProof.Word.ofNat_add_mod, ofNat_shr _ (by norm_num : 32 < 256),
    Nat.shiftRight_eq_div_pow]

/-! ## `LOK` -/

theorem LOK.mono {x : UInt256} {A B : Nat} {g : Nat → F} (h : LOK x A g) (hAB : A ≤ B) : LOK x B g :=
  fun k hk => ⟨Nat.lt_of_lt_of_le (h k hk).1 hAB, (h k hk).2⟩

theorem LOK.congr {x : UInt256} {A : Nat} {g g' : Nat → F} (h : LOK x A g)
    (hg : ∀ k, k < 4 → g k = g' k) : LOK x A g' :=
  fun k hk => ⟨(h k hk).1, (h k hk).2.trans (hg k hk)⟩

/-- `LOK` of a word given by its lanes. -/
theorem LOK_pack4 {v : Nat → Nat} {B : Nat} {g : Nat → F} (h64 : ∀ k, k < 4 → v k < 2 ^ 64)
    (hB : ∀ k, k < 4 → v k < B) (hg : ∀ k, k < 4 → ((v k : Nat) : F) = g k) :
    LOK (UInt256.ofNat (pack4 v)) B g := by
  intro k hk
  rw [toNat_ofNat_of_lt (pack4_lt4 h64), lane_pack4' h64 hk]
  exact ⟨hB k hk, hg k hk⟩

theorem zm_lt (m : Nat) : zm m < 8380417 := Nat.mod_lt _ (by decide)

theorem zm_cast (m : Nat) : ((zm m : Nat) : F) = ζ m * R := by
  unfold zm ζ
  have h0 : 0 ≤ Fips204.zetas m := by unfold Fips204.zetas; exact Int.natCast_nonneg _
  have h1 : ((Fips204.zetas m).toNat : ℤ) = Fips204.zetas m := Int.toNat_of_nonneg h0
  rw [show Fips204.q = 8380417 from rfl, ZMod.natCast_mod, Nat.cast_mul, ← h1]
  push_cast
  rfl

/-- The forward subtraction constant `2q` per lane. -/
theorem c2q_eq : (105209460187928082099348286046428385038300376303896864318478598146 : Nat) =
    pack4 (fun _ => 2 * 8380417) := by
  unfold pack4; norm_num

/-- The inverse subtraction constant `q ⌈2^34 / q⌉` per lane. -/
theorem cinv_eq : (107892301422720248192881667340612308856777035899646234358599802398723 : Nat) =
    pack4 (fun _ => 17188235267) := by
  unfold pack4; norm_num

/-- Lanes of the Montgomery product `montU (z * x)`. -/
theorem montU_mul {x : UInt256} {z c : Nat} {B : Nat}
    (hx : ∀ k, k < 4 → lane x.toNat k < B) (hzB : z * B ≤ 2 ^ 32 * c) (hc : c ≤ 2 ^ 30)
    (hc0 : 0 < c) :
    montU (UInt256.ofNat z * x) =
      UInt256.ofNat (pack4 (fun k => montL (z * lane x.toNat k))) ∧
      ∀ k, k < 4 → montL (z * lane x.toNat k) < c + 8380417 := by
  have hlt : ∀ k, k < 4 → z * lane x.toNat k < 2 ^ 32 * c := fun k hk => by
    have := hx k hk
    rcases Nat.eq_zero_or_pos z with h | h
    · subst h; simp only [Nat.zero_mul]; positivity
    · exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left this h) hzB
  constructor
  · conv_lhs => rw [toNat_eq_pack4 x]
    rw [ofNat_mul, pack4_mul, montU_ofNat, montE_pack4 (fun k hk => by
      have := hlt k hk; have : c * 2 ^ 32 ≤ 2 ^ 62 := by omega
      show z * lane x.toNat k < 2 ^ 63; omega)]
  · exact fun k hk => montL_lt (hlt k hk)

/-! ## Butterflies on words -/

theorem ct_core {xa xb : UInt256} {A z : Nat} {ga gb : Nat → F} {zv : F}
    (ha : LOK xa A ga) (hb : LOK xb A gb) (hA : A ≤ 2 ^ 28) (hzq : z < 2 ^ 23)
    (hz : ((z : Nat) : F) = zv * R) :
    LOK (ctA xa xb (UInt256.ofNat z)) (A + 2 * 8380417) (fun k => ga k + zv * gb k) ∧
      LOK (ctB (UInt256.ofNat 105209460187928082099348286046428385038300376303896864318478598146)
        xa xb (UInt256.ofNat z)) (A + 2 * 8380417) (fun k => ga k - zv * gb k) := by
  obtain ⟨hu, hul⟩ := montU_mul (x := xb) (z := z) (c := 2 ^ 19) (B := A)
    (fun k hk => (hb k hk).1) (by
      calc z * A ≤ 2 ^ 23 * 2 ^ 28 := Nat.mul_le_mul (by omega) hA
        _ = 2 ^ 32 * 2 ^ 19 := by norm_num) (by norm_num) (by norm_num)
  have hal : ∀ k, k < 4 → lane xa.toNat k < A := fun k hk => (ha k hk).1
  have hucast : ∀ k, k < 4 → ((montL (z * lane xb.toNat k) : Nat) : F) = zv * gb k := fun k hk => by
    simp only [montL_cast, Nat.cast_mul, hz, ← (hb k hk).2]
    linear_combination ((lane xb.toNat k : F) * zv) * R_Rinv
  have hxa := toNat_eq_pack4 xa
  constructor
  · unfold ctA
    rw [hu, hxa, EvmProof.Word.ofNat_add_mod, pack4_add]
    apply LOK_pack4
    · intro k hk; have := hul k hk; have := hal k hk; omega
    · intro k hk; have := hul k hk; have := hal k hk; omega
    · intro k hk
      simp only [Nat.cast_add, hucast k hk, (ha k hk).2]
      ring
  · unfold ctB
    rw [hu, hxa, c2q_eq, EvmProof.Word.ofNat_add_mod, pack4_add]
    have hle : ∀ k, k < 4 → montL (z * lane xb.toNat k) ≤ 2 * 8380417 + lane xa.toNat k :=
      fun k hk => by have := hul k hk; omega
    have h64 : ∀ k, k < 4 → 2 * 8380417 + lane xa.toNat k < 2 ^ 64 := fun k hk => by
      have := hal k hk; omega
    rw [EvmProof.Word.ofNat_sub_ofNat (pack4_le hle) (pack4_lt4 h64), pack4_sub hle]
    apply LOK_pack4
    · intro k hk; have := h64 k hk; omega
    · intro k hk; have := hal k hk; omega
    · intro k hk
      rw [Nat.cast_sub (hle k hk), Nat.cast_add, hucast k hk, (ha k hk).2]
      have hq : ((2 * 8380417 : Nat) : F) = 0 := by decide
      rw [hq]; ring

/-- `(C + b) − a` and its Montgomery product with `z` (inverse `b'`). -/
theorem gsB_core {xa xb : UInt256} {A z : Nat} {ga gb : Nat → F} {zv : F}
    (ha : LOK xa A ga) (hb : LOK xb A gb) (hA : A ≤ 9662627968) (hzq : z < 8380417)
    (hz : ((z : Nat) : F) = zv * R) :
    LOK (gsB (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
      xa xb (UInt256.ofNat z)) Bu (fun k => zv * (gb k - ga k)) := by
  have hal : ∀ k, k < 4 → lane xa.toNat k < A := fun k hk => (ha k hk).1
  have hbl : ∀ k, k < 4 → lane xb.toNat k < A := fun k hk => (hb k hk).1
  have hxa := toNat_eq_pack4 xa
  have hxb := toNat_eq_pack4 xb
  have hle : ∀ k, k < 4 → lane xa.toNat k ≤ 17188235267 + lane xb.toNat k := fun k hk => by
    have := hal k hk; omega
  have h64 : ∀ k, k < 4 → 17188235267 + lane xb.toNat k < 2 ^ 64 := fun k hk => by
    have := hbl k hk; omega
  have hd : UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723 + xb - xa =
      UInt256.ofNat (pack4 (fun k => 17188235267 + lane xb.toNat k - lane xa.toNat k)) := by
    conv_lhs => rw [hxa, hxb]
    rw [cinv_eq, EvmProof.Word.ofNat_add_mod, pack4_add,
      EvmProof.Word.ofNat_sub_ofNat (pack4_le hle) (pack4_lt4 h64), pack4_sub hle]
  have hdl : ∀ k, k < 4 → 17188235267 + lane xb.toNat k - lane xa.toNat k < 2 ^ 64 :=
    fun k hk => by have := h64 k hk; omega
  have hlane : ∀ k, k < 4 →
      lane (UInt256.ofNat (pack4 (fun k => 17188235267 + lane xb.toNat k - lane xa.toNat k))).toNat k =
        17188235267 + lane xb.toNat k - lane xa.toNat k := fun k hk => by
    rw [toNat_ofNat_of_lt (pack4_lt4 hdl), lane_pack4' hdl hk]
  obtain ⟨hu, hul⟩ := montU_mul
    (x := UInt256.ofNat (pack4 (fun k => 17188235267 + lane xb.toNat k - lane xa.toNat k)))
    (z := z) (c := 2 ^ 26) (B := 17188235267 + 9662627968)
    (fun k hk => by rw [hlane k hk]; have := hbl k hk; omega) (by
      calc z * (17188235267 + 9662627968) ≤ 8380417 * (17188235267 + 9662627968) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 32 * 2 ^ 26 := by norm_num) (by norm_num) (by norm_num)
  unfold gsB
  rw [hd, hu]
  apply LOK_pack4
  · intro k hk; have := hul k hk; omega
  · intro k hk; have := hul k hk; unfold Bu; omega
  · intro k hk
    rw [montL_cast, hlane k hk, Nat.cast_mul, hz, Nat.cast_sub (hle k hk), Nat.cast_add,
      (ha k hk).2, (hb k hk).2]
    have hq : ((17188235267 : Nat) : F) = 0 := by decide
    rw [hq]
    linear_combination (zv * (gb k - ga k)) * R_Rinv

theorem gsA_core {xa xb : UInt256} {A : Nat} {ga gb : Nat → F}
    (ha : LOK xa A ga) (hb : LOK xb A gb) (hA : A ≤ 9662627968) :
    LOK (gsA xa xb) (2 * A) (fun k => ga k + gb k) := by
  have hxa : xa = UInt256.ofNat (pack4 (fun k => lane xa.toNat k)) := toNat_eq_pack4 xa
  have hxb : xb = UInt256.ofNat (pack4 (fun k => lane xb.toNat k)) := toNat_eq_pack4 xb
  unfold gsA
  rw [hxa, hxb, EvmProof.Word.ofNat_add_mod, pack4_add]
  apply LOK_pack4
  · intro k hk; have := (ha k hk).1; have := (hb k hk).1; omega
  · intro k hk; have := (ha k hk).1; have := (hb k hk).1; omega
  · intro k hk
    simp only [Nat.cast_add, (ha k hk).2, (hb k hk).2]
    ring

theorem gs_core {xa xb : UInt256} {A z : Nat} {ga gb : Nat → F} {zv : F}
    (ha : LOK xa A ga) (hb : LOK xb A gb) (hA : A ≤ 9662627968) (hB : Bu ≤ 2 * A)
    (hzq : z < 8380417) (hz : ((z : Nat) : F) = zv * R) :
    LOK (gsA xa xb) (2 * A) (fun k => ga k + gb k) ∧
      LOK (gsB (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat z)) (2 * A) (fun k => zv * (gb k - ga k)) :=
  ⟨gsA_core ha hb hA, (gsB_core ha hb hA hzq hz).mono hB⟩

theorem gsS_core {xa xb : UInt256} {A f z : Nat} {ga gb : Nat → F} {sa zv : F}
    (ha : LOK xa A ga) (hb : LOK xb A gb) (hA : A ≤ 9662627968)
    (hfq : f < 8380417) (hf : ((f : Nat) : F) = sa * R)
    (hzq : z < 8380417) (hz : ((z : Nat) : F) = zv * R) :
    LOK (gsAs (UInt256.ofNat f) xa xb) Bu (fun k => sa * (ga k + gb k)) ∧
      LOK (gsB (UInt256.ofNat 107892301422720248192881667340612308856777035899646234358599802398723)
        xa xb (UInt256.ofNat z)) Bu (fun k => zv * (gb k - ga k)) := by
  refine ⟨?_, gsB_core ha hb hA hzq hz⟩
  have hs := gsA_core ha hb hA
  unfold gsAs
  unfold gsA at hs
  obtain ⟨hu, hul⟩ := montU_mul (x := xb + xa) (z := f) (c := 2 ^ 26) (B := 2 * 9662627968)
    (fun k hk => by have := (hs k hk).1; omega) (by
      calc f * (2 * 9662627968) ≤ 8380417 * (2 * 9662627968) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 32 * 2 ^ 26 := by norm_num) (by norm_num) (by norm_num)
  rw [hu]
  apply LOK_pack4
  · intro k hk; have := hul k hk; omega
  · intro k hk; have := hul k hk; unfold Bu; omega
  · intro k hk
    simp only [montL_cast, Nat.cast_mul, hf, (hs k hk).2]
    linear_combination (sa * (ga k + gb k)) * R_Rinv

theorem premont_core {w : Nat} {g : Nat → F} (h : LOK (UInt256.ofNat w) (2 ^ 58) g) :
    LOK (UInt256.ofNat (montE w)) Bu (fun k => g k * Rinv) := by
  have hw := toNat_eq_pack4 (UInt256.ofNat w)
  have hm := montU_mul (x := UInt256.ofNat w) (z := 1) (c := 2 ^ 26) (B := 2 ^ 58)
    (fun k hk => (h k hk).1) (by norm_num) (by norm_num) (by norm_num)
  rw [← montU_ofNat, ← ofNat_toNat (UInt256.ofNat w)]
  rw [show UInt256.ofNat (UInt256.ofNat w).toNat = UInt256.ofNat 1 * UInt256.ofNat w by
    rw [ofNat_toNat, ofNat_mul, Nat.one_mul], hm.1]
  apply LOK_pack4
  · intro k hk; have := hm.2 k hk; omega
  · intro k hk; have := hm.2 k hk; unfold Bu; omega
  · intro k hk
    simp only [montL_cast, Nat.one_mul, (h k hk).2]

end MlDsaOpt44.Proofs.NttW
