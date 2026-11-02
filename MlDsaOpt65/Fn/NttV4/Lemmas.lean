import MlDsaOpt65.Fn.NttV4.Arith
import MlDsaOpt44.Fn.Ntt.V4.Step
/-!
# v4 `ntt` / `intt` lemmas for ML-DSA-65 and ML-DSA-87 (shared)

The ML-DSA-44 development (`MlDsaOpt44/Fn/Ntt/V4/`: `shU`, `ftA`/`ftB`, `gsB4`, `PI`,
the inverse butterflies, the Shoup constants) applies unchanged; this file adds what
depends on the parameter set:

* `LI6`: the forward bias interval for `γ1 = 2^19` (`lo6`/`hi6`) and the forward
  butterflies against `fwdL` (`ct6m_step`, `ct6s_step`), as `ct4*` for ML-DSA-44;
* the UseHint word for `γ2 = 261888`, `m = 16` (`uh6W`: `D' = (y · 2149582851) >> 49`,
  unmasked, result `AND 15`), its lane semantics `uh6W_lanes` (`uh6L`), and the
  stored-word predicate `UHP6` relative to the polynomial address `P`
  (`SP_g = P − 0x4900`, `HP_g = P + 0x4000`).
-/

namespace MlDsaOpt65.Proofs.Ntt6

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4 MlDsaOpt44.Proofs.L10
open MlDsaOpt44.Proofs.Ntt4 MlDsaOpt65.Proofs.NttV4

/-- Forward lane invariant after `L` layers (`γ1 = 2^19`). -/
def LI6 (x : UInt256) (L : Nat) (g : Nat → F) : Prop :=
  ∀ k, k < 4 → lo6 L ≤ lane x.toNat k ∧ lane x.toNat k ≤ hi6 L ∧ ((lane x.toNat k : Nat) : F) = g k

/-! ## Forward butterflies -/

theorem ct6_core {xa u : UInt256} {L : Nat} {ga gu : Nat → F} (hL : L < 8)
    (ha : LI6 xa L ga) (hu : ∀ k, k < 4 → lane u.toNat k < U4 ∧ ((lane u.toNat k : Nat) : F) = gu k) :
    LI6 (ftA xa u) (L + 1) (fun k => ga k + gu k) ∧ LI6 (ftB xa u) (L + 1) (fun k => ga k - gu k) := by
  have hge := lo6_ge hL
  have hsu := lo6_succ hL
  have hhi := hi6_succ L
  have hlt := hi6_lt (L := L) (by omega)
  have hxa := toNat_eq_pack4 xa
  have hxu := toNat_eq_pack4 u
  constructor
  · have h64 : ∀ k, k < 4 → lane u.toNat k + lane xa.toNat k < 2 ^ 64 := fun k hk => by
      have := (hu k hk).1; have := (ha k hk).2.1; unfold U4 at *; omega
    unfold ftA
    rw [hxu, hxa, EvmProof.Word.ofNat_add_mod, pack4_add]
    intro k hk
    rw [lane_ofNat_pack4 h64 hk]
    have := (hu k hk).1; have := (ha k hk).1; have := (ha k hk).2.1
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.cast_add, (hu k hk).2, (ha k hk).2.2, add_comm]
  · have hle : ∀ k, k < 4 → lane u.toNat k ≤ lane xa.toNat k := fun k hk => by
      have := (hu k hk).1; have := (ha k hk).1; omega
    have h64 : ∀ k, k < 4 → lane xa.toNat k < 2 ^ 64 := fun k _ => lane_lt _ _
    unfold ftB
    rw [hxu, hxa, EvmProof.Word.ofNat_sub_ofNat (pack4_le hle) (pack4_lt4 h64), pack4_sub hle]
    have h64' : ∀ k, k < 4 → lane xa.toNat k - lane u.toNat k < 2 ^ 64 := fun k hk => by
      have := h64 k hk; omega
    intro k hk
    rw [lane_ofNat_pack4 h64' hk]
    have := (hu k hk).1; have := (ha k hk).1; have := (ha k hk).2.1
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.cast_sub (hle k hk), (hu k hk).2, (ha k hk).2.2]

theorem LI6.lt {x : UInt256} {L : Nat} {g : Nat → F} (h : LI6 x L g) (hL : L ≤ 8) {k : Nat} (hk : k < 4) :
    lane x.toNat k < 2 ^ 28 := Nat.lt_of_le_of_lt (h k hk).2.1 (hi6_lt hL)

/-- Montgomery product by a table zeta (`z < 2^23`, `z ≡ ζ R`). -/
theorem montu6_lanes {xb : UInt256} {L z : Nat} {gb : Nat → F} {zv : F} (hL : L ≤ 8)
    (hb : LI6 xb L gb) (hzq : z < 2 ^ 23) (hz : ((z : Nat) : F) = zv * R) :
    ∀ k, k < 4 → lane (montU (UInt256.ofNat z * xb)).toNat k < U4 ∧
      ((lane (montU (UInt256.ofNat z * xb)).toNat k : Nat) : F) = zv * gb k := by
  obtain ⟨hu, hul⟩ := montU_mul (x := xb) (z := z) (c := 2 ^ 19) (B := 2 ^ 28)
    (fun k hk => hb.lt hL hk) (by
      calc z * 2 ^ 28 ≤ 2 ^ 23 * 2 ^ 28 := Nat.mul_le_mul_right _ hzq.le
        _ = 2 ^ 32 * 2 ^ 19 := by norm_num) (by norm_num) (by norm_num)
  have h64 : ∀ k, k < 4 → montL (z * lane xb.toNat k) < 2 ^ 64 := fun k hk => by
    have := hul k hk; omega
  intro k hk
  rw [hu, lane_ofNat_pack4 h64 hk]
  refine ⟨by have := hul k hk; unfold U4; omega, ?_⟩
  simp only [montL_cast, Nat.cast_mul, hz, ← (hb k hk).2.2]
  linear_combination ((lane xb.toNat k : F) * zv) * R_Rinv

/-- Shoup product by an immediate zeta. -/
theorem shu6_lanes {xb : UInt256} {L zs zt m : Nat} {gb : Nat → F} (hL : L ≤ 8)
    (hb : LI6 xb L gb) (hS : ShoupOK zs zt m) :
    ∀ k, k < 4 → lane (shU zs zt xb).toNat k < U4 ∧
      ((lane (shU zs zt xb).toNat k : Nat) : F) = ζ m * gb k := by
  set B := fun k => lane xb.toNat k with hBdef
  have hB : ∀ k, k < 4 → B k < 2 ^ 28 := fun k hk => hb.lt hL hk
  have hsb := fun k (hk : k < 4) => shoup_bound hS.lo hS.hi (hB k hk)
  have hzsB : ∀ k, k < 4 → zs * B k < 2 ^ 60 := fun k hk => by
    have := hB k hk
    calc zs * B k < 2 ^ 32 * 2 ^ 28 := Nat.mul_lt_mul_of_lt_of_lt hS.zs_lt this
      _ = 2 ^ 60 := by norm_num
  have hdiv : ∀ k, k < 4 → zs * B k / 2 ^ 32 % 2 ^ 32 = zs * B k / 2 ^ 32 := fun k hk => by
    have := hzsB k hk; apply Nat.mod_eq_of_lt; omega
  have hztB : ∀ k, k < 4 → zt * B k < 2 ^ 64 := fun k hk => by
    have := hB k hk
    calc zt * B k < 2 ^ 23 * 2 ^ 28 := Nat.mul_lt_mul_of_lt_of_lt hS.zt_lt this
      _ < 2 ^ 64 := by norm_num
  have hxb : xb = UInt256.ofNat (pack4 B) := toNat_eq_pack4 xb
  have e : shU zs zt xb =
      UInt256.ofNat (pack4 fun k => zt * B k - 8380417 * (zs * B k / 2 ^ 32 % 2 ^ 32)) := by
    unfold shU
    rw [hxb, u_mul zs B, u_shr_and (j := 32) (fun k hk => by have := hzsB k hk; show _ < _; omega)
      (by norm_num) (by norm_num) m32_eq, u_mul 8380417, u_mul zt,
      u_sub (fun k hk => hztB k hk) (fun k hk => by rw [hdiv k hk]; exact (hsb k hk).1)]
  have h64 : ∀ k, k < 4 → zt * B k - 8380417 * (zs * B k / 2 ^ 32 % 2 ^ 32) < 2 ^ 64 := fun k hk => by
    have := hztB k hk; omega
  intro k hk
  rw [e, lane_ofNat_pack4 h64 hk, hdiv k hk]
  refine ⟨by have := hsb k hk; omega, ?_⟩
  rw [Nat.cast_sub (hsb k hk).1, Nat.cast_mul, Nat.cast_mul, hS.cast, (hb k hk).2.2]
  have hq : ((8380417 : Nat) : F) = 0 := by decide
  rw [hq]; ring

theorem LI6.congr {x : UInt256} {L : Nat} {g g' : Nat → F} (h : LI6 x L g)
    (hg : ∀ k, k < 4 → g k = g' k) : LI6 x L g' :=
  fun k hk => ⟨(h k hk).1, (h k hk).2.1, (h k hk).2.2.trans (hg k hk)⟩

/-! ## Forward butterflies against `fwdL` -/

theorem ct6_model {h : Nat → Nat → F} {L len ia ib m : Nat} {xa u : UInt256} {zv : F}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hzv : zv = ζ m)
    (ha : LI6 xa L (fun k => fwdL (h k) L ia))
    (hu : ∀ k, k < 4 → lane u.toNat k < U4 ∧ ((lane u.toNat k : Nat) : F) = zv * fwdL (h k) L ib) :
    LI6 (ftA xa u) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI6 (ftB xa u) (L + 1) (fun k => fwdL (h k) (L + 1) ib) := by
  subst hib hzv
  obtain ⟨h1, h2⟩ := ct6_core hL ha hu
  obtain ⟨hhi, hdiv⟩ := divmod_hi hlo
  constructor
  · refine h1.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_pos hlo, ← hm]
  · refine h2.congr (fun k _ => ?_)
    rw [fwdL_succ, ← hlen]
    unfold fwdLayer
    rw [if_neg (by rw [hhi]; omega), hdiv, ← hm, Nat.add_sub_cancel]

/-- Forward butterfly with a table zeta (passes B, C). -/
theorem ct6m_step (h : Nat → Nat → F) (L len ia ib m z : Nat) {xa xb : UInt256}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hz : z = zm m)
    (ha : LI6 xa L (fun k => fwdL (h k) L ia)) (hb : LI6 xb L (fun k => fwdL (h k) L ib)) :
    LI6 (ftA xa (montU (UInt256.ofNat z * xb))) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI6 (ftB xa (montU (UInt256.ofNat z * xb))) (L + 1) (fun k => fwdL (h k) (L + 1) ib) := by
  subst hz
  exact ct6_model hL hlen hlo hib hm rfl ha
    (montu6_lanes (by omega) hb (Nat.lt_trans (zm_lt m) (by norm_num)) (zm_cast m))

/-- Forward butterfly with an immediate zeta by Shoup's method (pass A). -/
theorem ct6s_step (h : Nat → Nat → F) (L len ia ib m : Nat) {zs zt : Nat} {xa xb : UInt256}
    (hL : L < 8) (hlen : len = 128 / 2 ^ L) (hlo : ia % (2 * len) < len) (hib : ib = ia + len)
    (hm : m = 128 / len + ia / (2 * len)) (hS : ShoupOK zs zt m)
    (ha : LI6 xa L (fun k => fwdL (h k) L ia)) (hb : LI6 xb L (fun k => fwdL (h k) L ib)) :
    LI6 (ftA xa (shU zs zt xb)) (L + 1) (fun k => fwdL (h k) (L + 1) ia) ∧
      LI6 (ftB xa (shU zs zt xb)) (L + 1) (fun k => fwdL (h k) (L + 1) ib) :=
  ct6_model hL hlen hlo hib hm rfl ha (shu6_lanes (by omega) hb hS)


/-! ## The fused UseHint word (`γ2 = 261888`, `m = 16`) -/

/-- `D' = (y · 2149582851) >> 49`, not masked. -/
def uD6 (y : UInt256) : UInt256 := UInt256.shiftRight (UInt256.ofNat 2149582851 * y) (UInt256.ofNat 49)
/-- `v = ((D' >> 1) & M14) + ((16 − h) + 2 (h & D'))`. -/
def uV6 (d : UInt256) (h : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat 102837757730839990959496584137676933742227568448368519617200127)
      (UInt256.shiftRight d (UInt256.ofNat 1)) +
    ((UInt256.ofNat 100433627766186892226817148642057678073346828735512196415504 - UInt256.ofNat h) +
      (UInt256.land (UInt256.ofNat h) d + UInt256.land (UInt256.ofNat h) d))
/-- `v & 15`. -/
def uF6 (v : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 94156526030800211462641076851929073193762651939542684139535) v

/-- The word `uh_word` stores (`x` the output word, `s` the `SP` word, `h` the `HP` word). -/
def uh6W (x : UInt256) (s h : Nat) : UInt256 := uF6 (uV6 (uD6 (uY (uX x s))) h)

/-- The stored word `w` at coefficient `t` of the polynomial at `P`: lane `r` is the fused
UseHint of a value `W < 2^26 + q` congruent to `g r`, against the `SP` word at
`P − 0x4900` and the `HP` word at `P + 0x4000` of `m0`. -/
def UHP6 (m0 : ByteArray) (P t w : Nat) (g : Nat → F) : Prop :=
  ∀ r, r < 4 → ∃ W, W < Bu ∧ ((W : Nat) : F) = g r ∧
    lane w r = uh6L (lane (word m0 (P - 18688 + 32 * t)) r + W) (lane (word m0 (P + 16384 + 32 * t)) r)

/-- Lane `r` of a word shifted right by 49, below bit 15, is the lane's own
quotient when every lane is `< 2^61`. -/
theorem lane_shr49 {P : Nat → Nat} (hP : ∀ r, r < 4 → P r < 2 ^ 63) {r : Nat} (hr : r < 4) :
    lane (pack4 P / 2 ^ 49) r % 2 ^ 15 = P r / 2 ^ 49 := by
  have h0 := hP 0 (by omega); have h1 := hP 1 (by omega)
  have h2 := hP 2 (by omega); have h3 := hP 3 (by omega)
  unfold lane pack4
  interval_cases r <;>
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.div_div_eq_div_mul] <;> omega

theorem pack4_congr {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : pack4 a = pack4 b := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem uh6W_lanes {x : UInt256} {s h : Nat} (hs : s < 2 ^ 256) (hh : h < 2 ^ 256)
    (hx : ∀ r, r < 4 → lane s r + lane x.toNat r < 2 ^ 31) (hh1 : ∀ r, r < 4 → lane h r ≤ 1) :
    ∀ r, r < 4 → lane (uh6W x s h).toNat r = uh6L (lane s r + lane x.toNat r) (lane h r) := by
  obtain ⟨X, hX⟩ : ∃ X : Nat → Nat, X = fun r => lane s r + lane x.toNat r := ⟨_, rfl⟩
  have hXlt : ∀ r, r < 4 → X r < 2 ^ 31 := fun r hr => by rw [hX]; exact hx r hr
  -- x = SP + W
  have eX : uX x s = UInt256.ofNat (pack4 X) := by
    unfold uX
    calc UInt256.ofNat s + x = UInt256.ofNat (pack4 fun r => lane s r) +
          UInt256.ofNat (pack4 fun r => lane x.toNat r) := by rw [pk_lanes hs, ← toNat_eq_pack4]
      _ = UInt256.ofNat (pack4 X) := by rw [u_add, hX]
  -- y = x − ⌊x/q⌋
  obtain ⟨Y, hY⟩ : ∃ Y : Nat → Nat, Y = fun r => X r - X r / 8380417 := ⟨_, rfl⟩
  have eY : uY (UInt256.ofNat (pack4 X)) = UInt256.ofNat (pack4 Y) := by
    unfold uY uQ
    rw [u_mul, u_shr_and (j := 9) (fun r hr => by have := hXlt r hr; show _ < _; omega)
      (by norm_num) (by norm_num) (by unfold pack4; norm_num),
      u_sub (fun r hr => by have := hXlt r hr; show _ < _; omega)
        (fun r hr => by
          have := hXlt r hr; show _ ≤ _; rw [UH.div_q this]; exact Nat.div_le_self _ _)]
    congr 1
    exact pack4_congr fun r hr => by rw [UH.div_q (hXlt r hr), hY]
  have hYlt : ∀ r, r < 4 → Y r < 2 ^ 31 := fun r hr => by have := hXlt r hr; rw [hY]; dsimp only; omega
  -- D' = (2149582851 y) >> 46, not masked
  obtain ⟨P, hP⟩ : ∃ P : Nat → Nat, P = fun r => 2149582851 * Y r := ⟨_, rfl⟩
  have hPlt : ∀ r, r < 4 → P r < 2 ^ 63 := fun r hr => by have := hYlt r hr; rw [hP]; dsimp only; omega
  have hPw : pack4 P < 2 ^ 256 := pack4_lt4 fun r hr => by have := hPlt r hr; omega
  obtain ⟨Dw, hDw⟩ : ∃ Dw : Nat, Dw = pack4 P / 2 ^ 49 := ⟨_, rfl⟩
  have eD : uD6 (UInt256.ofNat (pack4 Y)) = UInt256.ofNat Dw := by
    unfold uD6
    rw [u_mul, ofNat_shr _ (by norm_num), ← hP, Nat.mod_eq_of_lt hPw, Nat.shiftRight_eq_div_pow, hDw]
  have hDwlt : Dw < 2 ^ 256 := by rw [hDw]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hPw
  obtain ⟨Dl, hDl⟩ : ∃ Dl : Nat → Nat, Dl = fun r => lane Dw r := ⟨_, rfl⟩
  have hD15 : ∀ r, r < 4 → Dl r % 2 ^ 15 = Y r / 261888 := fun r hr => by
    rw [hDl, hDw]
    show lane (pack4 P / 2 ^ 49) r % 2 ^ 15 = _
    rw [lane_shr49 hPlt hr, hP]
    exact divg2_exact6 (by have := hYlt r hr; omega)
  have hDl64 : Lanes Dl := by rw [hDl]; exact lanes_lane Dw
  have eDw : UInt256.ofNat Dw = UInt256.ofNat (pack4 Dl) := by rw [hDl, pk_lanes hDwlt]
  -- v
  obtain ⟨H, hH⟩ : ∃ H : Nat → Nat, H = fun r => lane h r := ⟨_, rfl⟩
  have eh : UInt256.ofNat h = UInt256.ofNat (pack4 H) := by rw [hH, pk_lanes hh]
  have hH64 : Lanes H := by rw [hH]; exact lanes_lane h
  have hH1 : ∀ r, r < 4 → H r ≤ 1 := fun r hr => by rw [hH]; exact hh1 r hr
  obtain ⟨V, hV⟩ : ∃ V : Nat → Nat,
      V = fun r => Dl r / 2 ^ 1 % 2 ^ 14 + ((16 - H r) + ((H r &&& Dl r) + (H r &&& Dl r))) := ⟨_, rfl⟩
  have hand : ∀ r, r < 4 → H r &&& Dl r ≤ 1 := fun r hr => by
    rw [UH.land_bit (hH1 r hr)]; split_ifs <;> omega
  have hVlt : ∀ r, r < 4 → V r < 2 ^ 15 := fun r hr => by
    have := hand r hr; have : Dl r / 2 ^ 1 % 2 ^ 14 < 2 ^ 14 := Nat.mod_lt _ (by norm_num)
    rw [hV]; dsimp only; omega
  have eV : uV6 (UInt256.ofNat Dw) h = UInt256.ofNat (pack4 V) := by
    unfold uV6
    rw [eDw, eh, u_shr_and (j := 14) hDl64 (by norm_num) (by norm_num) (by unfold pack4; norm_num),
      show (100433627766186892226817148642057678073346828735512196415504 : Nat) = pack4 fun _ => 16 by
        unfold pack4; norm_num,
      u_sub (fun r _ => by show _ < _; omega) (fun r hr => by have := hH1 r hr; show _ ≤ _; omega),
      u_and hH64 hDl64, u_add, u_add, u_add, hV]
  -- v mod 16
  have eF : uF6 (UInt256.ofNat (pack4 V)) = UInt256.ofNat (pack4 fun r => V r % 16) := by
    unfold uF6
    rw [show (94156526030800211462641076851929073193762651939542684139535 : Nat) = pack4 fun _ => 15 by
        unfold pack4; norm_num,
      u_and (fun r _ => by show _ < _; omega) (fun r hr => by have := hVlt r hr; show _ < _; omega)]
    congr 1
    exact pack4_congr fun r _ => G5H.and15 _
  intro r hr
  unfold uh6W
  rw [eX, eY, eD, eV, eF, lane_ofNat_pack4 (fun r _ => by omega) hr]
  have h15 := hD15 r hr
  have hb := hH1 r hr
  have hXr : X r = lane s r + lane x.toNat r := by rw [hX]
  have hYr : Y r = X r - X r / 8380417 := by rw [hY]
  have hVr : V r = Dl r / 2 ^ 1 % 2 ^ 14 + ((16 - H r) + ((H r &&& Dl r) + (H r &&& Dl r))) := by rw [hV]
  have hHr : H r = lane h r := by rw [hH]
  rw [← hXr, ← hHr, hVr]
  unfold uh6L
  rw [← hYr, UH.land_bit hb, UH.land_bit hb]
  split_ifs <;> omega


theorem uh6_store {m0 M : ByteArray} {g : Nat → F} {x : UInt256} {P t : Nat}
    (hSH : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (P - 18688 + 32 * t)) r ≤ 128 * 8380417 + 261888 - 1 ∧
      lane (word m0 (P + 16384 + 32 * t)) r ≤ 1)
    (hF : FrameExcept m0 M [(P, P + 8192)]) (hP : 18688 ≤ P) (ht : t < 256) (hx : LOK x Bu g) :
    UHP6 m0 P t (uh6W x (word M (P - 18688 + 32 * t)) (word M (P + 16384 + 32 * t))).toNat g := by
  have eS : word M (P - 18688 + 32 * t) = word m0 (P - 18688 + 32 * t) :=
    FrameExcept.word hF (by simp only [avoids_cons, avoids_nil, and_true]; omega)
  have eH : word M (P + 16384 + 32 * t) = word m0 (P + 16384 + 32 * t) :=
    FrameExcept.word hF (by simp only [avoids_cons, avoids_nil, and_true]; omega)
  rw [eS, eH]
  intro r hr
  refine ⟨lane x.toNat r, (hx r hr).1, (hx r hr).2, ?_⟩
  exact uh6W_lanes (word_lt _ _) (word_lt _ _)
    (fun r hr => uh6_x_lt (by have := (hx r hr).1; unfold Bu at this; omega) (hSH t ht r hr).1)
    (fun r hr => (hSH t ht r hr).2) r hr

end MlDsaOpt65.Proofs.Ntt6
