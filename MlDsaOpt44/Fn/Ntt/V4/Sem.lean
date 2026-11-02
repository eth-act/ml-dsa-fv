import MlDsaOpt44.Fn.Ntt.V4.Defs
/-!
# Lane semantics of the v4 butterflies and of the fused UseHint word (WP G, H)

* `ct4_core`: `a' = u + a`, `b' = a − u` act lane-wise and move the forward
  interval `[lo4 L, hi4 L]` to `[lo4 (L+1), hi4 (L+1)]` for any `u` with lanes
  `< U4` (the bias keeps `a ≥ U4 > u`, so `a − u` never borrows);
* `montu_lanes` / `shu_lanes`: the Montgomery (table zetas) and Shoup (pass A)
  products have lanes `< U4` congruent to `ζ b`;
* `gsB4_eq`: `(C − a) + b = (C + b) − a` in `UInt256`, so the v3 inverse
  butterfly lemmas apply unchanged;
* `uh4W_lanes`: the fused UseHint word acts lane-wise (`D'` is not masked: the
  neighbouring lane's product bits land at bits `≥ 18` and only bits `< 15` are
  read) and computes `uh4L`.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4 MlDsaOpt44.Proofs.L10

theorem lane_ofNat_pack4 {v : Nat → Nat} (h : ∀ k, k < 4 → v k < 2 ^ 64) {k : Nat} (hk : k < 4) :
    lane (UInt256.ofNat (pack4 v)).toNat k = v k := by
  rw [toNat_ofNat_of_lt (pack4_lt4 h), lane_pack4' h hk]

/-! ## Forward butterflies -/

theorem ct4_core {xa u : UInt256} {L : Nat} {ga gu : Nat → F} (hL : L < 8)
    (ha : LI xa L ga) (hu : ∀ k, k < 4 → lane u.toNat k < U4 ∧ ((lane u.toNat k : Nat) : F) = gu k) :
    LI (ftA xa u) (L + 1) (fun k => ga k + gu k) ∧ LI (ftB xa u) (L + 1) (fun k => ga k - gu k) := by
  have hge := lo4_ge hL
  have hsu := lo4_succ hL
  have hhi := hi4_succ L
  have hlt := hi4_lt (L := L) (by omega)
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

theorem LI.lt {x : UInt256} {L : Nat} {g : Nat → F} (h : LI x L g) (hL : L ≤ 8) {k : Nat} (hk : k < 4) :
    lane x.toNat k < 2 ^ 28 := Nat.lt_of_le_of_lt (h k hk).2.1 (hi4_lt hL)

/-- Montgomery product by a table zeta (`z < 2^23`, `z ≡ ζ R`). -/
theorem montu_lanes {xb : UInt256} {L z : Nat} {gb : Nat → F} {zv : F} (hL : L ≤ 8)
    (hb : LI xb L gb) (hzq : z < 2 ^ 23) (hz : ((z : Nat) : F) = zv * R) :
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
theorem shu_lanes {xb : UInt256} {L zs zt m : Nat} {gb : Nat → F} (hL : L ≤ 8)
    (hb : LI xb L gb) (hS : ShoupOK zs zt m) :
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

/-! ## Inverse butterfly -/

theorem sub_add_eq' (C a b : UInt256) : (C - a) + b = (C + b) - a := by
  cases C; cases a; cases b
  show UInt256.add (UInt256.sub _ _) _ = UInt256.sub (UInt256.add _ _) _
  simp only [UInt256.add, UInt256.sub]
  congr 1
  exact sub_add_eq_add_sub _ _ _

theorem gsB4_eq (C xa xb z : UInt256) : gsB4 C xa xb z = gsB C xa xb z := by
  unfold gsB4 gsB; rw [sub_add_eq']

/-! ## The fused UseHint word -/

/-- Lane `r` of a word shifted right by 46, below bit 15, is the lane's own
quotient when every lane is `< 2^61`. -/
theorem lane_shr46 {P : Nat → Nat} (hP : ∀ r, r < 4 → P r < 2 ^ 61) {r : Nat} (hr : r < 4) :
    lane (pack4 P / 2 ^ 46) r % 2 ^ 15 = P r / 2 ^ 46 := by
  have h0 := hP 0 (by omega); have h1 := hP 1 (by omega)
  have h2 := hP 2 (by omega); have h3 := hP 3 (by omega)
  unfold lane pack4
  interval_cases r <;>
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.div_div_eq_div_mul] <;> omega

theorem pack4_congr {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : pack4 a = pack4 b := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem uh4W_lanes {x : UInt256} {s h : Nat} (hs : s < 2 ^ 256) (hh : h < 2 ^ 256)
    (hx : ∀ r, r < 4 → lane s r + lane x.toNat r < 2 ^ 31) (hh1 : ∀ r, r < 4 → lane h r ≤ 1) :
    ∀ r, r < 4 → lane (uh4W x s h).toNat r = uh4L (lane s r + lane x.toNat r) (lane h r) := by
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
  -- D' = (738919105 y) >> 46, not masked
  obtain ⟨P, hP⟩ : ∃ P : Nat → Nat, P = fun r => 738919105 * Y r := ⟨_, rfl⟩
  have hPlt : ∀ r, r < 4 → P r < 2 ^ 61 := fun r hr => by have := hYlt r hr; rw [hP]; dsimp only; omega
  have hPw : pack4 P < 2 ^ 256 := pack4_lt4 fun r hr => by have := hPlt r hr; omega
  obtain ⟨Dw, hDw⟩ : ∃ Dw : Nat, Dw = pack4 P / 2 ^ 46 := ⟨_, rfl⟩
  have eD : uD (UInt256.ofNat (pack4 Y)) = UInt256.ofNat Dw := by
    unfold uD
    rw [u_mul, ofNat_shr _ (by norm_num), ← hP, Nat.mod_eq_of_lt hPw, Nat.shiftRight_eq_div_pow, hDw]
  have hDwlt : Dw < 2 ^ 256 := by rw [hDw]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hPw
  obtain ⟨Dl, hDl⟩ : ∃ Dl : Nat → Nat, Dl = fun r => lane Dw r := ⟨_, rfl⟩
  have hD15 : ∀ r, r < 4 → Dl r % 2 ^ 15 = Y r / 95232 := fun r hr => by
    rw [hDl, hDw]
    show lane (pack4 P / 2 ^ 46) r % 2 ^ 15 = _
    rw [lane_shr46 hPlt hr, hP]
    exact divg2_exact (by have := hYlt r hr; omega)
  have hDl64 : Lanes Dl := by rw [hDl]; exact lanes_lane Dw
  have eDw : UInt256.ofNat Dw = UInt256.ofNat (pack4 Dl) := by rw [hDl, pk_lanes hDwlt]
  -- v
  obtain ⟨H, hH⟩ : ∃ H : Nat → Nat, H = fun r => lane h r := ⟨_, rfl⟩
  have eh : UInt256.ofNat h = UInt256.ofNat (pack4 H) := by rw [hH, pk_lanes hh]
  have hH64 : Lanes H := by rw [hH]; exact lanes_lane h
  have hH1 : ∀ r, r < 4 → H r ≤ 1 := fun r hr => by rw [hH]; exact hh1 r hr
  obtain ⟨V, hV⟩ : ∃ V : Nat → Nat,
      V = fun r => Dl r / 2 ^ 1 % 2 ^ 14 + ((44 - H r) + ((H r &&& Dl r) + (H r &&& Dl r))) := ⟨_, rfl⟩
  have hand : ∀ r, r < 4 → H r &&& Dl r ≤ 1 := fun r hr => by
    rw [UH.land_bit (hH1 r hr)]; split_ifs <;> omega
  have hVlt : ∀ r, r < 4 → V r < 2 ^ 15 := fun r hr => by
    have := hand r hr; have : Dl r / 2 ^ 1 % 2 ^ 14 < 2 ^ 14 := Nat.mod_lt _ (by norm_num)
    rw [hV]; dsimp only; omega
  have eV : uV (UInt256.ofNat Dw) h = UInt256.ofNat (pack4 V) := by
    unfold uV
    rw [eDw, eh, u_shr_and (j := 14) hDl64 (by norm_num) (by norm_num) (by unfold pack4; norm_num),
      show (276192476357013953623747158765658614701703779022658540142636 : Nat) = pack4 fun _ => 44 by
        unfold pack4; norm_num,
      u_sub (fun r _ => by show _ < _; omega) (fun r hr => by have := hH1 r hr; show _ ≤ _; omega),
      u_and hH64 hDl64, u_add, u_add, u_add, hV]
  -- v mod 44
  have eF : uF (UInt256.ofNat (pack4 V)) = UInt256.ofNat (pack4 fun r => V r % 44) := by
    unfold uF
    rw [u_mul, u_shr_and (j := 10) (fun r hr => by have := hVlt r hr; show _ < _; omega)
      (by norm_num) (by norm_num) (by unfold pack4; norm_num), u_mul,
      u_sub (fun r hr => by have := hVlt r hr; show _ < _; omega) (fun r hr => by
        have := hVlt r hr; show _ ≤ _; rw [div44_exact this]; omega)]
    congr 1
    exact pack4_congr fun r hr => by rw [mod44_exact (hVlt r hr)]
  intro r hr
  unfold uh4W
  rw [eX, eY, eD, eV, eF, lane_ofNat_pack4 (fun r _ => by omega) hr]
  have h15 := hD15 r hr
  have hb := hH1 r hr
  have hXr : X r = lane s r + lane x.toNat r := by rw [hX]
  have hYr : Y r = X r - X r / 8380417 := by rw [hY]
  have hVr : V r = Dl r / 2 ^ 1 % 2 ^ 14 + ((44 - H r) + ((H r &&& Dl r) + (H r &&& Dl r))) := by rw [hV]
  have hHr : H r = lane h r := by rw [hH]
  rw [← hXr, ← hHr, hVr]
  unfold uh4L
  rw [← hYr, UH.land_bit hb, UH.land_bit hb]
  split_ifs <;> omega

end MlDsaOpt44.Proofs.Ntt4
