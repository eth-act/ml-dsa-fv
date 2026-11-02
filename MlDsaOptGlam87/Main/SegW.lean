import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Fn.Ntt
import MlDsaOptGlam87.Fn.Hint
import MlDsaOpt87.Math
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/SegW.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# Segment `6727 … 6805`: `intt`, `usehint`, `pack` per row group

For `g < 2`: `intt [ACC + 0x2000 g]` (`Â ẑ`, lanes `< 2^57`, to lanes `< 2^30` congruent to
`NTT⁻¹`), `usehint [ACC + 0x2000 g]` (`UseHint(HP_g, W + SP_g − spOff)`, `SP_g` holding
`spOff − (2^13 S' + n_neg)`, `2^13 S' + n_neg ≡ 2^13 (c · t1)`; `S2.w_group`),
`pack [4, FIN + 256 + 2048 g, ACC + 0x2000 g]` (`w1Encode` of rows `4g … 4g + 3` into `FIN[8 + 64 g, 72 + 64 g)`). With `FinMu`: `FinAt m (finBytes cd)` under
`ok3`.
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs.Infra

/-- Subtraction respects congruence mod `q`. -/
theorem S2.sub_emod_congr {a b c d : Int} (h1 : (a - b) % (Fips204.q : Int) = 0)
    (h2 : (c - d) % (Fips204.q : Int) = 0) :
    (a - c) % (Fips204.q : Int) = (b - d) % (Fips204.q : Int) := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  have := dvd_sub (Int.dvd_of_emod_eq_zero h1) (Int.dvd_of_emod_eq_zero h2)
  have e : a - c - (b - d) = (a - b) - (c - d) := by ring
  rw [e]; exact this

theorem S2.azRow_size (cd : ByteArray) (r : Nat) : (azRow cd r).size = 256 := by
  simp [azRow]

theorem S2.wRow_get (cd : ByteArray) (r : Nat) {t : Nat} (ht : t < 256) :
    (wRow cd r)[t]! = ((Fips204.nttInv (azRow cd r))[t]! -
      2 ^ 13 * negacyclic (cD cd) (t1Of cd r) t) % (Fips204.q : Int) := by
  unfold wRow; exact MlDsaOpt44.Proofs.getElem!_map_range 256 t _ ht

theorem S2.w1Of_row (cd : ByteArray) {r : Nat} (hr : r < 8) : ((w1Of cd)[r]!).size = 256 := by
  unfold w1Of
  rw [MlDsaOpt44.Proofs.getElem!_map_range 8 r _ hr]
  simp

theorem S2.w1Of_get (cd : ByteArray) {r t : Nat} (hr : r < 8) (ht : t < 256) :
    ((w1Of cd)[r]!)[t]! = Fips204.useHint P (hintD cd)[r]![t]! (wRow cd r)[t]! := by
  unfold w1Of
  rw [MlDsaOpt44.Proofs.getElem!_map_range 8 r _ hr,
    MlDsaOpt44.Proofs.getElem!_map_range 256 t _ ht]

theorem S2.spOff_lt : spOff < 2 ^ 64 := by unfold spOff Fips204.q; norm_num

/-- One lane of a row: `UseHint(h, NTT⁻¹(Â ẑ)[t] + (spOff − s') − spOff)` with
`s' ≡ 2^13 (c · t1)` is `w1[t]` (the `intt` (65) / `usehint` (87) output). -/
theorem S2.w_lane {cd : ByteArray} (hcd : HDR ≤ cd.size) {g k t : Nat} (hg : g < 2) (hk : k < 4)
    (hR : 4 * g + k < 8) (ht : t < 256)
    {h : Array Fips204.Poly} (hhs : hintOf cd = some h) {c : Fips204.Poly} (hcs : cOf cd = some c)
    {n : Int} (hn : (n - (Fips204.nttInv (azRow cd (4 * g + k)))[t]!) % (Fips204.q : Int) = 0) :
    ((Fips204.useHint P ((h[4 * g + k]![t]!).toNat : Nat)
        (n + ((spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t) : Nat) : Int) -
          (spOff : Int))).toNat : Int) = ((w1Of cd)[4 * g + k]!)[t]! := by
  have hhD : hintD cd = h := by unfold hintD; rw [hhs]; rfl
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  have hcc := csum_congr cd hcd c hcs hg hk hR ht
  have hle : 2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t ≤ spOff := by
    have := hcc.1; unfold spOff Fips204.q; omega
  have hb := hintBitUnpack_range _ h hhs hR ht
  have hcong : (n + ((spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t) : Nat) : Int) -
      (spOff : Int)) % (Fips204.q : Int) = (wRow cd (4 * g + k))[t]! := by
    rw [S2.wRow_get cd _ ht, hcD, Nat.cast_sub hle]
    have e : n + ((spOff : Int) - ((2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t : Nat) : Int)) -
        (spOff : Int) = n - ((2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t : Nat) : Int) := by ring
    rw [e]
    exact S2.sub_emod_congr hn hcc.2
  rw [Int.toNat_of_nonneg (useHint_range _ _).1, ← useHint_emod, hcong, Int.toNat_of_nonneg hb.1,
    S2.w1Of_get cd hR ht, hhD]

/-- A row of the accumulator table is `w1` when each of its lanes is. -/
theorem S2.row_eq {cd : ByteArray} {m : ByteArray} {g k : Nat} (hR : 4 * g + k < 8)
    (hval : ∀ t, t < 256 → (lane (word m (ACC + 0x2000 * g + 32 * t)) k : Int) =
      ((w1Of cd)[4 * g + k]!)[t]!) :
    lanesPoly m (ACC + 0x2000 * g) k = (w1Of cd)[4 * g + k]! := by
  apply Array.ext (by rw [MlDsaOpt44.Proofs.lanesPoly_size, S2.w1Of_row cd hR])
  intro t h1 h2
  rw [MlDsaOpt44.Proofs.lanesPoly_size] at h1
  have e1 := MlDsaOpt44.Proofs.lanesPoly_get m (ACC + 0x2000 * g) k h1
  have e2 := hval t h1
  rw [getElem!_pos (lanesPoly m (ACC + 0x2000 * g) k) t
    (by rw [MlDsaOpt44.Proofs.lanesPoly_size]; exact h1)] at e1
  rw [getElem!_pos ((w1Of cd)[4 * g + k]!) t h2] at e2
  rw [e1, e2]

/-- One row group: after `intt` and `usehint`, the lanes of rows `4g + k`, `k < 4`, of the
accumulator table are `w1`. -/
theorem S2.w_group {cd : ByteArray} (hcd : HDR ≤ cd.size) {g : Nat} (hg : g < 2)
    {h : Array Fips204.Poly} (hhs : hintOf cd = some h) {c : Fips204.Poly} (hcs : cOf cd = some c)
    {m0 m1 m2 : ByteArray}
    (hA : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57)
    (hAc : ∀ k, k < 4 → ∀ t, t < 256 →
      ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
        (Fips204.q : Int) = 0)
    (hS : ∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t))
    (hH : ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
      word m0 (HP + 0x2000 * g + 32 * t) = pack4 b)
    (hHv : ∀ k, k < 4 → ∀ t, t < 256 →
      lane (word m0 (HP + 0x2000 * g + 32 * t)) k = (h[4 * g + k]![t]!).toNat)
    (hintt : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 30 ∧
          ((lane (word m1 (ACC + 0x2000 * g + 32 * t)) k : Int) -
            (Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) k))[t]!) % (Fips204.q : Int) = 0)
    (hfr1 : FrameExcept m0 m1 [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)])
    (huh : ∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) r < 2 ^ 30 ∧
          lane (word m1 (SP + 0x2000 * g + 32 * t)) r ≤ spOff ∧
          lane (word m1 (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m2 (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m1 (HP + 0x2000 * g + 32 * t)) r)
            ((lane (word m1 (ACC + 0x2000 * g + 32 * t)) r : Int) +
              lane (word m1 (SP + 0x2000 * g + 32 * t)) r - spOff)).toNat) :
    ∀ k, k < 4 → lanesPoly m2 (ACC + 0x2000 * g) k = (w1Of cd)[4 * g + k]! := by
  have hW := hintt hA
  have hsp1 : ∀ t, t < 256 → word m1 (SP + 0x2000 * g + 32 * t) = word m0 (SP + 0x2000 * g + 32 * t) :=
    fun t ht => word_frame hfr1 (lo := SP + 0x2000 * g) (hi := SP + 0x2000 * g + 8192)
      (by interval_cases g <;> avoids_tac) (by omega) (by omega)
  have hhp1 : ∀ t, t < 256 → word m1 (HP + 0x2000 * g + 32 * t) = word m0 (HP + 0x2000 * g + 32 * t) :=
    fun t ht => word_frame hfr1 (lo := HP + 0x2000 * g) (hi := HP + 0x2000 * g + 8192)
      (by interval_cases g <;> avoids_tac) (by omega) (by omega)
  have hspv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (SP + 0x2000 * g + 32 * t)) r =
      spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t) := fun t ht r hr => by
    rw [hsp1 t ht, hS t ht]
    exact MlDsaOpt44.Proofs.lane_pack4 (fun j _ => Nat.lt_of_le_of_lt (Nat.sub_le _ _) S2.spOff_lt) hr
  have hhpv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (HP + 0x2000 * g + 32 * t)) r ≤ 1 :=
    fun t ht r hr => by
      obtain ⟨b, hb, hw⟩ := hH t ht
      rw [hhp1 t ht, hw, MlDsaOpt44.Proofs.lane_pack4 (fun k hk => by have := hb k hk; omega) hr]
      exact hb r hr
  have hU := fun t ht => huh t ht fun r hr =>
    ⟨(hW r hr t ht).1, by rw [hspv t ht r hr]; exact Nat.sub_le _ _, hhpv t ht r hr⟩
  intro k hk
  refine S2.row_eq (by omega) fun t ht => ?_
  have hR : 4 * g + k < 8 := by omega
  have hinv : Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) k) =
      Fips204.nttInv (azRow cd (4 * g + k)) :=
    nttInv_congr _ _ (MlDsaOpt44.Proofs.lanesPoly_size m0 _ k) (S2.azRow_size cd _)
      fun t' ht' => by
        rw [MlDsaOpt44.Proofs.lanesPoly_get m0 _ k ht']
        exact hAc k hk t' ht'
  have hn := (hW k hk t ht).2
  rw [hinv] at hn
  rw [hU t ht k hk, hhp1 t ht, hHv k hk t ht, hspv t ht k hk]
  exact S2.w_lane hcd hg hk hR ht hhs hcs hn

theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 5686 [flag b] m) (callState s 5742 [flag b] m') Gas.pW := by
  sorry  -- glam: open item (package 2: `intt` with UseHint fused, no `usehint` call)

end MlDsaOptGlam87.Proofs
