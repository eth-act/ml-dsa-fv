import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Fn.Ntt
import MlDsaOptGlam65.Fn.Hint
import MlDsaOpt65.Math
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/SegW.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# Segment `6237 … 6293`: `intt` (UseHint fused, v4), `pack` per row group

For `g < 2`: `intt [ACC + 0x2000 g]` (`Â ẑ`, lanes `< 2^57`) applies UseHint in its last
pass against `SP + 0x2000 g` (`spOff − (2^13 S' + n_neg)`, `2^13 S' + n_neg ≡ 2^13 (c · t1)`)
and `HP + 0x2000 g` (`S2.w_group`: the rows are `w1`, every lane `< 16`), then
`pack [nr, FIN + 256 + 2048 g, ACC + 0x2000 g]` (`w1Encode` of rows
`4g … 4g + nr − 1`, `nr = 4, 2`, into `FIN[8 + 64 g, 8 + 64 g + 16 nr)`; lanes 2, 3 of
`ACC + 0x2000` are junk rows, only bounded). With `FinMu`: `FinAt m (finBytes cd)` under
`ok3`.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam65.Proofs.Infra

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

theorem S2.w1Of_row (cd : ByteArray) {r : Nat} (hr : r < 6) : ((w1Of cd)[r]!).size = 256 := by
  unfold w1Of
  rw [MlDsaOpt44.Proofs.getElem!_map_range 6 r _ hr]
  simp

theorem S2.w1Of_get (cd : ByteArray) {r t : Nat} (hr : r < 6) (ht : t < 256) :
    ((w1Of cd)[r]!)[t]! = Fips204.useHint P (hintD cd)[r]![t]! (wRow cd r)[t]! := by
  unfold w1Of
  rw [MlDsaOpt44.Proofs.getElem!_map_range 6 r _ hr,
    MlDsaOpt44.Proofs.getElem!_map_range 256 t _ ht]

theorem S2.spOff_lt : spOff < 2 ^ 64 := by unfold spOff Fips204.q; norm_num

/-- One lane of a row: `UseHint(h, NTT⁻¹(Â ẑ)[t] + (spOff − s') − spOff)` with
`s' ≡ 2^13 (c · t1)` is `w1[t]` (the `intt` (65) / `usehint` (87) output). -/
theorem S2.w_lane {cd : ByteArray} (hcd : HDR ≤ cd.size) {g k t : Nat} (hg : g < 2) (hk : k < 4)
    (hR : 4 * g + k < 6) (ht : t < 256)
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
theorem S2.row_eq {cd : ByteArray} {m : ByteArray} {g k : Nat} (hR : 4 * g + k < 6)
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

/-- One row group: after the fused `intt` (UseHint in its last pass), the lanes of rows
`4g + k`, `k < nr`, of the accumulator table are `w1`; every lane is below `16`. -/
theorem S2.w_group {cd : ByteArray} (hcd : HDR ≤ cd.size) {g nr : Nat} (hg : g < 2)
    (hnr : 4 * g + nr ≤ 6) (hnr4 : nr ≤ 4)
    {h : Array Fips204.Poly} (hhs : hintOf cd = some h) {c : Fips204.Poly} (hcs : cOf cd = some c)
    {m0 m1 : ByteArray}
    (hA : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57)
    (hAc : ∀ k, k < nr → ∀ t, t < 256 →
      ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
        (Fips204.q : Int) = 0)
    (hS : ∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
      pack4 fun r => spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t))
    (hH : ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
      word m0 (HP + 0x2000 * g + 32 * t) = pack4 b)
    (hHv : ∀ k, k < nr → ∀ t, t < 256 →
      lane (word m0 (HP + 0x2000 * g + 32 * t)) k = (h[4 * g + k]![t]!).toNat)
    (hintt : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 0x2000 * g + 32 * t)) r ≤ spOff ∧
          lane (word m0 (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m0 (HP + 0x2000 * g + 32 * t)) r)
            ((Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) r))[t]! +
              lane (word m0 (SP + 0x2000 * g + 32 * t)) r - spOff)).toNat) :
    (∀ k, k < nr → lanesPoly m1 (ACC + 0x2000 * g) k = (w1Of cd)[4 * g + k]!) ∧
      ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) r < 16 := by
  have hspv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 0x2000 * g + 32 * t)) r =
      spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t) := fun t ht r hr => by
    rw [hS t ht]
    exact MlDsaOpt44.Proofs.lane_pack4 (fun j _ => Nat.lt_of_le_of_lt (Nat.sub_le _ _) S2.spOff_lt) hr
  have hhpv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (HP + 0x2000 * g + 32 * t)) r ≤ 1 :=
    fun t ht r hr => by
      obtain ⟨b, hb, hw⟩ := hH t ht
      rw [hw, MlDsaOpt44.Proofs.lane_pack4 (fun k hk => by have := hb k hk; omega) hr]
      exact hb r hr
  have hU := hintt hA fun t ht r hr => ⟨by rw [hspv t ht r hr]; exact Nat.sub_le _ _, hhpv t ht r hr⟩
  refine ⟨fun k hk => S2.row_eq (by omega) fun t ht => ?_, fun t ht r hr => ?_⟩
  · have hk4 : k < 4 := by omega
    have hR : 4 * g + k < 6 := by omega
    have hinv : Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) k) =
        Fips204.nttInv (azRow cd (4 * g + k)) :=
      nttInv_congr _ _ (MlDsaOpt44.Proofs.lanesPoly_size m0 _ k) (S2.azRow_size cd _)
        fun t' ht' => by
          rw [MlDsaOpt44.Proofs.lanesPoly_get m0 _ k ht']
          exact hAc k hk t' ht'
    rw [hU t ht k hk4, hHv k hk t ht, hspv t ht k hk4, hinv]
    exact S2.w_lane hcd hg hk4 hR ht hhs hcs (by simp)
  · rw [hU t ht r hr]
    have := (useHint_range (lane (word m0 (HP + 0x2000 * g + 32 * t)) r)
      ((Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) r))[t]! +
        lane (word m0 (SP + 0x2000 * g + 32 * t)) r - spOff))
    omega

theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 5908 [flag b] m) (callState s 5964 [flag b] m') Gas.pW := by
  have hb1 : Reach (callState s 5908 [flag b] m)
      (callState s Entry.intt [wd (ACC + 0x2000 * 0), wd 5918, flag b] m) 17 := by
    glam65_rreach [2103, 2104, 2105, 2106] with [ACC, Entry.intt]
  obtain ⟨m1, hintt0, hfr1, hc1⟩ := intt_call hs (g := 0) (by norm_num)
    (ret := 5918) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  have hb2 : Reach (callState s 5918 [flag b] m1)
      (callState s Entry.pack [wd 4, wd (FIN + 256 + 2048 * 0), wd (ACC + 0x2000 * 0), wd 5935,
        flag b] m1) 24 := by
    glam65_rreach [2107, 2108, 2109, 2110, 2111, 2112, 2113] with [ACC, FIN, Entry.pack]
  obtain ⟨m2, hpk0, hfr2, hc2⟩ := pack_call hs (ret := 5935) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (g := 0) (nr := 4) (by norm_num) (Or.inr rfl)
  have htbl2 : TblAt m2 :=
    TblAt.frame (TblAt.frame hI.tbl hfr1 (by avoids_tac)) hfr2 (by avoids_tac)
  have hb3 : Reach (callState s 5935 [flag b] m2)
      (callState s Entry.intt [wd (ACC + 0x2000 * 1), wd 5946, flag b] m2) 18 := by
    glam65_rreach [2114, 2115, 2116, 2117, 2118] with [ACC, Entry.intt]
  obtain ⟨m3, hintt1, hfr3, hc3⟩ := intt_call hs (g := 1) (by norm_num)
    (ret := 5946) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2 htbl2
  have hb4 : Reach (callState s 5946 [flag b] m3)
      (callState s Entry.pack [wd 2, wd (FIN + 256 + 2048 * 1), wd (ACC + 0x2000 * 1), wd 5963,
        flag b] m3) 24 := by
    glam65_rreach [2119, 2120, 2121, 2122, 2123, 2124, 2125] with [ACC, FIN, Entry.pack]
  obtain ⟨m4, hpk1, hfr4, hc4⟩ := pack_call hs (ret := 5963) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3
    (g := 1) (nr := 2) (by norm_num) (Or.inl rfl)
  have hb5 : Reach (callState s 5963 [flag b] m4) (callState s 5964 [flag b] m4) 1 := by
    glam65_rreach [2126]
  refine ⟨m4, ⟨RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame hI.rc1 hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac), ?_⟩,
    ((((((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).trans hc3).trans hb4).trans hc4).trans
      hb5).mono (by unfold Gas.pW; omega)⟩
  intro h3
  generalize hcdv : s.executionEnv.calldata = cd at hI h3 hpk0 hpk1 hcd
  simp only [ok3, ok2, Bool.and_eq_true] at h3
  obtain ⟨⟨⟨hz, ha⟩, hh⟩, hc⟩ := h3
  obtain ⟨h, hhs⟩ := Option.isSome_iff_exists.mp (show (hintOf cd).isSome = true from hh)
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp (show (cOf cd).isSome = true from hc)
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  -- the row-group facts of `Inv8` at the state `m0` before the group's `intt`
  have hgroup : ∀ g nr, g < 2 → 4 * g + nr ≤ 6 → nr ≤ 4 → ∀ m0 : ByteArray,
      (∀ a, ACC + 0x2000 * g ≤ a → a + 32 ≤ ACC + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, SP + 0x2000 * g ≤ a → a + 32 ≤ SP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, HP + 0x2000 * g ≤ a → a + 32 ≤ HP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) ∧
      (∀ k, k < nr → ∀ t, t < 256 →
        ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
          (Fips204.q : Int) = 0) ∧
      (∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
        pack4 fun r => spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t)) ∧
      (∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
        word m0 (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
      (∀ k, k < nr → ∀ t, t < 256 →
        lane (word m0 (HP + 0x2000 * g + 32 * t)) k = (h[4 * g + k]![t]!).toNat) := by
    intro g nr hg hnr hnr4 m0 eA eS eH
    refine ⟨fun k hk t ht => ?_, fun k hk t ht => ?_, fun t ht => ?_, fun t ht => ?_,
      fun k hk t ht => ?_⟩
    · rw [eA _ (by omega) (by omega)]; exact (hI.acc ha).1 g hg k hk t ht
    · have := (hI.acc ha).2 (4 * g + k) (by omega) t ht
      rwa [show accAddr (4 * g + k) t = ACC + 0x2000 * g + 32 * t by unfold accAddr; omega,
        show (4 * g + k) % 4 = k by omega, ← eA _ (by omega) (by omega)] at this
    · rw [eS _ (by omega) (by omega), hI.sp hc g hg t ht, hcD]
    · rw [eH _ (by omega) (by omega)]; exact hI.hp.1 g hg t ht
    · have := hI.hp.2 h hhs (4 * g + k) (by omega) t ht
      rwa [show hpAddr (4 * g + k) t = HP + 0x2000 * g + 32 * t by unfold hpAddr; omega,
        show (4 * g + k) % 4 = k by omega, ← eH _ (by omega) (by omega)] at this
  obtain ⟨A0, Ac0, S0, H0', Hv0⟩ := hgroup 0 4 (by norm_num) (by norm_num) (le_refl _) m
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  obtain ⟨hrow0, hlt0⟩ := S2.w_group hcd (g := 0) (nr := 4) (by norm_num) (by norm_num) (le_refl _)
    hhs hcs A0 Ac0 S0 H0' Hv0 hintt0
  have e2 : ∀ lo, (lo = ACC + 0x2000 * 1 ∨ lo = SP + 0x2000 * 1 ∨ lo = HP + 0x2000 * 1) →
      ∀ a, lo ≤ a → a + 32 ≤ lo + 8192 → word m2 a = word m a := by
    intro lo hlo a h1 h2
    rcases hlo with rfl | rfl | rfl <;>
    rw [word_frame hfr2 (by avoids_tac) h1 h2, word_frame hfr1 (by avoids_tac) h1 h2]
  obtain ⟨A1, Ac1, S1, H1', Hv1⟩ := hgroup 1 2 (by norm_num) (by norm_num) (by norm_num) m2
    (e2 _ (Or.inl rfl)) (e2 _ (Or.inr (Or.inl rfl))) (e2 _ (Or.inr (Or.inr rfl)))
  obtain ⟨hrow1, hlt1⟩ := S2.w_group hcd (g := 1) (nr := 2) (by norm_num) (by norm_num) (by norm_num)
    hhs hcs A1 Ac1 S1 H1' Hv1 hintt1
  have hpw0 := hpk0 hlt0
  have hpw1 := hpk1 hlt1
  have hfmu : FinMu m4 cd :=
    FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame hI.fmu hfr1 (by avoids_tac)) hfr2
      (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)
  intro x hx
  by_cases h8 : x < 8
  · rw [hfmu x h8, finBytes_le64_mu cd h8]
  · have hR : (x - 8) / 16 < 6 := by omega
    have hj : (x - 8) % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hxe : x = 8 + 16 * ((x - 8) / 16) + (x - 8) % 16 := by omega
    by_cases hg : (x - 8) / 16 < 4
    · have hfin : ∀ a, FIN + 256 ≤ a → a + 32 ≤ FIN + 2304 → word m4 a = word m2 a :=
        fun a h1 h2 => by
          rw [word_frame hfr4 (by avoids_tac) h1 h2, word_frame hfr3 (by avoids_tac) h1 h2]
      have ha := hfin (FIN + 256 + 2048 * 0 + 32 * (16 * ((x - 8) / 16) + (x - 8) % 16))
        (by clear * - hx h8 hg; omega) (by clear * - hx h8 hg; omega)
      have hadr : FIN + 32 * x = FIN + 256 + 2048 * 0 + 32 * (16 * ((x - 8) / 16) + (x - 8) % 16) :=
        by omega
      have hidx : 4 * 0 + (x - 8) / 16 = (x - 8) / 16 := by omega
      have hw := hpw0 _ hg _ hj
      rw [hrow0 _ hg, hidx] at hw
      rw [hadr, ha, hw, ← finBytes_le64_w1 cd hR hj, ← hxe]
    · have hg' : (x - 8) / 16 - 4 < 2 := by omega
      have hadr : FIN + 32 * x =
          FIN + 256 + 2048 * 1 + 32 * (16 * ((x - 8) / 16 - 4) + (x - 8) % 16) := by omega
      have hidx : 4 * 1 + ((x - 8) / 16 - 4) = (x - 8) / 16 := by omega
      have hw := hpw1 _ hg' _ hj
      rw [hrow1 _ hg', hidx] at hw
      rw [hadr, hw, ← finBytes_le64_w1 cd hR hj, ← hxe]

end MlDsaOptGlam65.Proofs
