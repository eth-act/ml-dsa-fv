import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Ntt
import MlDsaOpt87.Fn.Hint
import MlDsaOpt87.Math
/-!
# Segment `6727 … 6805`: `intt`, `usehint`, `pack` per row group

For `g < 2`: `intt [ACC + 0x2000 g]` (`Â ẑ`, lanes `< 2^57`, to lanes `< 2^30` congruent to
`NTT⁻¹`), `usehint [ACC + 0x2000 g]` (`UseHint(HP_g, W + SP_g − spOff)`, `SP_g` holding
`spOff − (2^13 S' + n_neg)`, `2^13 S' + n_neg ≡ 2^13 (c · t1)`; `S2.w_group`),
`pack [4, FIN + 256 + 2048 g, ACC + 0x2000 g]` (`w1Encode` of rows `4g … 4g + 3` into `FIN[8 + 64 g, 72 + 64 g)`). With `FinMu`: `FinAt m (finBytes cd)` under
`ok3`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

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
      Reach (callState s 6727 [flag b] m) (callState s 6805 [flag b] m') Gas.pW := by
  have hb1 : Reach (callState s 6727 [flag b] m)
      (callState s Entry.intt [wd (ACC + 0x2000 * 0), wd 6737, flag b] m) 17 := by
    opt87_reach [2235, 2236, 2237, 2238] with [ACC, Entry.intt]
  obtain ⟨m1, hintt0, hfr1, hc1⟩ := intt_call hs (p := ACC + 0x2000 * 0) (Or.inl (by omega))
    (ret := 6737) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  have hb2 : Reach (callState s 6737 [flag b] m1)
      (callState s Entry.usehint [wd (ACC + 0x2000 * 0), wd 6748, flag b] m1) 18 := by
    opt87_reach [2239, 2240, 2241, 2242, 2243] with [ACC, Entry.usehint]
  obtain ⟨m2, huh0, hlt0, hfr2, hc2⟩ := usehint_call hs (ret := 6748) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (g := 0) (by norm_num)
  have hb3 : Reach (callState s 6748 [flag b] m2)
      (callState s Entry.pack [wd 4, wd (FIN + 256 + 2048 * 0), wd (ACC + 0x2000 * 0), wd 6765,
        flag b] m2) 24 := by
    opt87_reach [2244, 2245, 2246, 2247, 2248, 2249, 2250] with [ACC, FIN, Entry.pack]
  obtain ⟨m3, hpk0, hfr3, hc3⟩ := pack_call hs (ret := 6765) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
    (g := 0) (by norm_num)
  have htbl3 : TblAt m3 :=
    TblAt.frame (TblAt.frame (TblAt.frame hI.tbl hfr1 (by avoids_tac)) hfr2 (by avoids_tac)) hfr3
      (by avoids_tac)
  have hb4 : Reach (callState s 6765 [flag b] m3)
      (callState s Entry.intt [wd (ACC + 0x2000 * 1), wd 6776, flag b] m3) 18 := by
    opt87_reach [2251, 2252, 2253, 2254, 2255] with [ACC, Entry.intt]
  obtain ⟨m4, hintt1, hfr4, hc4⟩ := intt_call hs (p := ACC + 0x2000 * 1) (Or.inr (by omega))
    (ret := 6776) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3 htbl3
  have hb5 : Reach (callState s 6776 [flag b] m4)
      (callState s Entry.usehint [wd (ACC + 0x2000 * 1), wd 6787, flag b] m4) 18 := by
    opt87_reach [2256, 2257, 2258, 2259, 2260] with [ACC, Entry.usehint]
  obtain ⟨m5, huh1, hlt1, hfr5, hc5⟩ := usehint_call hs (ret := 6787) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (g := 1) (by norm_num)
  have hb6 : Reach (callState s 6787 [flag b] m5)
      (callState s Entry.pack [wd 4, wd (FIN + 256 + 2048 * 1), wd (ACC + 0x2000 * 1), wd 6804,
        flag b] m5) 24 := by
    opt87_reach [2261, 2262, 2263, 2264, 2265, 2266, 2267] with [ACC, FIN, Entry.pack]
  obtain ⟨m6, hpk1, hfr6, hc6⟩ := pack_call hs (ret := 6804) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (g := 1) (by norm_num)
  have hb7 : Reach (callState s 6804 [flag b] m6) (callState s 6805 [flag b] m6) 1 := by
    opt87_reach [2268]
  refine ⟨m6, ⟨RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame
      (RC1Table.frame hI.rc1 hfr1 (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4
      (by avoids_tac)) hfr5 (by avoids_tac)) hfr6 (by avoids_tac), ?_⟩,
    ((((((((((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).trans hc3).trans hb4).trans
      hc4).trans hb5).trans hc5).trans hb6).trans hc6).trans hb7).mono (by unfold Gas.pW; omega)⟩
  intro h3
  generalize hcdv : s.executionEnv.calldata = cd at hI h3 hpk0 hpk1 hcd huh0 huh1
  simp only [ok3, ok2, Bool.and_eq_true] at h3
  obtain ⟨⟨⟨hz, ha⟩, hh⟩, hc⟩ := h3
  obtain ⟨h, hhs⟩ := Option.isSome_iff_exists.mp (show (hintOf cd).isSome = true from hh)
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp (show (cOf cd).isSome = true from hc)
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  -- the row-group facts of `Inv8` at the state `m0` before the group's `intt`
  have hgroup : ∀ g, g < 2 → ∀ m0 : ByteArray,
      (∀ a, ACC + 0x2000 * g ≤ a → a + 32 ≤ ACC + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, SP + 0x2000 * g ≤ a → a + 32 ≤ SP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, HP + 0x2000 * g ≤ a → a + 32 ≤ HP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 57) ∧
      (∀ k, k < 4 → ∀ t, t < 256 →
        ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
          (Fips204.q : Int) = 0) ∧
      (∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
        pack4 fun r => spOff - (2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t)) ∧
      (∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
        word m0 (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
      (∀ k, k < 4 → ∀ t, t < 256 →
        lane (word m0 (HP + 0x2000 * g + 32 * t)) k = (h[4 * g + k]![t]!).toNat) := by
    intro g hg m0 eA eS eH
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
  obtain ⟨A0, Ac0, S0, H0', Hv0⟩ := hgroup 0 (by norm_num) m (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hrow0 := S2.w_group hcd (g := 0) (by norm_num) hhs hcs A0 Ac0 S0 H0' Hv0 hintt0 hfr1 huh0
  have e3 : ∀ lo, (lo = ACC + 0x2000 * 1 ∨ lo = SP + 0x2000 * 1 ∨ lo = HP + 0x2000 * 1) →
      ∀ a, lo ≤ a → a + 32 ≤ lo + 8192 → word m3 a = word m a := by
    intro lo hlo a h1 h2
    rcases hlo with rfl | rfl | rfl <;>
    rw [word_frame hfr3 (by avoids_tac) h1 h2, word_frame hfr2 (by avoids_tac) h1 h2,
      word_frame hfr1 (by avoids_tac) h1 h2]
  obtain ⟨A1, Ac1, S1, H1', Hv1⟩ := hgroup 1 (by norm_num) m3 (e3 _ (Or.inl rfl))
    (e3 _ (Or.inr (Or.inl rfl))) (e3 _ (Or.inr (Or.inr rfl)))
  have hrow1 := S2.w_group hcd (g := 1) (by norm_num) hhs hcs A1 Ac1 S1 H1' Hv1 hintt1 hfr4 huh1
  have hpw0 := hpk0 hlt0
  have hpw1 := hpk1 hlt1
  have hfmu : FinMu m6 cd :=
    FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame hI.fmu hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)) hfr5
      (by avoids_tac)) hfr6 (by avoids_tac)
  intro x hx
  by_cases h8 : x < 8
  · rw [hfmu x h8, finBytes_le64_mu cd h8]
  · have hR : (x - 8) / 16 < 8 := by omega
    have hj : (x - 8) % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hxe : x = 8 + 16 * ((x - 8) / 16) + (x - 8) % 16 := by omega
    by_cases hg : (x - 8) / 16 < 4
    · have hfin : ∀ a, FIN + 256 ≤ a → a + 32 ≤ FIN + 2304 → word m6 a = word m3 a :=
        fun a h1 h2 => by
          rw [word_frame hfr6 (by avoids_tac) h1 h2, word_frame hfr5 (by avoids_tac) h1 h2,
            word_frame hfr4 (by avoids_tac) h1 h2]
      have ha := hfin (FIN + 256 + 2048 * 0 + 32 * (16 * ((x - 8) / 16) + (x - 8) % 16))
        (by clear * - hx h8 hg; omega) (by clear * - hx h8 hg; omega)
      have hadr : FIN + 32 * x = FIN + 256 + 2048 * 0 + 32 * (16 * ((x - 8) / 16) + (x - 8) % 16) :=
        by omega
      have hidx : 4 * 0 + (x - 8) / 16 = (x - 8) / 16 := by omega
      have hw := hpw0 _ hg _ hj
      rw [hrow0 _ hg, hidx] at hw
      rw [hadr, ha, hw, ← finBytes_le64_w1 cd hR hj, ← hxe]
    · have hg' : (x - 8) / 16 - 4 < 4 := by omega
      have hadr : FIN + 32 * x =
          FIN + 256 + 2048 * 1 + 32 * (16 * ((x - 8) / 16 - 4) + (x - 8) % 16) := by omega
      have hidx : 4 * 1 + ((x - 8) / 16 - 4) = (x - 8) / 16 := by omega
      have hw := hpw1 _ hg' _ hj
      rw [hrow1 _ hg', hidx] at hw
      rw [hadr, hw, ← finBytes_le64_w1 cd hR hj, ← hxe]

end MlDsaOpt87.Proofs
