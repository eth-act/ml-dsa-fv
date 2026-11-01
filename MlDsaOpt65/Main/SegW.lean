import MlDsaOpt65.Main.Base
import MlDsaOpt65.Fn.Ntt
import MlDsaOpt65.Fn.Hint
import MlDsaOpt65.Math
set_option warningAsError true
/-!
# Segment `6610 … 6688`: `intt`, `usehint`, `pack` per row group

For `g < 2`: `intt [ACC + 0x2000 g]` (`Â ẑ`, lanes `< 2^58`, to `w′ + c · t1 · 2^d` up to
`q`), `usehint [ACC + 0x2000 g]` against `SP + 0x2000 g` (`2^13 S' + n_neg ≡ 2^13 (c · t1)`)
and `HP + 0x2000 g`, `pack [nr, FIN + 256 + 2048 g, ACC + 0x2000 g]` (`w1Encode` of rows
`4g … 4g + nr − 1`, `nr = 4, 2`, into `FIN[8 + 64 g, 8 + 64 g + 16 nr)`; lanes 2, 3 of
`ACC + 0x2000` are junk rows, only bounded). With `FinMu`: `FinAt m (finBytes cd)` under
`ok3`.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt65.Proofs.Infra

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

/-- One row group: after `intt` and `usehint`, the lanes of rows `4g + k`, `k < nr`, of the
accumulator table are `w1`. -/
theorem S2.w_group {cd : ByteArray} (hcd : HDR ≤ cd.size) {g nr : Nat} (hg : g < 2)
    (hnr : 4 * g + nr ≤ 6) (hnr4 : nr ≤ 4)
    {h : Array Fips204.Poly} (hhs : hintOf cd = some h) {c : Fips204.Poly} (hcs : cOf cd = some c)
    {m0 m1 m2 : ByteArray}
    (hA : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 58)
    (hAc : ∀ k, k < nr → ∀ t, t < 256 →
      ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
        (Fips204.q : Int) = 0)
    (hS : ∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
      pack4 fun r => 2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t)
    (hSlt : ∀ r, r < 4 → ∀ t, t < 256 → 2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t < 2 ^ 29)
    (hH : ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
      word m0 (HP + 0x2000 * g + 32 * t) = pack4 b)
    (hHv : ∀ k, k < nr → ∀ t, t < 256 →
      lane (word m0 (HP + 0x2000 * g + 32 * t)) k = (h[4 * g + k]![t]!).toNat)
    (hintt : (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 58) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 27 ∧
          ((lane (word m1 (ACC + 0x2000 * g + 32 * t)) k : Int) -
            (Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) k))[t]!) % (Fips204.q : Int) = 0)
    (hfr1 : FrameExcept m0 m1 [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)])
    (huh : ∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m1 (ACC + 0x2000 * g + 32 * t)) r < 2 ^ 27 ∧
          lane (word m1 (SP + 0x2000 * g + 32 * t)) r < 2 ^ 29 ∧
          lane (word m1 (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m2 (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m1 (HP + 0x2000 * g + 32 * t)) r)
            ((lane (word m1 (ACC + 0x2000 * g + 32 * t)) r : Int) -
              lane (word m1 (SP + 0x2000 * g + 32 * t)) r)).toNat) :
    ∀ k, k < nr → lanesPoly m2 (ACC + 0x2000 * g) k = (w1Of cd)[4 * g + k]! := by
  have hW := hintt hA
  have hhD : hintD cd = h := by unfold hintD; rw [hhs]; rfl
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  have hc' : Fips204.sampleInBallOf P (cStream cd) = some c := hcs
  have hsp1 : ∀ t, t < 256 → word m1 (SP + 0x2000 * g + 32 * t) = word m0 (SP + 0x2000 * g + 32 * t) :=
    fun t ht => word_frame hfr1 (lo := SP + 0x2000 * g) (hi := SP + 0x2000 * g + 8192)
      (by interval_cases g <;> avoids_tac) (by omega) (by omega)
  have hhp1 : ∀ t, t < 256 → word m1 (HP + 0x2000 * g + 32 * t) = word m0 (HP + 0x2000 * g + 32 * t) :=
    fun t ht => word_frame hfr1 (lo := HP + 0x2000 * g) (hi := HP + 0x2000 * g + 8192)
      (by interval_cases g <;> avoids_tac) (by omega) (by omega)
  have hspv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (SP + 0x2000 * g + 32 * t)) r =
      2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t := fun t ht r hr => by
    rw [hsp1 t ht, hS t ht]
    exact MlDsaOpt44.Proofs.lane_pack4 (fun j hj => Nat.lt_trans (hSlt j hj t ht) (by norm_num)) hr
  have hhpv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (HP + 0x2000 * g + 32 * t)) r ≤ 1 :=
    fun t ht r hr => by
      obtain ⟨b, hb, hw⟩ := hH t ht
      rw [hhp1 t ht, hw, MlDsaOpt44.Proofs.lane_pack4 (fun k hk => by have := hb k hk; omega) hr]
      exact hb r hr
  have hU := fun t ht => huh t ht fun r hr =>
    ⟨(hW r hr t ht).1, by rw [hspv t ht r hr]; exact hSlt r hr t ht, hhpv t ht r hr⟩
  have hval : ∀ k, k < nr → ∀ t, t < 256 →
      (lane (word m2 (ACC + 0x2000 * g + 32 * t)) k : Int) = ((w1Of cd)[4 * g + k]!)[t]! :=
    fun k hk t ht => by
      have hk4 : k < 4 := by omega
      have hR : 4 * g + k < 6 := by omega
      rw [hU t ht k hk4, hhp1 t ht, hHv k hk t ht, hspv t ht k hk4]
      have hb := hintBitUnpack_range _ h hhs hR ht
      have hinv : Fips204.nttInv (lanesPoly m0 (ACC + 0x2000 * g) k) =
          Fips204.nttInv (azRow cd (4 * g + k)) :=
        nttInv_congr _ _ (MlDsaOpt44.Proofs.lanesPoly_size m0 _ k) (S2.azRow_size cd _)
          fun t' ht' => by
            rw [MlDsaOpt44.Proofs.lanesPoly_get m0 _ k ht']
            exact hAc k hk t' ht'
      have hlane := (hW k hk4 t ht).2
      rw [hinv] at hlane
      have hcong : ((lane (word m1 (ACC + 0x2000 * g + 32 * t)) k : Int) -
          ((2 ^ 13 * sPrime c cd (32 + 1280 * g) k t + nNeg c t : Nat) : Int)) %
            (Fips204.q : Int) = (wRow cd (4 * g + k))[t]! := by
        rw [S2.wRow_get cd _ ht, hcD]
        exact S2.sub_emod_congr hlane (csum_congr cd hcd c hcs hg hk4 hR ht).2
      rw [Int.toNat_of_nonneg (useHint_range _ _).1, ← useHint_emod, hcong,
        Int.toNat_of_nonneg hb.1, S2.w1Of_get cd hR ht, hhD]
  intro k hk
  apply Array.ext (by rw [MlDsaOpt44.Proofs.lanesPoly_size, S2.w1Of_row cd (by omega)])
  intro t h1 h2
  rw [MlDsaOpt44.Proofs.lanesPoly_size] at h1
  have e1 := MlDsaOpt44.Proofs.lanesPoly_get m2 (ACC + 0x2000 * g) k h1
  have e2 := hval k hk t h1
  rw [getElem!_pos (lanesPoly m2 (ACC + 0x2000 * g) k) t
    (by rw [MlDsaOpt44.Proofs.lanesPoly_size]; exact h1)] at e1
  rw [getElem!_pos ((w1Of cd)[4 * g + k]!) t h2] at e2
  rw [e1, e2]

theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 6610 [flag b] m) (callState s 6688 [flag b] m') Gas.pW := by
  have hb1 : Reach (callState s 6610 [flag b] m)
      (callState s Entry.intt [wd (ACC + 0x2000 * 0), wd 6620, flag b] m) 17 := by
    opt65_reach [2238, 2239, 2240, 2241] with [ACC, Entry.intt]
  obtain ⟨m1, hintt0, hfr1, hc1⟩ := intt_call hs (p := ACC + 0x2000 * 0) (Or.inl (by omega))
    (ret := 6620) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  have hb2 : Reach (callState s 6620 [flag b] m1)
      (callState s Entry.usehint [wd (ACC + 0x2000 * 0), wd 6631, flag b] m1) 18 := by
    opt65_reach [2242, 2243, 2244, 2245, 2246] with [ACC, Entry.usehint]
  obtain ⟨m2, huh0, hlt0, hfr2, hc2⟩ := usehint_call hs (ret := 6631) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (g := 0) (by norm_num)
  have hb3 : Reach (callState s 6631 [flag b] m2)
      (callState s Entry.pack [wd 4, wd (FIN + 256 + 2048 * 0), wd (ACC + 0x2000 * 0), wd 6648,
        flag b] m2) 24 := by
    opt65_reach [2247, 2248, 2249, 2250, 2251, 2252, 2253] with [ACC, FIN, Entry.pack]
  obtain ⟨m3, hpk0, hfr3, hc3⟩ := pack_call hs (ret := 6648) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
    (g := 0) (nr := 4) (by norm_num) (Or.inr rfl)
  have htbl3 : TblAt m3 :=
    TblAt.frame (TblAt.frame (TblAt.frame hI.tbl hfr1 (by avoids_tac)) hfr2 (by avoids_tac)) hfr3
      (by avoids_tac)
  have hb4 : Reach (callState s 6648 [flag b] m3)
      (callState s Entry.intt [wd (ACC + 0x2000 * 1), wd 6659, flag b] m3) 18 := by
    opt65_reach [2254, 2255, 2256, 2257, 2258] with [ACC, Entry.intt]
  obtain ⟨m4, hintt1, hfr4, hc4⟩ := intt_call hs (p := ACC + 0x2000 * 1) (Or.inr (by omega))
    (ret := 6659) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m3 htbl3
  have hb5 : Reach (callState s 6659 [flag b] m4)
      (callState s Entry.usehint [wd (ACC + 0x2000 * 1), wd 6670, flag b] m4) 18 := by
    opt65_reach [2259, 2260, 2261, 2262, 2263] with [ACC, Entry.usehint]
  obtain ⟨m5, huh1, hlt1, hfr5, hc5⟩ := usehint_call hs (ret := 6670) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m4
    (g := 1) (by norm_num)
  have hb6 : Reach (callState s 6670 [flag b] m5)
      (callState s Entry.pack [wd 2, wd (FIN + 256 + 2048 * 1), wd (ACC + 0x2000 * 1), wd 6687,
        flag b] m5) 24 := by
    opt65_reach [2264, 2265, 2266, 2267, 2268, 2269, 2270] with [ACC, FIN, Entry.pack]
  obtain ⟨m6, hpk1, hfr6, hc6⟩ := pack_call hs (ret := 6687) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m5
    (g := 1) (nr := 2) (by norm_num) (Or.inl rfl)
  have hb7 : Reach (callState s 6687 [flag b] m6) (callState s 6688 [flag b] m6) 1 := by
    opt65_reach [2271]
  refine ⟨m6, ⟨RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame (RC1Table.frame
      (RC1Table.frame hI.rc1 hfr1 (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4
      (by avoids_tac)) hfr5 (by avoids_tac)) hfr6 (by avoids_tac), ?_⟩,
    ((((((((((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).trans hc3).trans hb4).trans
      hc4).trans hb5).trans hc5).trans hb6).trans hc6).trans hb7).mono (by unfold Gas.pW; omega)⟩
  intro h3
  generalize hcdv : s.executionEnv.calldata = cd at hI h3 hpk0 hpk1 hcd huh0 huh1
  simp only [ok3, ok2, ok1, Bool.and_eq_true] at h3
  obtain ⟨⟨⟨hz, hh⟩, ha⟩, hc⟩ := h3
  obtain ⟨h, hhs⟩ := Option.isSome_iff_exists.mp (show (hintOf cd).isSome = true from hh)
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp (show (cOf cd).isSome = true from hc)
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  -- the row-group facts of `Inv8` at the state `m0` before the group's `intt`
  have hgroup : ∀ g nr, g < 2 → 4 * g + nr ≤ 6 → nr ≤ 4 → ∀ m0 : ByteArray,
      (∀ a, ACC + 0x2000 * g ≤ a → a + 32 ≤ ACC + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, SP + 0x2000 * g ≤ a → a + 32 ≤ SP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ a, HP + 0x2000 * g ≤ a → a + 32 ≤ HP + 0x2000 * g + 8192 → word m0 a = word m a) →
      (∀ k, k < 4 → ∀ t, t < 256 → lane (word m0 (ACC + 0x2000 * g + 32 * t)) k < 2 ^ 58) ∧
      (∀ k, k < nr → ∀ t, t < 256 →
        ((lane (word m0 (ACC + 0x2000 * g + 32 * t)) k : Int) - (azRow cd (4 * g + k))[t]!) %
          (Fips204.q : Int) = 0) ∧
      (∀ t, t < 256 → word m0 (SP + 0x2000 * g + 32 * t) =
        pack4 fun r => 2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t) ∧
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
  have hslt : ∀ g, g < 2 → ∀ r, r < 4 → ∀ t, t < 256 →
      2 ^ 13 * sPrime c cd (32 + 1280 * g) r t + nNeg c t < 2 ^ 29 :=
    fun g hg r hr t ht => csum_lt cd hcd c hcs hg hr ht
  obtain ⟨A0, Ac0, S0, H0', Hv0⟩ := hgroup 0 4 (by norm_num) (by norm_num) (le_refl _) m (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hrow0 := S2.w_group hcd (g := 0) (nr := 4) (by norm_num) (by norm_num) (le_refl _) hhs hcs
    A0 Ac0 S0 (hslt 0 (by norm_num)) H0' Hv0 hintt0 hfr1 huh0
  have e3 : ∀ lo, (lo = ACC + 0x2000 * 1 ∨ lo = SP + 0x2000 * 1 ∨ lo = HP + 0x2000 * 1) →
      ∀ a, lo ≤ a → a + 32 ≤ lo + 8192 → word m3 a = word m a := by
    intro lo hlo a h1 h2
    rcases hlo with rfl | rfl | rfl <;>
    rw [word_frame hfr3 (by avoids_tac) h1 h2, word_frame hfr2 (by avoids_tac) h1 h2,
      word_frame hfr1 (by avoids_tac) h1 h2]
  obtain ⟨A1, Ac1, S1, H1', Hv1⟩ := hgroup 1 2 (by norm_num) (by norm_num) (by norm_num) m3 (e3 _ (Or.inl rfl))
    (e3 _ (Or.inr (Or.inl rfl))) (e3 _ (Or.inr (Or.inr rfl)))
  have hrow1 := S2.w_group hcd (g := 1) (nr := 2) (by norm_num) (by norm_num) (by norm_num) hhs hcs
    A1 Ac1 S1 (hslt 1 (by norm_num)) H1' Hv1 hintt1 hfr4 huh1
  have hpw0 := hpk0 hlt0
  have hpw1 := hpk1 hlt1
  have hfmu : FinMu m6 cd :=
    FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame (FinMu.frame hI.fmu hfr1
      (by avoids_tac)) hfr2 (by avoids_tac)) hfr3 (by avoids_tac)) hfr4 (by avoids_tac)) hfr5
      (by avoids_tac)) hfr6 (by avoids_tac)
  intro x hx
  by_cases h8 : x < 8
  · rw [hfmu x h8, finBytes_le64_mu cd h8]
  · have hR : (x - 8) / 16 < 6 := by omega
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
    · have hg' : (x - 8) / 16 - 4 < 2 := by omega
      have hadr : FIN + 32 * x =
          FIN + 256 + 2048 * 1 + 32 * (16 * ((x - 8) / 16 - 4) + (x - 8) % 16) := by omega
      have hidx : 4 * 1 + ((x - 8) / 16 - 4) = (x - 8) / 16 := by omega
      have hw := hpw1 _ hg' _ hj
      rw [hrow1 _ hg', hidx] at hw
      rw [hadr, hw, ← finBytes_le64_w1 cd hR hj, ← hxe]

end MlDsaOpt65.Proofs
