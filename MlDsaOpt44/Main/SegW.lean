import MlDsaOpt44.Main.Base
set_option warningAsError true
/-!
# Segment `5963 … 6001`: `intt`, `usehint`, `pack`

`ACC` (`Â ẑ`, lanes `< 2^58`) goes through the inverse NTT (`w′ + c · t1 · 2^d`
up to `q`), `UseHint` against `SP` (`2^13 S' + n_neg ≡ 2^13 (c · t1)`) and
`HP`, and `w1Encode` into `FIN[8, 104)`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem HPAt.lane_le {m : ByteArray} {cd : ByteArray} (hp : HPAt m cd) {t r : Nat} (ht : t < 256)
    (hr : r < 4) : lane (word m (HP + 32 * t)) r ≤ 1 := by
  obtain ⟨b, hb, hw⟩ := hp.1 t ht
  rw [hw, lane_pack4 (fun k hk => by have := hb k hk; omega) hr]
  exact hb r hr

/-- Subtraction respects congruence mod `q`. -/
theorem sub_emod_congr {a b c d : Int} (h1 : (a - b) % (Fips204.q : Int) = 0)
    (h2 : (c - d) % (Fips204.q : Int) = 0) :
    (a - c) % (Fips204.q : Int) = (b - d) % (Fips204.q : Int) := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  have := dvd_sub (Int.dvd_of_emod_eq_zero h1) (Int.dvd_of_emod_eq_zero h2)
  have e : a - c - (b - d) = (a - b) - (c - d) := by ring
  rw [e]; exact this

theorem seg_w {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : Inv8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv9 s.executionEnv.calldata m' ∧
      Reach (callState s 5963 [flag b] m) (callState s 6001 [flag b] m') Gas.pW := by
  have hb1 : Reach (callState s 5963 [flag b] m) (callState s 18164 [wd ACC, wd 5973, flag b] m) 17 := by
    opt44_reach [2002, 2003, 2004, 2005] with [ACC]
  obtain ⟨m1, hintt, hfr1, hc1⟩ := intt_call hs (ret := 5973) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  have hb2 : Reach (callState s 5973 [flag b] m1) (callState s 15457 [wd ACC, wd 5984, flag b] m1) 18 := by
    opt44_reach [2006, 2007, 2008, 2009, 2010] with [ACC]
  obtain ⟨m2, huh, hfr2, hc2⟩ := usehint_call hs (ret := 5984) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
  have hb3 : Reach (callState s 5984 [flag b] m2)
      (callState s 15808 [wd 4, wd (FIN + 256), wd ACC, wd 6000, flag b] m2) 24 := by
    opt44_reach [2011, 2012, 2013, 2014, 2015, 2016, 2017] with [ACC, FIN]
  obtain ⟨m3, hpk, hfr3, hc3⟩ := pack_call hs (ret := 6000) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m2
  have hb4 : Reach (callState s 6000 [flag b] m3) (callState s 6001 [flag b] m3) 1 := by
    opt44_reach [2018]
  refine ⟨m3, ⟨((hI.rc1.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac)).frame hfr3
    (by avoids_tac), ?_⟩,
    ((((((hb1.trans hc1).trans hb2).trans hc2).trans hb3).trans hc3).trans hb4).mono
      (by unfold Gas.pW; omega)⟩
  intro h3
  generalize hcdv : s.executionEnv.calldata = cd at hI h3 hpk hcd ⊢
  simp only [ok3, ok2, ok1, Bool.and_eq_true] at h3
  obtain ⟨⟨⟨hz, hh⟩, ha⟩, hc⟩ := h3
  -- the hint, c
  obtain ⟨h, hhs⟩ := Option.isSome_iff_exists.mp (show (hintOf cd).isSome = true from hh)
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.mp (show (cOf cd).isSome = true from hc)
  have hcs' : Fips204.sampleInBallOf (cStream cd) = some c := hcs
  have hhD : hintD cd = h := by unfold hintD; rw [hhs]; rfl
  have hcD : cD cd = c := by unfold cD; rw [hcs]; rfl
  -- inverse NTT
  have hin : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 58 :=
    fun k hk t ht => (hI.acc ha k hk t ht).1
  have hW := hintt hin
  have hinv : ∀ k, k < 4 → Fips204.nttInv (lanesPoly m ACC k) = Fips204.nttInv (azRow cd k) :=
    fun k hk => nttInv_congr _ _ (lanesPoly_size m ACC k) (azRow_size cd k) fun t ht => by
      rw [lanesPoly_get m ACC k ht]
      exact (hI.acc ha k hk t ht).2
  -- SP and HP are untouched by intt
  have hsp1 : ∀ t, t < 256 → word m1 (SP + 32 * t) = word m (SP + 32 * t) := fun t ht =>
    word_frame hfr1 (lo := SP) (hi := SP + 8192) (by avoids_tac) (by omega) (by omega)
  have hhp1 : ∀ t, t < 256 → word m1 (HP + 32 * t) = word m (HP + 32 * t) := fun t ht =>
    word_frame hfr1 (lo := HP) (hi := HP + 8192) (by avoids_tac) (by omega) (by omega)
  have hspv : ∀ t, t < 256 → ∀ r, r < 4 → lane (word m1 (SP + 32 * t)) r =
      2 ^ 13 * sPrime c cd r t + nNeg c t := fun t ht r hr => by
    rw [hsp1 t ht, hI.sp hc t ht, hcD]
    exact lane_pack4 (fun j hj => Nat.lt_trans (csum_congr cd hcd c hcs' hj ht).1 (by norm_num)) hr
  -- UseHint
  have hU := fun t ht => huh t ht fun r hr => ⟨(hW r hr t ht).1,
    by rw [hspv t ht r hr]; exact (csum_congr cd hcd c hcs' hr ht).1,
    by rw [hhp1 t ht]; exact hI.hp.lane_le ht hr⟩
  have hval : ∀ t, t < 256 → ∀ r, r < 4 →
      (lane (word m2 (ACC + 32 * t)) r : Int) = ((w1Of cd)[r]!)[t]! := fun t ht r hr => by
    rw [hU t ht r hr, hhp1 t ht, hI.hp.2 h hhs t ht r hr, hspv t ht r hr]
    have hb := hintBitUnpack_range _ h hhs hr ht
    have hlane := (hW r hr t ht).2
    rw [hinv r hr] at hlane
    have hcong : ((lane (word m1 (ACC + 32 * t)) r : Int) -
        ((2 ^ 13 * sPrime c cd r t + nNeg c t : Nat) : Int)) % (Fips204.q : Int) =
        (wRow cd r)[t]! := by
      rw [wRow_get cd r ht, hcD]
      exact sub_emod_congr hlane (csum_congr cd hcd c hcs' hr ht).2
    rw [Int.toNat_of_nonneg (useHint_range _ _).1, ← useHint_emod, hcong,
      Int.toNat_of_nonneg hb.1, w1Of_get cd hr ht, hhD]
  -- pack
  have hpk' := hpk fun t ht r hr => by
    have h1 := hval t ht r hr
    have h2 := (useHint_range ((hintD cd)[r]![t]!) ((wRow cd r)[t]!)).2
    rw [w1Of_get cd hr ht] at h1
    omega
  have hrow : ∀ r, r < 4 → lanesPoly m2 ACC r = (w1Of cd)[r]! := fun r hr => by
    apply Array.ext (by rw [lanesPoly_size, w1Of_row cd hr]; simp)
    intro t h1 h2
    rw [lanesPoly_size] at h1
    have e1 := lanesPoly_get m2 ACC r h1
    have e2 := hval t h1 r hr
    rw [getElem!_pos (lanesPoly m2 ACC r) t (by rw [lanesPoly_size]; exact h1)] at e1
    rw [getElem!_pos ((w1Of cd)[r]!) t h2] at e2
    rw [e1, e2]
  have hfmu : FinMu m3 cd :=
    ((hI.fmu.frame hfr1 (by avoids_tac)).frame hfr2 (by avoids_tac)).frame hfr3 (by avoids_tac)
  intro x hx
  by_cases h8 : x < 8
  · rw [hfmu x h8, finBytes_le64_mu cd h8]
  · have hr : (x - 8) / 24 < 4 := by omega
    have hj : (x - 8) % 24 < 24 := Nat.mod_lt _ (by norm_num)
    have hxe : x = 8 + 24 * ((x - 8) / 24) + (x - 8) % 24 := by omega
    have hpw := hpk' _ hr _ hj
    rw [hrow _ hr] at hpw
    rw [show FIN + 32 * x = FIN + 256 + 32 * (24 * ((x - 8) / 24) + (x - 8) % 24) by omega, hpw,
      ← finBytes_le64_w1 cd hr hj, ← hxe]

end MlDsaOpt44.Proofs
