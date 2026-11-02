import MlDsaOpt87.Main.Base
import MlDsaOpt87.Fn.Ntt
import MlDsaOpt87.Fn.Decode
import MlDsaOpt87.Math
set_option warningAsError true
/-! # Segment `3100 … 3122`: `ntt(ZH)`, `ntt(ZH2)`, the return `JUMPDEST`.

Every lane of both `ZAt` tables is a `zLane ∈ [zLo, zHi]` (v4 bias `8q`); polynomials `0 … 6` (lanes `0 … 3`
of `ZH`, lanes `0 … 2` of `ZH2`) give `ẑ` via `ntt_zLane`; lane 3 of `ZH2` is transformed
garbage, unconstrained. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

theorem S2.zLane_lt (cd : ByteArray) (k t : Nat) : zLane cd k t < 2 ^ 28 := by
  unfold zLane
  have : Fips204.q = 8380417 := rfl
  omega

theorem S2.zLane_range (cd : ByteArray) (k t : Nat) : zLo ≤ zLane cd k t ∧ zLane cd k t ≤ zHi := by
  have h := DecodeZ.rawZ_lt cd k t
  have : Fips204.q = 8380417 := rfl
  unfold zLane zLo zHi
  omega

/-- The lanes `ZAt` stores at a table, as an `Array` of polynomials. -/
theorem S2.lanesPoly_zLane {m : ByteArray} {cd : ByteArray} {base j : Nat}
    (h : ∀ t, t < 256 → word m (base + 32 * t) = pack4 fun k => zLane cd (j + k) t)
    {k : Nat} (hk : k < 4) :
    lanesPoly m base k = (Array.range 256).map fun t => (zLane cd (j + k) t : Int) := by
  apply Array.ext (by simp only [lanesPoly, Array.size_map])
  intro i h1 _
  simp only [lanesPoly, Array.size_map, Array.size_range] at h1
  simp only [lanesPoly, Array.getElem_map, Array.getElem_range, h i h1,
    MlDsaOpt44.Proofs.lane_pack4 (fun j' _ => Nat.lt_trans (S2.zLane_lt cd _ i) (by norm_num)) hk]

theorem seg_ntt {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv2 cd m) (b : Bool)
    (hcd : HDR ≤ cd.size) :
    ∃ m', Inv3 cd m' ∧
      Reach (callState s 3100 [flag b] m) (callState s 3122 [flag b] m') Gas.pNtt := by
  have hb1 : Reach (callState s 3100 [flag b] m) (callState s Entry.ntt [wd ZH, wd 3110, flag b] m)
      17 := by
    opt87_reach [968, 969, 970, 971] with [ZH, Entry.ntt]
  obtain ⟨m1, hpost1, hfr1, hc1⟩ := ntt_call hs (p := ZH) (Or.inl rfl) (ret := 3110)
    (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  have hb2 : Reach (callState s 3110 [flag b] m1)
      (callState s Entry.ntt [wd ZH2, wd 3121, flag b] m1) 18 := by
    opt87_reach [972, 973, 974, 975, 976] with [ZH2, Entry.ntt]
  obtain ⟨m2, hpost2, hfr2, hc2⟩ := ntt_call hs (p := ZH2) (Or.inr rfl) (ret := 3121)
    (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (TblAt.frame hI.tbl hfr1 (by avoids_tac))
  have hb3 : Reach (callState s 3121 [flag b] m2) (callState s 3122 [flag b] m2) 1 := by
    opt87_reach [977]
  have hz0 : ∀ t, t < 256 → word m (ZH + 32 * t) = pack4 fun k => zLane cd (0 + k) t :=
    fun t ht => by simp only [Nat.zero_add]; exact (hI.z t ht).1
  have hz1 : ∀ t, t < 256 → word m1 (ZH2 + 32 * t) = pack4 fun k => zLane cd (4 + k) t :=
    fun t ht => by
      rw [word_frame hfr1 (lo := ZH2) (hi := ZH2 + 8192) (by avoids_tac) (by omega) (by omega)]
      exact (hI.z t ht).2
  have hp1 := hpost1 fun k hk t ht => by
    rw [hz0 t ht, MlDsaOpt44.Proofs.lane_pack4
      (fun j _ => Nat.lt_trans (S2.zLane_lt cd _ t) (by norm_num)) hk]
    exact S2.zLane_range cd _ t
  have hp2 := hpost2 fun k hk t ht => by
    rw [hz1 t ht, MlDsaOpt44.Proofs.lane_pack4
      (fun j _ => Nat.lt_trans (S2.zLane_lt cd _ t) (by norm_num)) hk]
    exact S2.zLane_range cd _ t
  refine ⟨m2, ⟨RC4Table.frame (RC4Table.frame hI.rc4 hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    RC1Table.frame (RC1Table.frame hI.rc1 hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    TblAt.frame (TblAt.frame hI.tbl hfr1 (by avoids_tac)) hfr2 (by avoids_tac), ?_,
    ZeroOn.frame (ZeroOn.frame hI.zMisc hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    ZeroOn.frame (ZeroOn.frame hI.zCw hfr1 (by avoids_tac)) hfr2 (by avoids_tac),
    ZeroOn.frame (ZeroOn.frame hI.zHigh hfr1 (by avoids_tac)) hfr2 (by avoids_tac)⟩,
    (((hb1.trans hc1).trans hb2).trans hc2).trans hb3 |>.mono (by unfold Gas.pNtt; omega)⟩
  intro k hk t ht
  unfold zhLane
  by_cases h4 : k < 4
  · rw [show zhAddr k t = ZH + 32 * t by unfold zhAddr; rw [Nat.div_eq_of_lt h4]; omega,
      Nat.mod_eq_of_lt h4,
      word_frame hfr2 (lo := ZH) (hi := ZH + 8192) (by avoids_tac) (by omega) (by omega)]
    refine ⟨(hp1 k h4 t ht).1, ?_⟩
    have := (hp1 k h4 t ht).2
    rwa [S2.lanesPoly_zLane hz0 h4, Nat.zero_add, ntt_zLane cd hcd hk] at this
  · rw [show zhAddr k t = ZH2 + 32 * t by unfold zhAddr ZH2 ZH; omega,
      show k % 4 = k - 4 by omega]
    refine ⟨(hp2 (k - 4) (by omega) t ht).1, ?_⟩
    have := (hp2 (k - 4) (by omega) t ht).2
    rwa [S2.lanesPoly_zLane hz1 (by omega), show 4 + (k - 4) = k by omega, ntt_zLane cd hcd hk]
      at this

end MlDsaOpt87.Proofs
