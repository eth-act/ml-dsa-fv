import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Ntt
set_option warningAsError true
/-! # Segment `3068 … 3078`: `ntt(ZH)`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem seg_ntt {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv2 cd m) (b : Bool)
    (hcd : HDR ≤ cd.size) :
    ∃ m', Inv3 cd m' ∧
      Reach (callState s 3068 [flag b] m) (callState s 3078 [flag b] m') Gas.pNtt := by
  have hblk : Reach (callState s 3068 [flag b] m) (callState s 16828 [wd ZH, wd 3078, flag b] m) 17 := by
    opt44_reach [964, 965, 966, 967] with [ZH]
  obtain ⟨m', hpost, hfr, hcall⟩ := ntt_call hs (ret := 3078) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hI.tbl
  refine ⟨m', ⟨hI.rc4.frame hfr (by avoids_tac), hI.rc1.frame hfr (by avoids_tac),
    hI.tbl.frame hfr (by avoids_tac), ?_, hI.hp.frame hfr (by avoids_tac),
    hI.zMisc.frame hfr (by avoids_tac), hI.zCw.frame hfr (by avoids_tac),
    hI.zHigh.frame hfr (by avoids_tac)⟩, hblk.trans hcall⟩
  have hlanes : ∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k = zLane cd k t :=
    fun k hk t ht => by
      rw [hI.z t ht, lane_pack4 (fun j _ => Nat.lt_trans (zLane_lt cd j t) (by norm_num)) hk]
  have hp := hpost fun k hk t ht => by rw [hlanes k hk t ht]; exact zLane_lt cd k t
  intro k hk t ht
  refine ⟨(hp k hk t ht).1, ?_⟩
  have hpoly : lanesPoly m ZH k = (Array.range 256).map fun t => (zLane cd k t : Int) := by
    apply Array.ext (by simp only [lanesPoly, Array.size_map])
    intro i h1 _
    simp only [lanesPoly, Array.size_map, Array.size_range] at h1
    simp only [lanesPoly, Array.getElem_map, Array.getElem_range, hlanes k hk i h1]
  have := (hp k hk t ht).2
  rwa [hpoly, ntt_zLane cd hcd hk] at this


end MlDsaOpt44.Proofs
