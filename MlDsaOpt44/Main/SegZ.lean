import MlDsaOpt44.Main.Base
import MlDsaOpt44.Fn.Decode
set_option warningAsError true
/-! # Segment `992 … 1076`: `dz`, the norm-flag check. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

theorem zflag_eq (f : Nat) (hf : f < 2 ^ 256) :
    (7067389101611870667173807517204293913874466279225986744253852419608281088 &&&
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 &&& f ||| 0)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
    f &&& zBits := by
  have hz : zBits = 7067389101611870667173807517204293913874466279225986744253852419608281088 := by
    decide
  have hall : (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat) =
      2 ^ 256 - 1 := by norm_num
  have hmod : (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) =
      2 ^ 256 := by norm_num
  rw [hall, hmod, Nat.and_comm (2 ^ 256 - 1) f, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hf,
    Nat.or_zero, Nat.and_comm, hz]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hf)

theorem zflag_block {s : State} (hs : Ctx s) {m : ByteArray} {f : Nat} (hf : f < 2 ^ 256) :
    Reach (callState s 1006 [wd f, wd 0] m)
      (callState s 1076 [wd (if f &&& zBits = 0 then 1 else 0)] m) 19 := by
  opt44_reach [208, 209, 210, 211, 212, 213, 214]
  simp only [zflag_eq f hf]

theorem seg_z {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv0 m) :
    ∃ m', Inv1 s.executionEnv.calldata m' ∧
      Reach (callState s 992 [] m) (callState s 1076 [flag (okZ s.executionEnv.calldata)] m')
        Gas.pZ := by
  have hb1 : Reach (callState s 992 [] m) (callState s 8219 [wd ZH, wd Z0, wd 1006, wd 0] m) 22 := by
    opt44_reach [202, 203, 204, 205, 206, 207] with [ZH, Z0]
  obtain ⟨m1, f, hf, hfz, hz, hfr1, hc1⟩ := dz_call hs (ret := 1006) (tail := [wd 0])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m hcd
  have hb2 := zflag_block hs (m := m1) hf
  have hzf : (if f &&& zBits = 0 then 1 else 0) = if okZ s.executionEnv.calldata = true then 1 else 0 := by
    by_cases h : f &&& zBits = 0
    · rw [if_pos h, if_pos (hfz.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hfz.mpr h'))]
  rw [hzf] at hb2
  refine ⟨m1, ⟨hI.rc4.frame hfr1 (by avoids_tac), hI.rc1.frame hfr1 (by avoids_tac),
    fun t ht => hz t ht,
    (hI.zero.mono (by unfold MISC; omega) (by unfold ZH TOP; omega)).frame hfr1 (by avoids_tac),
    (hI.zero.mono (by unfold MISC BASES; omega) (by unfold FIN TOP; omega)).frame hfr1 (by avoids_tac)⟩,
    ((hb1.trans hc1).trans hb2).mono (by unfold Gas.pZ; omega)⟩

end MlDsaOpt44.Proofs
