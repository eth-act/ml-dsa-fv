import MlDsaOpt65.Main.Exp.G8Short
import MlDsaOpt65.Main.Exp.G8Long
import MlDsaOpt65.Main.Exp.G8Acc
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# ExpandA group 8 and `pass3f8` (ML-DSA-65, v4; pc 5022 → 5242)

`HAVE6 := 0`, `ginit [0, 1, 2, L4]`, `mub0 [2]`, then (`G8Path.lean`) the short
μ path (`|M| ≤ 69`, `g8_short`) or the out-of-line mulong region at 7066
(`g8_long`), both ending at `gfix [1]` (return 5233), `AND`, `pass3f8`
(row group 1 of `Â ẑ` into `ACC + 0x2000`, `G8Acc.lean`).

`gG8` is the longer (mulong) path: 432185 gas; the short path costs 418315.
-/

namespace MlDsaOpt65.Proofs.Exp

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Ex
open MlDsaOpt65.Proofs.Infra

/-- Group 8 plus `pass3f8`, the mulong path (the longer one). -/
def gG8 : Nat :=
  33 + Gas.ginit + 21 + Gas.mub0 + 4 * (15 + Gas.kf4 + 21 + Gas.blk) + (15 + Gas.kf4 + 21 + Gas.blkh) +
    2 * (24 + Gas.cext 17) + 5 * (21 + Gas.mub) + 18 + Gas.gfix 1 + 18 + Gas.pass3f8

theorem gG8_eq : gG8 = 432185 := by
  simp only [gG8, Gas.ginit, Gas.mub0, Gas.kf4, Gas.blk, Gas.blkh, Gas.cext, Gas.mub, Gas.gfix, Gas.gfix0,
    Gas.blkt, Gas.fixNo, Gas.fixSq, Gas.pass3f8]

/-- The short μ path costs 13870 less. -/
theorem gShort_eq : 33 + Gas.ginit + 21 + Gas.mub0 + cShort + Gas.gfix 1 + 18 + Gas.pass3f8 = 418315 := by
  simp only [cShort, Gas.ginit, Gas.mub0, Gas.kf4, Gas.blk, Gas.blkh, Gas.cext, Gas.gfix, Gas.gfix0,
    Gas.blkt, Gas.fixNo, Gas.fixSq, Gas.pass3f8]

theorem cShort_le : cShort ≤ cLong := by
  simp only [cShort, cLong, Gas.kf4, Gas.blk, Gas.blkh, Gas.cext, Gas.mub]; omega

theorem gG8_long : gG8 = 33 + Gas.ginit + 21 + Gas.mub0 + cLong + Gas.gfix 1 + 18 + Gas.pass3f8 := by
  unfold gG8 cLong
  generalize Gas.kf4 = a1; generalize Gas.blk = a2; generalize Gas.blkh = a3
  generalize Gas.cext 17 = a4; generalize Gas.mub = a5
  omega

theorem gfix1_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(1 : Nat).testBit sl || (aI (I8 cd sl)).isSome) = okI cd 9 := by
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (1 : Nat).testBit 0 = true by decide, show (1 : Nat).testBit 1 = false by decide,
    show (1 : Nat).testBit 2 = false by decide, show (1 : Nat).testBit 3 = false by decide,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true]
  rw [show I8 cd 0 = seedState 168 (aSeed cd 5 4) from rfl, GroupP.aI_aSeed hcd]
  simp only [okI, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv]

set_option maxHeartbeats 1000000 in
theorem exp_g8 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG8 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 5022 [flag b] m)
        (callState s 5242 [flag (b && okI s.executionEnv.calldata 9)] m') gG8 := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  obtain ⟨m2, hks2, h62, hf2, hR2⟩ := g8_head hs hcdN hI.rho hI.trl b
  have hrc2 := RC4Table.frame hI.rc4 hf2 (by g57_frame)
  have hmid : ∃ m10, G8Mid s.executionEnv.calldata m2 m10 ∧
      Reach (callState s 5022 [flag b] m) (callState s 11577 [wd 1, wd 5233, flag b] m10)
        (33 + Gas.ginit + 21 + Gas.mub0 + cLong) := by
    by_cases hmN : mlenOf s.executionEnv.calldata ≤ 69
    · rw [if_pos hmN] at hR2
      obtain ⟨m10, hM, hR⟩ := g8_short hs hcdN hmN hrc2 hks2 h62 (b := b)
      exact ⟨m10, hM, (hR2.trans hR).mono (by have := cShort_le; omega)⟩
    · rw [if_neg hmN] at hR2
      obtain ⟨m10, hM, hR⟩ := g8_long hs hcdN hmN hrc2 hks2 h62 (b := b)
      exact ⟨m10, hM, hR2.trans hR⟩
  obtain ⟨m10, hM, hR10⟩ := hmid
  -- gfix [1]
  obtain ⟨m11, hlanes, hks11, -, hf11, hc11⟩ := gfix_call hs (ret := 5233) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m10 hM.rc
    (amask := 1) (by norm_num) 1 (by decide) (St s.executionEnv.calldata 4) (St_sized _ 4) hM.ks
    (I8 s.executionEnv.calldata) hM.h6
    (fun sl hsl hbit => by
      obtain rfl : sl = 0 := by
        interval_cases sl
        · rfl
        all_goals exact absurd hbit (by decide)
      exact ⟨hM.hb.slotHead (by norm_num) fun b' _ => St_ne2 _ b' (by decide), St_ne2 _ 4 (by decide)⟩)
  rw [gfix1_flag hcd32] at hc11
  -- AND, pass3f8
  have gP : Reach (callState s 5233 [flag (okI s.executionEnv.calldata 9), flag b] m11)
      (callState s 11211 [wd 5242, flag (b && okI s.executionEnv.calldata 9)] m11) 18 := by
    opt65_reach [1726, 1727, 1728, 1729, 1730] with [flag, ite01_land]
  obtain ⟨m12, hw12, hf12, hc12⟩ := pass3f8_call hs (ret := 5242)
    (tail := [flag (b && okI s.executionEnv.calldata 9)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m11
  -- frames
  have hfA := ((hf2.trans hM.fr).trans hf11).trans hf12
  have hf11' := (hf2.trans hM.fr).trans hf11
  have hz11 : ZHatAt m11 s.executionEnv.calldata := G57.zhat_frame hI.zhat hf11' (by g57_frame)
  have hzh : ∀ k, k < 5 → ∀ t, t < 256 → zhLane m12 k t = zhLane m11 k t := fun k hk t ht => by
    unfold zhLane zhAddr
    rw [word_frame hf12 (lo := ZH) (hi := ZH + 16384) (by g57_frame) (by omega)
      (by interval_cases k <;> simp [ZH] <;> omega)]
  have hacc : AccAt m12 s.executionEnv.calldata := fun hok =>
    s3_accAt (G57.zhat_frame hI.zhat hfA (by g57_frame)) (G57.acc0_frame hI.acc0 hfA (by g57_frame)
      (by g57_frame))
      (accCols1_p3f8 hok hz11 (hI.b5.frame hf11' (by g57_frame)) (hI.b6.frame hf11' (by g57_frame))
        (hI.b7.frame hf11' (by g57_frame))
        (fun t ht => by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (s3_okA_get hok (r := 5) (s := 4) (by norm_num)
            (by norm_num))
          rw [hlanes 0 (by norm_num) (by decide) a
            (by rw [show I8 s.executionEnv.calldata 0 = seedState 168 (aSeed s.executionEnv.calldata 5 4)
              from rfl, GroupP.aI_aSeed hcd32]; exact ha) t ht]
          unfold aD; rw [ha]; rfl)
        hw12 hzh) hok
  refine ⟨m12, ⟨RC1Table.frame hI.rc1 hfA (by g57_frame), TblAt.frame hI.tbl hfA (by g57_frame), hacc,
    ?_, ?_, ?_, ZeroOn.frame hI.zBases hfA (by g57_frame), ZeroOn.frame hI.zIdx hfA (by g57_frame),
    ZeroOn.frame hI.zNeg hfA (by g57_frame)⟩, ?_⟩
  · intro hm x hx
    rw [word_frame (hf11.trans hf12) (a := MU + 32 * x) (lo := MU) (hi := MU + 256) (by g57_frame) (by omega)
      (by omega)]
    exact hM.mu hm x hx
  · intro h613
    refine ⟨St s.executionEnv.calldata 4, St_sized _ 4, KS4.frame hks11 hf12 (by g57_frame), ?_⟩
    rw [St_two, muT_absorb _ (by unfold muN; omega) (by norm_num)]
  · intro x hx
    rw [word_frame (hf11.trans hf12) (a := CB + 32 * x) (lo := CB) (hi := CB + 1088) (by g57_frame) (by omega)
      (by omega)]
    exact hM.cb x hx
  · have hR := ((hR10.trans hc11).trans gP).trans hc12
    exact hR.mono (le_of_eq gG8_long.symm)

end MlDsaOpt65.Proofs.Exp
