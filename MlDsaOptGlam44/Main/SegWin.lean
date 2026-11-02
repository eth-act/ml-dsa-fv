import MlDsaOptGlam44.Main.Base
import MlDsaOptGlam44.Fn.Group
import MlDsaOptGlam44.Main.Win.PartB
import MlDsaOptGlam44.Main.Win.PartC
import MlDsaOptGlam44.Main.Win.PartE
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Main/SegWin.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-! # Segment `3875 … 3948`: the packed window and the fused accumulation

Eight `kf4` calls (`emit_window44`): slot 0 runs `tr`'s blocks 5 … 9 (calls
15 … 19), then `c̃` (20), then `A[1][3]` (21, 22); slot 1 runs `A[0][3]`
(15 … 19), μ's block 0 (20), `A[2][3]` (21, 22); slots 2, 3 run `A[1][3]`,
`A[2][3]` (15 … 17) and `A[3][3]`, `A[3][2]` (18 … 22). `A[1][3]`, `A[2][3]`
pause after call 17 (image `SAVE0`) and resume in slots 0, 1; the staged
column-3 candidates are merged (`lmerge`) in `ACC` / `BASES`. Then the two
fix-ups (`E = (A[3][3], A[3][2])`, copied to `SB + 8192`; `B3 = A[0 … 2][3]`)
and `pass3f4`. The parts are in `Main/Win/Part{A … E}` (`A` in
`Main/Win/States.lean`). -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

/-- The flags ANDed by the groups and the window give `okZ ∧ okA`. -/
def winFlag (cd : ByteArray) : Bool :=
  ((okZ cd && okCol cd 0) && okCol cd 1) && okCol3 cd 2

theorem winFlag_and (cd : ByteArray) :
    ((winFlag cd && Ex.okE cd) && okCol3 cd 3) = (okZ cd && okA cd) := by
  simp only [winFlag, Ex.okE, okCol, okCol3, okA, show List.range 4 = [0, 1, 2, 3] from rfl,
    show List.range 3 = [0, 1, 2] from rfl, List.all_cons, List.all_nil, Bool.and_true]
  generalize okZ cd = z
  generalize (aOf cd 0 0).isSome = a00
  generalize (aOf cd 0 1).isSome = a01
  generalize (aOf cd 0 2).isSome = a02
  generalize (aOf cd 0 3).isSome = a03
  generalize (aOf cd 1 0).isSome = a10
  generalize (aOf cd 1 1).isSome = a11
  generalize (aOf cd 1 2).isSome = a12
  generalize (aOf cd 1 3).isSome = a13
  generalize (aOf cd 2 0).isSome = a20
  generalize (aOf cd 2 1).isSome = a21
  generalize (aOf cd 2 2).isSome = a22
  generalize (aOf cd 2 3).isSome = a23
  generalize (aOf cd 3 0).isSome = a30
  generalize (aOf cd 3 1).isSome = a31
  generalize (aOf cd 3 2).isSome = a32
  generalize (aOf cd 3 3).isSome = a33
  simp only [Bool.and_comm, Bool.and_left_comm]

open Ex in
theorem seg_win {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG2 s.executionEnv.calldata m) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 2850 [flag (winFlag s.executionEnv.calldata)] m)
        (callState s 3948 [flag (okZ s.executionEnv.calldata && okA s.executionEnv.calldata)] m')
        Gas.pWin := by
  obtain ⟨S, -, hks, hS0⟩ := hI.tr
  obtain ⟨mA, hksA, hstA, hsv0A, hrcA, hfA, hRA⟩ := winA hs hcd (w := winFlag s.executionEnv.calldata)
    hI.rc4 hI.rho hks hS0
  obtain ⟨mB, hksB, hBB, htrlB, hsv1B, hrcB, hfB, hRB⟩ := winB hs hcd (w := winFlag s.executionEnv.calldata)
    hrcA (hI.rho.frame hfA (by avoids_tac)) hksA
  have hfAB := FrameExcept.trans hfA hfB
  obtain ⟨mC, hksC, hBC, hcbC, hmuC, hscC, -, hrcC, hfC, hRC⟩ := winC hs hcd
    (w := winFlag s.executionEnv.calldata) hrcB (hI.rho.frame hfAB (by avoids_tac)) hksB hBB htrlB
  obtain ⟨mD, hksD, hBD, hmgD, hrcD, hfD, hRD⟩ := winD hs (w := winFlag s.executionEnv.calldata) hrcC hksC
    ((hsv0A.frame hfB (by avoids_tac)).frame hfC (by avoids_tac)) hBC
  have hfBCD := FrameExcept.trans (FrameExcept.trans hfB hfC) hfD
  have hfAll := FrameExcept.trans hfA hfBCD
  obtain ⟨mE, haccE, hfE, hRE⟩ := winE hs hcd (w := winFlag s.executionEnv.calldata) hrcD hksD hBD hmgD
    (hstA.frame hfBCD (by avoids_tac) (by avoids_tac))
    ((hsv1B.frame hfC (by avoids_tac)).frame hfD (by avoids_tac))
    (fun k hk t ht => by
      rw [word_frame hfAll (lo := ZH) (hi := ZH + 8192) (by avoids_tac) (by omega) (by omega)]
      exact hI.zhat k hk t ht)
    (hI.c0.frame hfAll (by avoids_tac)) (hI.c1.frame hfAll (by avoids_tac))
    (fun hok t ht r hr => by
      rw [word_frame hfAll (lo := SB) (hi := SB + 8192) (by avoids_tac) (by omega) (by omega)]
      exact hI.c2 hok t ht r hr)
  have hfDE := FrameExcept.trans hfD hfE
  have hfX := FrameExcept.trans hfAll hfE
  refine ⟨mE, ⟨hI.rc4.frame hfX (by avoids_tac), hI.rc1.frame hfX (by avoids_tac),
    hI.tbl.frame hfX (by avoids_tac), haccE, fun hshort x hx => ?_, fun x hx => ?_,
    hscC.frame hfDE (by avoids_tac), hI.zIdx.frame hfX (by avoids_tac), hI.zNeg.frame hfX (by avoids_tac),
    by rw [word_frame hfX (lo := FLAG) (hi := FLAG + 32) (by unfold FLAG; avoids_tac) le_rfl le_rfl]
       exact hI.flag⟩, ?_⟩
  · rw [word_frame hfDE (lo := MU) (hi := MU + 256) (by avoids_tac) (by omega) (by omega)]
    exact hmuC hshort x hx
  · rw [word_frame hfDE (lo := CB) (hi := CB + 544) (by avoids_tac) (by omega) (by omega)]
    exact hcbC x hx
  · have hR := (((hRA.trans hRB).trans hRC).trans hRD).trans hRE
    rw [winFlag_and] at hR
    refine hR.mono (le_of_eq ?_)
    unfold Gas.pWin
    generalize Gas.ginit = a; generalize Gas.trabs 5 = b; generalize Gas.trabs 3 = c
    generalize Gas.kf4 = d; generalize Gas.blk = e; generalize Gas.blkh = f; generalize Gas.mub0 = g
    generalize Gas.cext 8 = h; generalize Gas.cext 17 = i; generalize Gas.kmove = j
    generalize Gas.lmerge 8 = k; generalize Gas.lmerge 1 = l; generalize Gas.gfix 2 = n
    generalize Gas.gfix 3 = o; generalize Gas.pass3f4 = p
    omega

end MlDsaOptGlam44.Proofs
