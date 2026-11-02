import MlDsaOptGlam87.Fn.TBuild.Run
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Fn/TBuild.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# `tbuild`: the `c · t1` window table (65/87 generalisation of `MlDsaOpt44/Fn/Ct.lean`)

`tbuild [tp, off, ret]` writes the window table of the four `t1` rows packed at calldata
offset `off`: 768 16-bit fields per row, interleaved by row (field `(e, r)` big-endian at byte
`tp + 6142 − 8e − 2r`): `e < 256` and `e ≥ 512` hold `1023 − t1_r[e mod 256]`,
`256 ≤ e < 512` hold `t1_r[e − 256]` (`TTable`, `Fn/TBuild/Defs.lean`). Call sites:
`(0x5000, 32)` (rows 0–3) and `(0x6800, 0x520)` (rows 4–7, `t1f_520`).
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **tbuild**: `[tp, off, ret]`; table at `[tp, tp + 6144)`, rows read from calldata
`[off, off + 1280)`. -/
theorem tbuild_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.tbuild ret tail) (m : ByteArray) {tp off : Nat} (htp : tp + 6144 ≤ 65536)
    (hcd : off + 1280 ≤ s.executionEnv.calldata.size) :
    ∃ m', TTable m' tp off s.executionEnv.calldata ∧
      FrameExcept m m' [(tp, tp + 6144)] ∧
      Call s Entry.tbuild [wd tp, wd off] ret tail m [] m' Gas.tbuild :=
  TB.tbuild_main hs hr m htp hcd

end MlDsaOptGlam87.Proofs
