import MlDsaOpt65.Fn.Group.Defs
import MlDsaOptGlam65.Fn.Ginit.Lanes
import MlDsaOptGlam65.Budget
import MlDsaOptGlam65.Layout
/- Ported from `MlDsaOpt65/Fn/Ginit/Call.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# `ginit`: initialise the kf4 state of a SIMD group (ML-DSA-65)

Entry `[l4, cmult, amult, keep, ret]` (`gen_ginit`). ML-DSA-65's `ginit`
differs from ML-DSA-44's: `RHO1` moved, the c̃ slot absorbs six c̃ lanes
(48 bytes) with its domain byte in lane 6. The stored words are `ginitWord`
(`Fn/Group/Defs.lean`). Straight line, 25 lane blocks (`Fn/Ginit/Lanes.lean`),
exactly `Gas.ginit`.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option linter.unusedVariables false in
/-- **ginit**: `[l4, cmult, amult, keep, ret]`; `KS[x] := ginitWord m keep
amult cmult l4 x` for every lane `x < 25`, nothing else written, no results,
gas `Gas.ginit`. Covers every call site: `group` (`keep = 0`, `amult = 15`,
`cmult = 0`) and the mixed groups of the main flow (`keep`, `amult`,
`cmult = 2^cslot` or `0`). Proof: `G1.ginit_reach` (`Fn/Ginit/Lanes.lean`, one block
lemma per lane, generated from the ML-DSA-65 listing, pcs 17659–12083). -/
theorem ginit_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit :=
  G1.ginit_reach hs hr m hk hl

end MlDsaOptGlam65.Proofs
