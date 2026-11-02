import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOptGlam65.Budget
import MlDsaOptGlam65.Layout
/- Ported from `MlDsaOpt65/Fn/Sponge/Spr.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Sponge/Spr.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
/-!
# `spr`: the spreading network on any input word
-/

namespace MlDsaOptGlam65.Proofs.WP4

open MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs.WP4
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

set_option maxRecDepth 100000 in
/-- `spr` on an arbitrary word (callers with non-lane inputs, `mu0`). -/
theorem spr_call_any {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) (v : Nat) :
    Call s Entry.spr [wd v] ret tail m [wd (sprNet v)] m Gas.spr := by
  have := hr.depth; simp only [Stack.spr, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  rw [call_iff, Entry.spr, Gas.spr]
  glam65_rreach [8212, 8213, 8214, 8215, 8216, 8217, 8218, 8219, 8220, 8221, 8222, 8223, 8224,
    8225, 8226, 8227, 8228, 8229, 8230, 8231, 8232, 8233, 8234, 8235, 8236, 8237, 8238, 8239,
    8240, 8241, 8242, 8243, 8244, 8245, 8246, 8247, 8248, 8249, 8250] with [hj]
  rfl

theorem spr_call_lane {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr := by
  have h := spr_call_any hs hr m v
  rwa [sprNet_eq hv] at h

end MlDsaOptGlam65.Proofs.WP4
