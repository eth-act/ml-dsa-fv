import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt65.Budget
import MlDsaOpt65.Layout
/- Ported from `MlDsaOpt44/Fn/Sponge/Spr.lean` by `scripts/proofgen_port.py 65`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
/-!
# `spr`: the spreading network on any input word
-/

namespace MlDsaOpt65.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt65.Proofs.Infra

set_option maxRecDepth 100000 in
/-- `spr` on an arbitrary word (callers with non-lane inputs, `mu0`). -/
theorem spr_call_any {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) (v : Nat) :
    Call s Entry.spr [wd v] ret tail m [wd (sprNet v)] m Gas.spr := by
  have := hr.depth; simp only [Stack.spr, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  rw [call_iff, Entry.spr, Gas.spr]
  opt65_reach [5538, 5539, 5540, 5541, 5542, 5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550,
    5551, 5552, 5553, 5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561, 5562, 5563, 5564, 5565,
    5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575, 5576] with [hj]
  rfl

theorem spr_call_lane {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr := by
  have h := spr_call_any hs hr m v
  rwa [sprNet_eq hv] at h

end MlDsaOpt65.Proofs.WP4
