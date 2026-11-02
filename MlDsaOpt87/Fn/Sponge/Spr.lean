import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt87.Budget
import MlDsaOpt87.Layout
/- Ported from `MlDsaOpt44/Fn/Sponge/Spr.lean` by `scripts/proofgen_port.py 87`; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
/-!
# `spr`: the spreading network on any input word
-/

namespace MlDsaOpt87.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt87.Proofs.Infra

set_option maxRecDepth 100000 in
/-- `spr` on an arbitrary word (callers with non-lane inputs, `mu0`). -/
theorem spr_call_any {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) (v : Nat) :
    Call s Entry.spr [wd v] ret tail m [wd (sprNet v)] m Gas.spr := by
  have := hr.depth; simp only [Stack.spr, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  rw [call_iff, Entry.spr, Gas.spr]
  opt87_reach [6370, 6371, 6372, 6373, 6374, 6375, 6376, 6377, 6378, 6379, 6380, 6381, 6382,
    6383, 6384, 6385, 6386, 6387, 6388, 6389, 6390, 6391, 6392, 6393, 6394, 6395, 6396, 6397,
    6398, 6399, 6400, 6401, 6402, 6403, 6404, 6405, 6406, 6407, 6408] with [hj]
  rfl

theorem spr_call_lane {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr := by
  have h := spr_call_any hs hr m v
  rwa [sprNet_eq hv] at h

end MlDsaOpt87.Proofs.WP4
