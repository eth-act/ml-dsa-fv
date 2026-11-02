import MlDsaOpt44.Fn.Sponge.Bits
import MlDsaOpt44.Budget
set_option warningAsError true
/-!
# `spr`: the spreading network on any input word
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

set_option maxRecDepth 100000 in
/-- `spr` on an arbitrary word (callers with non-lane inputs, `mu0`). -/
theorem spr_call_any {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) (v : Nat) :
    Call s Entry.spr [wd v] ret tail m [wd (sprNet v)] m Gas.spr := by
  have := hr.depth; simp only [Stack.spr, Stack.leaf] at this
  have hret := hr.small
  have hj := hr.jumpdest
  rw [call_iff, Entry.spr, Gas.spr]
  opt44_reach [5434, 5435, 5436, 5437, 5438, 5439, 5440, 5441, 5442, 5443, 5444, 5445, 5446,
    5447, 5448, 5449, 5450, 5451, 5452, 5453, 5454, 5455, 5456, 5457, 5458, 5459, 5460, 5461,
    5462, 5463, 5464, 5465, 5466, 5467, 5468, 5469, 5470, 5471, 5472] with [hj]
  rfl

theorem spr_call_lane {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr := by
  have h := spr_call_any hs hr m v
  rwa [sprNet_eq hv] at h

end MlDsaOpt44.Proofs.WP4
