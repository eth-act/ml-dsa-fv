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
  opt87_reach [6158, 6159, 6160, 6161, 6162, 6163, 6164, 6165, 6166, 6167, 6168, 6169, 6170,
    6171, 6172, 6173, 6174, 6175, 6176, 6177, 6178, 6179, 6180, 6181, 6182, 6183, 6184, 6185,
    6186, 6187, 6188, 6189, 6190, 6191, 6192, 6193, 6194, 6195, 6196] with [hj]
  rfl

theorem spr_call_lane {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr := by
  have h := spr_call_any hs hr m v
  rwa [sprNet_eq hv] at h

end MlDsaOpt87.Proofs.WP4
