import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Fn.Hint.PackMain
/- Ported from `MlDsaOpt44/Fn/Hint.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# `pack` (WP10)

`pack [4, FIN + 256, ACC, ret]`: `w1Encode` (6 bits per coefficient) of the
four rows, each 64-bit stream lane replicated (`rep`) into `FIN` for `kf1`.
(v4: UseHint is fused into the inverse NTT, `Fn/Ntt.lean`.)
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **pack**: `[4, FIN + 256, ACC, ret]`. -/
theorem pack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 64) →
        ∀ r, r < 4 → ∀ j, j < 24 → word m' (FIN + 256 + 32 * (24 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m ACC r) 43) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256, FIN + 256 + 3072)] ∧
      Call s Entry.pack [wd 4, wd (FIN + 256), wd ACC] ret tail m [] m' Gas.pack :=
  PK.pack_main hs hr m

end MlDsaOptGlam44.Proofs
