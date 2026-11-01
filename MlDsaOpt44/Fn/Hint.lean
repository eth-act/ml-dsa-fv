import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
import MlDsaOpt44.Fn.Hint.UseHintRun
import MlDsaOpt44.Fn.Hint.PackMain
/-!
# `usehint`, `pack` (WP10)

* `usehint [ACC, ret]`: for the 256 row-packed words `W` at `ACC`, lane-wise
  `W := UseHint(HP, (W − SP) mod q)`, with `x mod q` and the `2γ2` quotient by
  exact multiply-shift (`K = 53` resp. `(39, 2886403)`), and the `mod 44` by
  `(v · 94) >> 12`.
* `pack [4, FIN + 256, ACC, ret]`: `w1Encode` (6 bits per coefficient) of the
  four rows, each 64-bit stream lane replicated (`rep`) into `FIN` for `kf1`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **usehint**: `[ACC, ret]`. Exact on words whose lanes are in range. -/
theorem usehint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 2 ^ 27 ∧ lane (word m (SP + 32 * t)) r < 2 ^ 29 ∧
          lane (word m (HP + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m' (ACC + 32 * t)) r =
          (Fips204.useHint (lane (word m (HP + 32 * t)) r)
            ((lane (word m (ACC + 32 * t)) r : Int) - lane (word m (SP + 32 * t)) r)).toNat) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.usehint [wd ACC] ret tail m [] m' Gas.usehint :=
  UH.usehint_main hs hr m

/-- **pack**: `[4, FIN + 256, ACC, ret]`. -/
theorem pack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 32 * t)) r < 64) →
        ∀ r, r < 4 → ∀ j, j < 24 → word m' (FIN + 256 + 32 * (24 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m ACC r) 43) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256, FIN + 256 + 3072)] ∧
      Call s Entry.pack [wd 4, wd (FIN + 256), wd ACC] ret tail m [] m' Gas.pack :=
  PK.pack_main hs hr m

end MlDsaOpt44.Proofs
