import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
import MlDsaOpt44.Fn.Ntt.Top
/-!
# Four-lane NTT and inverse NTT (WP7)

`scripts/opt_ntt.py`: layers merged 3 + 3 + 2 (forward) and 2 + 3 + 3
(inverse), eight words on the stack, lane-wise Montgomery multiplication with
`R = 2^32` by the zeta records at `TBL` (`TblAt`) or immediates. The inverse
also Montgomery-reduces its inputs at load (`premont`), and folds `256⁻¹` and
the Montgomery factor into its last layer.

The contracts are congruences with bounds (the exact lane values depend on
the Montgomery representatives): forward inputs `< 2^25` give outputs
`< 2^28` congruent to `Fips204.ntt`; inverse inputs `< 2^58` give outputs
`< 2^27` congruent to `Fips204.nttInv`. The bound argument is in the
`opt_ntt.py` docstring.

Proof (`Fn/Ntt/`): `Defs`/`Sem` (lane-wise Montgomery butterflies on words),
`Step` (butterflies against the index-wise layer models, pass invariants),
`FwdA`…`InvA` (generated block lemmas and loop bodies), `Ctl` (loop control),
`Passes` (the six loops), `Model` (`Fips204.ntt`/`nttInv` mod `q` are the layer
models), `Top` (composition).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **ntt**: `[ZH, ret]`, in place on the four lane polynomials of `ZH`. -/
theorem ntt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ZH + 32 * t)) k < 2 ^ 25) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (ZH + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (ZH + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m ZH k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.ntt [wd ZH] ret tail m [] m' Gas.ntt :=
  NttW.ntt_full hs hr m htbl

/-- **intt**: `[ACC, ret]`, in place on the four lane polynomials of `ACC`. -/
theorem intt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 58) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (ACC + 32 * t)) k < 2 ^ 27 ∧
          ((lane (word m' (ACC + 32 * t)) k : Int) - (Fips204.nttInv (lanesPoly m ACC k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.intt [wd ACC] ret tail m [] m' Gas.intt :=
  NttW.intt_full hs hr m htbl

end MlDsaOpt44.Proofs
