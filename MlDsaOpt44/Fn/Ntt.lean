import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
/-!
# Four-lane NTT and inverse NTT (WP7)

`scripts/opt_ntt.py`: layers merged 3 + 3 + 2 (forward) and 2 + 3 + 3
(inverse), eight words on the stack, lane-wise Montgomery multiplication with
`R = 2^32` by the zeta records at `TBL` (`TblAt`) or immediates.

v4: the forward NTT's inputs carry a bias of `8q` (`zLane`), so lanes stay
non-negative with `b' = a − u` (no `+2q` per butterfly); pass A multiplies by
its immediate zetas with Shoup's method. Inputs in `[zLo, zHi]` give outputs
`< 2^28` congruent to `Fips204.ntt` (interval argument: `opt_selftest.py`).
The inverse NTT Montgomery-reduces its inputs at load (`premont`), uses GS
butterflies without swap (`b' = mont(((C − a) + b) ζ)`), folds `256⁻¹` and the
Montgomery factor into its last layer, and applies UseHint to each output
word before storing it (`gen_opt.py` `uh_word`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **ntt**: `[ZH, ret]`, in place on the four lane polynomials of `ZH`. -/
theorem ntt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ntt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → zLo ≤ lane (word m (ZH + 32 * t)) k ∧
          lane (word m (ZH + 32 * t)) k ≤ zHi) →
        ∀ k, k < 4 → ∀ t, t < 256 → lane (word m' (ZH + 32 * t)) k < 2 ^ 28 ∧
          ((lane (word m' (ZH + 32 * t)) k : Int) - (Fips204.ntt (lanesPoly m ZH k))[t]!) %
            (Fips204.q : Int) = 0) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.ntt [wd ZH] ret tail m [] m' Gas.ntt :=
  sorry

/-- **intt**: `[ACC, ret]`, in place on the four lane polynomials of `ACC`,
with UseHint fused into the last pass: lane `r` of `ACC[t]` becomes
`UseHint(HP, NTT⁻¹(ACC) + SP − spOff)`. -/
theorem intt_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.intt ret tail) (m : ByteArray) (htbl : TblAt m) :
    ∃ m', ((∀ k, k < 4 → ∀ t, t < 256 → lane (word m (ACC + 32 * t)) k < 2 ^ 57) →
        (∀ t, t < 256 → ∀ r, r < 4 → lane (word m (SP + 32 * t)) r ≤ spOff ∧
          lane (word m (HP + 32 * t)) r ≤ 1) →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 32 * t)) r =
          (Fips204.useHint (lane (word m (HP + 32 * t)) r)
            ((Fips204.nttInv (lanesPoly m ACC r))[t]! + lane (word m (SP + 32 * t)) r - spOff)).toNat) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.intt [wd ACC] ret tail m [] m' Gas.intt :=
  sorry

end MlDsaOpt44.Proofs
