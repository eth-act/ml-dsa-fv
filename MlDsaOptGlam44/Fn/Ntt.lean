import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Fn.Ntt.Passes
/-!
# Four-lane NTT and inverse NTT (Glamsterdam: 4 + 4 layers)

`scripts/opt_ntt_glam.py` (`Kernel4x4`): layers merged 4 + 4, sixteen words on
the stack (`DUPN` / `SWAPN`), lane-wise Montgomery multiplication with
`R = 2^32` by the zeta records at `TBL` (`TblAt`, `nttRecG`: each block's 15
zetas loaded once onto the stack) or immediates; the contracts are v4's.

v4: the forward NTT's inputs carry a bias of `8q` (`zLane`), so lanes stay
non-negative with `b' = a − u` (no `+2q` per butterfly); pass A multiplies by
its immediate zetas with Shoup's method. Inputs in `[zLo, zHi]` give outputs
`< 2^28` congruent to `Fips204.ntt` (interval argument: `opt_selftest.py`).
The inverse NTT Montgomery-reduces its inputs at load (`premont`), uses GS
butterflies without swap (`b' = mont(((C − a) + b) ζ)`), folds `256⁻¹` and the
Montgomery factor into its last layer, and applies UseHint to each output
word before storing it (`gen_opt.py` `uh_word`).

Proofs: `Fn/Ntt/` (generated blocks and loop bodies: `Fn/Ntt/gen_nttg.py`;
`Passes.lean`), on v4's lane semantics and per-layer lemmas
(`MlDsaOpt44/Fn/Ntt/V4/{Defs,Sem,Step}.lean`; the numeric bounds of
`opt_selftest.py` / `opt_selftest_glam.py`: `MlDsaOpt44/Math/NttV4.lean`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

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
  NttG.ntt_g hs hr m htbl

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
  NttG.intt_g hs hr m htbl


end MlDsaOptGlam44.Proofs
