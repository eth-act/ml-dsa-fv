import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
set_option warningAsError true
/-!
# `sib`: SampleInBall representation (ML-DSA-65)

As `MlDsaOpt44/Fn/Ball/Defs.lean` with `τ = 49` and the ML-DSA-65 `BASES`/`IDX`
addresses (`CW`, `NNEG`, `CNT` are the shared constants). `sib` keeps, instead of the
coefficient array:

* `CW[t]`: a code word per position (`0`; `1` for `c_t = −1`; `2^256 − 1` for `c_t = +1`),
  read by `csum` as the running `n_neg` correction;
* `BASES[i]`, `i < τ`: the window base `4064 + 8 p − 2048 [c_p = −1]` of every nonzero
  position `p` (moved when SampleInBall moves a coefficient);
* `IDX` (one byte per position: slot + 1 in `BASES`), `NNEG`, `CNT`.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa

/-- `CW` code of a coefficient of `c`. -/
def codeOf (v : Int) : Nat := if v = 0 then 0 else if v = -1 then REP else 2 ^ 256 - REP

/-- Window base of a nonzero coefficient at `p`. -/
def baseOf (c : Fips204.Poly) (p : Nat) : Nat := 4064 + 8 * p - if c[p]! = -1 then 2048 else 0

/-- Number of `−1` coefficients. -/
def negCount (c : Fips204.Poly) : Nat := ((List.range 256).filter fun p => c[p]! = -1).length

/-- `c` as `sib` leaves it in memory. -/
def CRep (m : ByteArray) (c : Fips204.Poly) : Prop :=
  (∀ t, t < 256 → word m (CW + 32 * t) = codeOf c[t]!) ∧
  word m NNEG = negCount c ∧
  ∃ ps : List Nat, ps.length = P.tau ∧ ps.Nodup ∧
    (∀ p, p ∈ ps ↔ p < 256 ∧ c[p]! ≠ 0) ∧
    ∀ i, i < P.tau → word m (BASES + 32 * i) = baseOf c ps[i]!

/-- `sib`'s scratch regions start zeroed. -/
def SibFresh (m : ByteArray) : Prop :=
  ZeroOn m CW (CW + 8192) ∧ ZeroOn m IDX (IDX + 256) ∧ ZeroOn m NNEG (NNEG + 64)

end MlDsaOpt65.Proofs
