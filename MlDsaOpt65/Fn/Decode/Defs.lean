import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
set_option warningAsError true
/-!
# Definitions of the `dz` contract (ML-DSA-65)

`dz` is called twice (`MlDsaOpt/65/opt.asm`, segment zh, pcs 1002 and 1051): `[ZH, Z0]` decodes
`z_0 … z_3` and `[ZH2, Z0 + 4 · 640]` decodes "polynomials" 4 … 7 of the
20-bit stream: `z_4` and three phantom polynomials read from the hint bytes, the
message and zero padding past the end of the calldata (`CALLDATALOAD` reads zeros there,
as `rawZ` does through `ByteArray.extract` and `[·]!`). The caller masks the flag
word of the second call to lane 0 (`PUSH8 0xff…ff; AND`) before the norm check
`flag_check` (`f &&& zBits = 0`).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa

/-- The norm-flag bits checked by `flag_check` (`zbits + 32 = 52` and `25` of every lane). -/
def zBits : Nat := pack4 fun _ => 2 ^ 52 + 2 ^ 25

/-- The norm-flag bits of lane `j` (`zBits = Σ_j zFlagBit j`). -/
def zFlagBit (j : Nat) : Nat := (2 ^ 52 + 2 ^ 25) * 2 ^ (64 * j)

/-- Every 20-bit field of polynomial `k` of the z stream lies strictly between `β` and
`2γ1 − β`, i.e. `|γ1 − raw| < γ1 − β` (for `k < ℓ`: `‖z_k‖∞ < γ1 − β`). -/
def zNormOk (cd : ByteArray) (k : Nat) : Prop :=
  ∀ t, t < 256 → P.beta < rawZ cd k t ∧ rawZ cd k t < 2 * P.gamma1 - P.beta

end MlDsaOpt65.Proofs
