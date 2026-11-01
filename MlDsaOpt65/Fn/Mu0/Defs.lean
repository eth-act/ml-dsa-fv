import MlDsaOpt65.Layout
set_option warningAsError true
/-!
# `muBlock` (ML-DSA-65): μ's single padded block, with this artifact's `msgOf`
-/

namespace MlDsaOpt65.Proofs

open MlDsa

/-- μ's single padded SHAKE256 block for `|M| ≤ 69`: `tr ‖ 0 ‖ 0 ‖ M ‖ pad`. -/
def muBlock (tr : ByteArray) (cd : ByteArray) : ByteArray :=
  MlDsa44.Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))

end MlDsaOpt65.Proofs
