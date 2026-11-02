import MlDsaOptGlam65.Layout
set_option warningAsError true
/-!
# The words stored by 65's interleaved fused passes (`PACK65` schedule)

`pass3f7` stores row group 0 into `ACC`, `pass3f8` row group 1 into
`ACC + 8192`. Each is the exact word the code computes; the Kronecker terms are
the masked lanes of a full-word product.
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOptCommon
open MlDsaOpt44.Proofs (ZH CW ABUF M64 lane)

/-- The word `pass3f7` stores at `ACC[t]`. -/
def p3f7Word (m : ByteArray) (t : Nat) : Nat :=
  let z0 := word m (ZH + 32 * t)
  let z1 := word m (ZH + 8192 + 32 * t)
  (word m (CW + 32 * t) * lane z0 0 + word m (HP + 32 * t) * lane z0 1 +
    word m (HP + 8192 + 32 * t) * lane z0 2 + word m (ACC + 32 * t) / 2 ^ 64 * lane z0 3 +
    word m (SB + 8192 + 32 * t) / 2 ^ 64 * lane z1 0 +
    ((word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (z1 * 2 ^ 64 % 2 ^ 256 ||| z0 / 2 ^ 192) % 2 ^ 256 &&&
      (M64 * 2 ^ 192))) % 2 ^ 256

/-- The word `pass3f8` stores at `(ACC + 8192)[t]`. -/
def p3f8Word (m : ByteArray) (t : Nat) : Nat :=
  let z0 := word m (ZH + 32 * t)
  let z1 := word m (ZH + 8192 + 32 * t)
  (word m (ACC + 8192 + 32 * t) * z0 % 2 ^ 256 / 2 ^ 192 +
    (word m (SB + 32 * t) * z0 % 2 ^ 256 &&& (M64 * 2 ^ 192)) / 2 ^ 128 +
    (word m (ABUF + 32 * t) &&& (2 ^ 128 - 1)) * lane z1 0) % 2 ^ 256

end MlDsaOptGlam65.Proofs
