import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
set_option warningAsError true
/-!
Definitions of the `c · t1` window table that `tbuild` writes (65/87 generalisation of
`MlDsaOpt44/Fn/Ct/Defs.lean`): the four `t1` rows are read from calldata offset `off`
(`32` for rows 0–3, `0x520 = 32 + 4 · 320` for rows 4–7).
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa

/-- The 10-bit field `i` of the `t1` row `r` of the four rows packed at calldata offset `off`
(`t1f cd 32 r = t1v cd r`, `t1f cd 0x520 r = t1v cd (4 + r)`). -/
def t1f (cd : ByteArray) (off r i : Nat) : Nat :=
  Fips204.bitsToInteger (cd.extract (off + 320 * r) (off + 320 * (r + 1))) (10 * i) 10

/-- Window table entry `e < 768` of row `r`. -/
def tEntry (cd : ByteArray) (off r e : Nat) : Nat :=
  if 256 ≤ e ∧ e < 512 then t1f cd off r (e - 256) else 1023 - t1f cd off r (e % 256)

/-- The table `tbuild [tt, off]` writes at `tt`. -/
def TTable (m : ByteArray) (tt off : Nat) (cd : ByteArray) : Prop :=
  ∀ e, e < 768 → ∀ r, r < 4 → be16 m (tt + 6142 - 8 * e - 2 * r) = tEntry cd off r e

theorem t1f_32 (cd : ByteArray) (r i : Nat) : t1f cd 32 r i = t1v cd r i := rfl

theorem t1f_520 (cd : ByteArray) (r i : Nat) : t1f cd 0x520 r i = t1v cd (4 + r) i := by
  unfold t1f t1v
  rw [show 0x520 + 320 * r = 32 + 320 * (4 + r) by omega,
    show 0x520 + 320 * (r + 1) = 32 + 320 * (4 + r + 1) by omega]

end MlDsaOpt65.Proofs
