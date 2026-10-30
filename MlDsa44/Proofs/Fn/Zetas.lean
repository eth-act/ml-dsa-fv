import MlDsa44.Proofs.Layout
/-!
# `brv8` and `initZetas`

Yul:
* `brv8(i) -> r`: eight-step bit reversal;
* `initZetas()`: `mstore(ZETA + 32 brv8(i), ζ^i mod q)` for `i < 256`,
  so every `zetas[k] = ζ^BitRev8(k) mod q` lands at `ZETA + 32 k`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def brv8 : Nat := 800

def initZetas : Nat := 256 * (brv8 + 150) + 100

end Gas

theorem brv8_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) (m : ByteArray) {i : Nat} (hi : i < 256) :
    Call s Entry.brv8 [wd i] ret tail m [wd (Fips204.bitRev8 i)] m Gas.brv8 := by
  sorry

theorem initZetas_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) (m : ByteArray) :
    ∃ m', ZetaTable m' ∧ FrameExcept m m' [(ZETA, ZETA + POLY)] ∧
      Call s Entry.initZetas [] ret tail m [] m' Gas.initZetas := by
  sorry

end MlDsa44.Proofs
