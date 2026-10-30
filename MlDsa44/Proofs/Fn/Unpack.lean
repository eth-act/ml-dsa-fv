import MlDsa44.Proofs.Layout
/-!
# `unpack`: one little-endian bit-packed coefficient from calldata

Yul: `unpack(off, i, c) -> v`; reads four bytes at `off + (i c) / 8`
little-endian, shifts by `(i c) mod 8` and masks `c` bits.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def unpack : Nat := 200

end Gas

/-- Coefficient `i` of the `c`-bit packing of the calldata field
`[off, off + n)`. -/
theorem unpack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) (m : ByteArray) {off n i c : Nat}
    (hc : 1 ≤ c ∧ c ≤ 18) (hfield : off + n ≤ s.executionEnv.calldata.size)
    (hi : (i + 1) * c ≤ 8 * n) :
    Call s Entry.unpack [wd off, wd i, wd c] ret tail m
      [wd (Fips204.bitsToInteger (s.executionEnv.calldata.extract off (off + n)) (i * c) c)]
      m Gas.unpack := by
  sorry

end MlDsa44.Proofs
