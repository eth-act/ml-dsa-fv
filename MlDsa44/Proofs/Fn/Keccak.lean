import MlDsa44.Proofs.Layout
/-!
# `keccakF`: Keccak-f[1600] on the lanes at `ST`

Yul: `function keccakF()`; twelve iterations of two straight-line rounds,
`ST → BT` then `BT → ST`, with column parities in `CT` and round constants
read from `RC`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def keccakF : Nat := 54328

end Gas

theorem keccakF_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) {m : ByteArray} {A : Array UInt64}
    (hA : LanesAt m ST A) (hrc : RCTable m) :
    ∃ m', LanesAt m' ST (Crypto.Keccak.permute A) ∧ FrameExcept m m' [(ST, RC)] ∧
      Call s Entry.keccakF [] ret tail m [] m' Gas.keccakF := by
  sorry

end MlDsa44.Proofs
