import MlDsa44.Proofs.Fn.Keccak
import MlDsa44.Proofs.Fn.Lanes
/-!
# `shake`: SHAKE128/256 sponge over memory

Yul: `function shake(rate, ptr, len, out, blocks)`. Zero the state, absorb
`len / rate` full blocks from `[ptr, …)`, copy the remainder into `PADB`
(zeroed as six words), add the `0x1F … 0x80` padding, absorb it, then write
`blocks` output blocks to `out` (the last lane store overhangs by 24 bytes).
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

/-- One absorb step per full block plus the padded block, the final-block
copy, and one squeeze step per output block. -/
def shake (rate len blocks : Nat) : Nat :=
  3000 + (len / rate + 1) * (xorBlock rate + keccakF + 100) +
    3 * ((len % rate + 31) / 32) + blocks * (keccakF + rate / 8 * 300 + 200)

end Gas

theorem shake_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {m : ByteArray} {rate ptr len out blocks : Nat}
    (hrate : rate = 136 ∨ rate = 168) (hblocks : 1 ≤ blocks ∧ blocks ≤ 6)
    (hrc : RCTable m)
    (hin : ZETA ≤ ptr) (hinPad : ptr + len ≤ PADB ∨ PADB + 192 ≤ ptr)
    (hout : ZETA ≤ out) (houtPad : out + blocks * rate + 32 ≤ PADB ∨ PADB + 192 ≤ out)
    (hdisj : ptr + len ≤ out ∨ out + blocks * rate + 32 ≤ ptr)
    (hmem : ptr + len + 32 ≤ 32 * s.activeWords.toNat ∧
      out + blocks * rate + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', BytesAt m' out (Fips202.squeeze rate
          (Fips202.absorb rate (Fips202.pad rate 0x1F (MachineState.readPadded m ptr len)))
          blocks) ∧
      FrameExcept m m' [(ST, RC), (PADB, PADB + 192), (out, out + blocks * rate + 24)] ∧
      Call s Entry.shake [wd rate, wd ptr, wd len, wd out, wd blocks] ret tail m [] m'
        (Gas.shake rate len blocks) := by
  sorry

end MlDsa44.Proofs
