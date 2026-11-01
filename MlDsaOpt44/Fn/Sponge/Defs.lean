import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
set_option warningAsError true
/-!
# Definitions used by the sponge-glue contracts (`Fn/Sponge.lean`)
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- `spread (2^63)`: the SHAKE final padding bit `0x80` of byte 7 of a lane. -/
def padTop : Nat := spread (2 ^ 63)

/-- The word `ginit` stores at lane `x` (see `Gen.gen_ginit`): ρ (resp. c̃)
lanes from `RHO1` times the slot multipliers, lane 4 (`l4`, carrying every
slot's column/row bytes and padding), the `0x80` padding bits, complemented
lanes inverted in fresh slots, and the `keep` slots carried over. -/
def ginitWord (m : ByteArray) (keep amult cmult l4 x : Nat) : Nat :=
  let d0 := if x < 4 then
      (word m (RHO1 + 32 * x) * amult % 2 ^ 256) ^^^ (word m (RHO1 + 32 * (4 + x)) * cmult % 2 ^ 256)
    else 0
  let d1 := if x = 4 then l4 else 0
  let d2 := if x = 16 then padTop * cmult % 2 ^ 256 else 0
  let d3 := if x = 20 then padTop * amult % 2 ^ 256 else 0
  let d4 := if x ∈ complemented then 2 ^ 256 - 1 - keep else 0
  (d0 ^^^ d1 ^^^ d2 ^^^ d3 ^^^ d4) ||| (word m (KS + 32 * x) &&& keep)

/-- The calldata word at `a` with the bytes of every 64-bit lane reversed:
lane `3 − j` (from the top, `j`) is `LE64(cd[a + 8j …])`. -/
def bsw (cd : ByteArray) (a : Nat) : Nat :=
  pack4 fun k => le64 cd (a + 8 * (3 - k))

/-- Lane `u` (`u = 4i + j`) absorbed by `trabs off sh n4 lm`: group `i` is the
calldata word at `off + 32 i`, byte-swapped per lane; the last group is masked
by `lm`; lane `j` from the top. -/
def trLane (cd : ByteArray) (off lm n4 u : Nat) : Nat :=
  let w := bsw cd (off + 32 * (u / 4))
  let w' := if u / 4 + 1 = n4 then w &&& lm else w
  w' / 2 ^ (192 - 64 * (u % 4)) % 2 ^ 64

/-- μ's single padded SHAKE256 block for `|M| ≤ 69`: `tr ‖ 0 ‖ 0 ‖ M ‖ pad`. -/
def muBlock (tr : ByteArray) (cd : ByteArray) : ByteArray :=
  Fips202.pad 136 0x1F (tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd))

end MlDsaOpt44.Proofs
