import MlDsaOpt65.Layout
set_option warningAsError true
/-!
# Vocabulary of the ExpandA SIMD groups (ML-DSA-65)

`Rho1At` (what `init_rho1` leaves at `RHO1`), `ginitWord` (the word `ginit`
stores), `gOk` (the flag of `group`) and `groupFrame` (what `group` may write).
Light module: only `MlDsaOpt65.Layout`.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- `RHO1[x] = spread(ρ lane x)` (`x < 4`), `RHO1[4 + x] = spread(c̃ lane x)` (`x < 6`):
the rows `init_rho1` stores in the main flow (pcs 3115–3565). -/
def Rho1At (m : ByteArray) (cd : ByteArray) : Prop :=
  (∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x))) ∧
  (∀ x, x < 6 → word m (RHO1 + 32 * (4 + x)) = spread (le64 cd (CTOFF + 8 * x)))

/-- The word `ginit` stores at lane `x` (`gen_ginit`, ML-DSA-65: c̃ has six
lanes): ρ lanes `x < 4` times `amult`, c̃ lanes `x < 6` times `cmult`, lane 4
(`l4`), c̃'s SHAKE256 domain byte `0x1F` in lane 6 (`spread 0x1F · cmult`), the
`0x80` padding bits in lane 16 (`cmult`, rate 136) and lane 20 (`amult`, rate
168), complemented lanes inverted in fresh slots (`NOT keep`), and the `keep`
slots carried over. Every product is a 256-bit `MUL`. -/
def ginitWord (m : ByteArray) (keep amult cmult l4 x : Nat) : Nat :=
  let da := if x < 4 then word m (RHO1 + 32 * x) * amult % 2 ^ 256 else 0
  let dc := if x < 6 then word m (RHO1 + 32 * (4 + x)) * cmult % 2 ^ 256 else 0
  let d1 := if x = 4 then l4 else 0
  let d5 := if x = 6 then spread 0x1F * cmult % 2 ^ 256 else 0
  let d2 := if x = 16 then spread (2 ^ 63) * cmult % 2 ^ 256 else 0
  let d3 := if x = 20 then spread (2 ^ 63) * amult % 2 ^ 256 else 0
  let d4 := if x ∈ complemented then 2 ^ 256 - 1 - keep else 0
  (da ^^^ dc ^^^ d1 ^^^ d5 ^^^ d2 ^^^ d3 ^^^ d4) ||| (word m (KS + 32 * x) &&& keep)

/-- The flag of `group [amask, col, rb]`: every active slot `r` (bit `r` of
`amask`) has its matrix entry `A[4 rb + r][col]`. -/
def gOk (cd : ByteArray) (amask col rb : Nat) : Bool :=
  (List.range 4).all fun r => !amask.testBit r || (aOf cd (4 * rb + r) col).isSome

/-- Regions `group [amask, col, rb]` may write: the Keccak / ExpandA scratch
and the accumulators of row group `rb`. -/
def groupFrame (rb : Nat) : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800),
    (ACC + 8192 * rb, ACC + 8192 * rb + 8192)]

end MlDsaOpt65.Proofs
