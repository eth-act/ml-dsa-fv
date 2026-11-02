import MlDsaOpt87.Layout
set_option warningAsError true
/-!
# Vocabulary of the ExpandA SIMD groups (ML-DSA-87)

`Rho1At` (what `init_rho1` leaves at `RHO1`), `ginitWord` (the word `ginit`
stores), `gOk` (the flag of `group`) and `groupFrame` (what `group` may write).
Light module: only `MlDsaOpt87.Layout`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- `RHO1[x] = spread(ρ lane x)`, `x < 4`: the rows `init_rho1` stores in the
main flow (ML-DSA-87 has no c̃ rider). -/
def Rho1At (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x))

/-- The word `ginit` stores at lane `x` (`gen_ginit`, ML-DSA-87: no c̃ slot, the
`cmult` argument is unused): ρ lanes `x < 4` times `amult`, lane 4 (`l4`), the
`0x80` padding bits in lane 20 (`amult`, rate 168), complemented lanes inverted
in fresh slots (`NOT keep`), and the `keep` slots carried over. Every product
is a 256-bit `MUL`. -/
def ginitWord (m : ByteArray) (keep amult _cmult l4 x : Nat) : Nat :=
  let da := if x < 4 then word m (RHO1 + 32 * x) * amult % 2 ^ 256 else 0
  let d1 := if x = 4 then l4 else 0
  let d3 := if x = 20 then spread (2 ^ 63) * amult % 2 ^ 256 else 0
  let d4 := if x ∈ complemented then 2 ^ 256 - 1 - keep else 0
  (da ^^^ d1 ^^^ d3 ^^^ d4) ||| (word m (KS + 32 * x) &&& keep)

/-- The flag of `group [amask, col, rb]`: every active slot `r` (bit `r` of
`amask`) has its matrix entry `A[4 rb + r][col]`. -/
def gOk (cd : ByteArray) (amask col rb : Nat) : Bool :=
  (List.range 4).all fun r => !amask.testBit r || (aOf cd (4 * rb + r) col).isSome

/-- Regions `group [amask, col, rb]` may write: the Keccak / ExpandA scratch
(v4: the caller accumulates, so no accumulator; `rb` is kept for the callers). -/
def groupFrame (_rb : Nat) : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800)]

/-- Lane `j % 4` of `ẑ`'s word `t` in table `j / 4`: `ẑ_j[t]`. -/
def zl (m : ByteArray) (j t : Nat) : Nat := lane (word m (ZH + 8192 * (j / 4) + 32 * t)) (j % 4)

end MlDsaOpt87.Proofs
