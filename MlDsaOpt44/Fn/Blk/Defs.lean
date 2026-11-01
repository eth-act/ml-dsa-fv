import MlDsaOpt44.Layout
/-!
# `blk`: candidate bytes and flag words of a squeezed SIMD block (WP3)
-/

namespace MlDsaOpt44.Proofs

open MlDsa44

/-- Byte `j` of the squeezed block of a state (`stateBytes 168 S`). -/
def sbyte (S : Fips202.SpongeState) (j : Nat) : Nat := laneOf S (j / 8) / 2 ^ (8 * (j % 8)) % 256

/-- RejNTTPoly candidate `i < 56` of a block: three bytes, top bit masked
(FIPS 204 Algorithm 14 before the `< q` test). -/
def cand (S : Fips202.SpongeState) (i : Nat) : Nat :=
  sbyte S (3 * i) + 256 * sbyte S (3 * i + 1) + 65536 * (sbyte S (3 * i + 2) % 128)

/-- Flag word `g` of a block: lane `k` bit 23 is set iff slot `k` rejected one
of the candidates `8g … 8g + 7` (`cand + 2^23 − q < 2^24`, no carry). -/
def flagWord (S : Nat → Fips202.SpongeState) (g : Nat) : Nat :=
  orList ((List.range 8).map fun i => pack4 fun k => cand (S k) (8 * g + i) + 2 ^ 23 - Fips204.q)

end MlDsaOpt44.Proofs
