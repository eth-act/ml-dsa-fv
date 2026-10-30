import MlDsa44.Proofs.Layout
/-!
# `useHint` and `encodeRow`

Yul:
* `useHint(hb, r) -> r1`: Algorithm 40 (with Algorithm 36) on `r ∈ [0, q)`
  using unsigned arithmetic: `r0' = r mod 2γ₂`, negative iff `r0' > γ₂`;
* `encodeRow(i)`: for `g < 64`, four `useHint(HB[256 i + t], ACC[t])` values
  of 6 bits packed into three bytes at `W1 + 64 + 192 i + 3 g`
  (`w1Encode` row `i`, Algorithm 28).
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def useHint : Nat := 250

def encodeRow : Nat := 64 * (4 * (useHint + 150) + 300) + 100

end Gas

theorem useHint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) (m : ByteArray) {hb r : Nat} (hhb : hb ≤ 1)
    (hrq : r < Fips204.q) :
    Call s Entry.useHint [wd hb, wd r] ret tail m
      [wd (Fips204.useHint hb r).toNat] m Gas.useHint := by
  sorry

/-- Row `i` of `w1 = UseHint(h, w)`, with the hint bits read from `HB`. -/
def w1Row (m : ByteArray) (i : Nat) (f : Fips204.Poly) : Fips204.Poly :=
  (Array.range 256).map fun j => Fips204.useHint (byteAt m (HB + 256 * i + j)) f[j]!

theorem encodeRow_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) {m : ByteArray} {i : Nat} (hi : i < 4) {f : Fips204.Poly}
    (hf : PolyAt m ACC f) (hred : Reduced f)
    (hbits : ∀ j, j < 256 → byteAt m (HB + 256 * i + j) ≤ 1) :
    ∃ m', BytesAt m' (W1 + 64 + 192 * i)
        (Fips204.simpleBitPack (w1Row m i f) ((Fips204.q - 1) / (2 * Fips204.gamma2) - 1)) ∧
      FrameExcept m m' [(W1 + 64 + 192 * i, W1 + 64 + 192 * (i + 1))] ∧
      Call s Entry.encodeRow [wd i] ret tail m [] m' Gas.encodeRow := by
  sorry

end MlDsa44.Proofs
