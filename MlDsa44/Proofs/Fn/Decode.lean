import MlDsa44.Proofs.Fn.Ntt
import MlDsa44.Proofs.Fn.Unpack
/-!
# Signature decoding: `decodeHint` and `decodeZ`

Calldata layout: `pk = [0, 1312)`, `σ = [1312, 3732)` with `c̃ = [1312, 1344)`,
`z = [1344, 3648)` (four 576-byte polynomials, 18 bits per coefficient) and
`h = [3648, 3732)` (`ω = 80` index bytes, then `k = 4` counts).

Yul:
* `decodeHint() -> good`: zero `HB`, then Algorithm 21 with every
  `return ⊥` turned into `good := 0` and the scan clamped so it stays
  bounded; set bytes go to `HB + 256 i + y`;
* `decodeZ() -> good`: for each `z[i]`, unpack, check `β < raw < 2γ₁ − β`
  (`‖z‖∞ < γ₁ − β`), store `(γ₁ − raw) mod q` at `ZH + POLY i`, then NTT.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def decodeHint : Nat := 32 * 30 + 4 * 200 + 80 * 250 + 200

def decodeZ : Nat := 4 * (256 * (unpack + 150) + ntt + 100) + 100

end Gas

/-- The signature field of EIP-8355 calldata. -/
def sigOf (cd : ByteArray) : ByteArray := cd.extract 1312 3732

/-- The public-key field of EIP-8355 calldata. -/
def pkOf (cd : ByteArray) : ByteArray := cd.extract 0 1312

/-- `z` as decoded by `sigDecode`. -/
def zOf (cd : ByteArray) : Array Fips204.Poly := (Fips204.sigDecode (sigOf cd)).2.1

/-- The hint field of the signature. -/
def hintBytesOf (cd : ByteArray) : ByteArray := cd.extract 3648 3732

theorem decodeHint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.decodeHint ret tail) (m : ByteArray) (hcd : 3732 ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ h, Fips204.hintBitUnpack (hintBytesOf s.executionEnv.calldata) = some h →
        HintAt m' h) ∧
      FrameExcept m m' [(HB, HB + 0x400)] ∧
      Call s Entry.decodeHint [] ret tail m
        [flag (Fips204.hintBitUnpack (hintBytesOf s.executionEnv.calldata)).isSome] m'
        Gas.decodeHint := by
  sorry

theorem decodeZ_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.decodeZ ret tail) {m : ByteArray} (hz : ZetaTable m)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ i, i < 4 →
        PolyAt m' (ZH + POLY * i)
          (Fips204.ntt ((zOf s.executionEnv.calldata)[i]!.map (· % (Fips204.q : Int)))) ∧
        Reduced (Fips204.ntt ((zOf s.executionEnv.calldata)[i]!.map (· % (Fips204.q : Int))))) ∧
      FrameExcept m m' [(ZH, ZH + 4 * POLY)] ∧
      Call s Entry.decodeZ [] ret tail m
        [flag (Fips204.normBelow (zOf s.executionEnv.calldata)
          (Fips204.gamma1 - Fips204.beta))] m'
        Gas.decodeZ := by
  sorry

end MlDsa44.Proofs
