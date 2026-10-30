import MlDsa44.Proofs.Fn.Shake
import MlDsa44.Proofs.Fn.Sampling
import MlDsa44.Proofs.Fn.Decode
/-!
# `computeRow`: one row of `w'Approx = NTT⁻¹(Â ∘ ẑ − ĉ ∘ t̂₁)`

Yul: `computeRow(i) -> good`. Zero `ACC`; for `j < 4`: set the seed bytes
`SEEDA[32] = j`, `SEEDA[33] = i`, squeeze six SHAKE128 blocks of
`ρ ‖ j ‖ i` into `XOF`, `rejSample(AP)`, accumulate `AP ∘ ZH[j]` into `ACC`.
Then unpack `t1[i]` from calldata scaled by `2^13` into `TP`, `ntt(TP)`,
subtract `CH ∘ TP`, and `nttInv(ACC)`. `good` iff every `RejNTTPoly`
succeeded within the Appendix C limit.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def computeRow : Nat :=
  zeroPoly + 4 * (shake 168 34 6 + rejSample + 256 * 150 + 200) +
    256 * (unpack + 100) + ntt + 256 * 150 + nttInv + 500

end Gas

/-- `Â[i][j] = RejNTTPoly(ρ ‖ j ‖ i)` (Algorithm 32). -/
def aEntry (rho : ByteArray) (i j : Nat) : Option Fips204.Poly :=
  Fips204.rejNTTPoly (rho ++ ByteArray.mk #[UInt8.ofNat j, UInt8.ofNat i])

/-- `NTT(t1[i] · 2^d)` for the public key `pk`. -/
def t1Hat (pk : ByteArray) (i : Nat) : Fips204.Poly :=
  Fips204.ntt (((Fips204.pkDecode pk).2[i]!).map (· * 2 ^ Fips204.d))

/-- Row `i` of `NTT⁻¹(Â ∘ ẑ − ĉ ∘ t̂₁)` from row `i` of `Â`. -/
def rowApprox (aRow zHat : Array Fips204.Poly) (cHat t1H : Fips204.Poly) : Fips204.Poly :=
  let az := (List.range Fips204.l).foldl
    (fun acc j => Fips204.addNTT acc (Fips204.multiplyNTT aRow[j]! zHat[j]!)) Fips204.zeroPoly
  Fips204.nttInv ((Array.range 256).map fun j =>
    (az[j]! - (Fips204.multiplyNTT cHat t1H)[j]!) % Fips204.q)

theorem computeRow_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK ret tail) {m : ByteArray} {i : Nat} (hi : i < 4)
    (hcd : 3732 ≤ s.executionEnv.calldata.size)
    (hrc : RCTable m) (hz : ZetaTable m)
    {zHat : Array Fips204.Poly} (hzHat : zHat.size = 4)
    (hzs : ∀ j, j < 4 → PolyAt m (ZH + POLY * j) zHat[j]! ∧ Reduced zHat[j]!)
    {cHat : Fips204.Poly} (hc : PolyAt m CH cHat) (hcred : Reduced cHat)
    (hrho : BytesAt m SEEDA (pkOf s.executionEnv.calldata |>.extract 0 32)) :
    ∃ m',
      (∀ aRow : Array Fips204.Poly, aRow.size = 4 →
        (∀ j, j < 4 → aEntry ((pkOf s.executionEnv.calldata).extract 0 32) i j = some aRow[j]!) →
          PolyAt m' ACC (rowApprox aRow zHat cHat (t1Hat (pkOf s.executionEnv.calldata) i)) ∧
          Reduced (rowApprox aRow zHat cHat (t1Hat (pkOf s.executionEnv.calldata) i))) ∧
      FrameExcept m m' [(ST, RC), (AP, AP + POLY), (ACC, ACC + POLY), (TP, TP + POLY),
        (XOF, XOF + 0x420), (SEEDA + 32, SEEDA + 34), (PADB, PADB + 192)] ∧
      Call s Entry.computeRow [wd i] ret tail m
        [flag ((List.range 4).all fun j =>
          (aEntry ((pkOf s.executionEnv.calldata).extract 0 32) i j).isSome)] m'
        Gas.computeRow := by
  sorry

end MlDsa44.Proofs
