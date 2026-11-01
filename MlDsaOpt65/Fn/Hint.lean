import MlDsaOpt65.Layout
import MlDsaOpt65.Budget
/-!
# `usehint`, `pack` (ML-DSA-65)

Open contracts (statements only); the proofs mirror `MlDsaOpt44/Fn/Hint.lean` and
`MlDsaOpt44/Fn/Hint/*` (`UseHint`, `UseHintRun`, `Pack*`), with the ML-DSA-65
parameters and the row-group pointers as parameters.

* `usehint [ACC + 0x2000 g, ret]`: for the 256 row-packed words `W` at `ACC_g`, lane-wise
  `W := UseHint(HP_g, (W − SP_g) mod q)` (`HP_g = ACC_g + 0x4000`, `SP_g = ACC_g − 0x4900`),
  with `x mod q` by the exact multiply-shift `(x · 1074791297) >> 53`, the `2γ2 = 523776`
  quotient by `((r + γ2 − 1) · 8396809) >> 42`, and `mod m = 16` by `AND 15`.
* `pack [nr, FIN + 256 + 2048 g, ACC + 0x2000 g, ret]`: `w1Encode` (4 bits per coefficient,
  16 stream lanes per row) of the rows `r < nr` of row group `g`, each 64-bit stream lane
  replicated (`rep`) into `FIN` for `kf1`; rows `≥ nr` are skipped.

Call sites (`MlDsaOpt/65/opt.asm`, segment w): `usehint [ACC]`, `pack [4, FIN + 256, ACC]`,
`usehint [ACC + 0x2000]`, `pack [2, FIN + 256 + 2048, ACC + 0x2000]`.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **usehint**: `[ACC + 0x2000 g, ret]`, `g < 2`. Exact on words whose lanes are in range;
every output lane is below `m = 16` unconditionally (the result is masked by `AND 15`). -/
theorem usehint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.usehint ret tail) (m : ByteArray) {g : Nat} (hg : g < 2) :
    ∃ m', (∀ t, t < 256 →
        (∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 2 ^ 27 ∧
          lane (word m (SP + 0x2000 * g + 32 * t)) r < 2 ^ 29 ∧
          lane (word m (HP + 0x2000 * g + 32 * t)) r ≤ 1) →
        ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r =
          (Fips204.useHint P (lane (word m (HP + 0x2000 * g + 32 * t)) r)
            ((lane (word m (ACC + 0x2000 * g + 32 * t)) r : Int) -
              lane (word m (SP + 0x2000 * g + 32 * t)) r)).toNat) ∧
      (∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (ACC + 0x2000 * g + 32 * t)) r < 16) ∧
      FrameExcept m m' [(ACC + 0x2000 * g, ACC + 0x2000 * g + 8192)] ∧
      Call s Entry.usehint [wd (ACC + 0x2000 * g)] ret tail m [] m' Gas.usehint := by
  sorry

/-- **pack**: `[nr, FIN + 256 + 2048 g, ACC + 0x2000 g, ret]`, `g < 2`, `nr ∈ {2, 4}`.
Row `r < nr` of row group `g` (lane `r` of `ACC_g`) is 4-bit packed; its stream lane
`j < 16` goes to `FIN[8 + 16 (4 g + r) + j]`, replicated. -/
theorem pack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) {g nr : Nat} (hg : g < 2)
    (hnr : nr = 2 ∨ nr = 4) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 16) →
        ∀ r, r < nr → ∀ j, j < 16 → word m' (FIN + 256 + 2048 * g + 32 * (16 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m (ACC + 0x2000 * g) r) 15) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256 + 2048 * g, FIN + 256 + 2048 * g + 512 * nr)] ∧
      Call s Entry.pack [wd nr, wd (FIN + 256 + 2048 * g), wd (ACC + 0x2000 * g)] ret tail m []
        m' (Gas.pack nr) := by
  sorry

end MlDsaOpt65.Proofs
