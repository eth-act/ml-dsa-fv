import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Fn.Hint.G5Pack
/- Ported from `MlDsaOpt87/Fn/Hint.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# `usehint`, `pack` (ML-DSA-87)

Proved in `Fn/Hint/UseHint4.lean` (v4) and `Fn/Hint/G5Pack.lean` (+ `G5PackBlocks`; the code is
the ML-DSA-65 code relocated, the pack proof covers `nr ∈ {2, 4}`); the pure part is
`MlDsaOpt65/Fn/Hint/G5Pure.lean`. They follow `MlDsaOpt44/Fn/Hint/*` with the ML-DSA-87
parameters and the row-group pointers as parameters.

* `usehint [ACC + 0x2000 g, ret]` (v4): for the 256 row-packed words `W` at `ACC_g`,
  lane-wise `W := UseHint(HP_g, W + SP_g − spOff)` (`SP` stores `spOff − (2^13 S' + n_neg)`,
  `y = x − ⌊x/q⌋` instead of `x mod q`; v3 description:)
  `W := UseHint(HP_g, (W − SP_g) mod q)` (`HP_g = ACC_g + 0x4000`, `SP_g = ACC_g − 0x4900`),
  with `x mod q` by the exact multiply-shift `(x · 1074791297) >> 53`, the `2γ2 = 523776`
  quotient and the sign of `r0` by one exact multiply-shift
  `D = ((r + γ2 − 1) · 16793617) >> 42 = 2 r1 + [r0 > 0]`, the lane value
  `(D >> 1) + 16 − h + 2 (h & D)`, and `mod m = 16` by `AND 15`.
* `pack [4, FIN + 256 + 2048 g, ACC + 0x2000 g, ret]`: `w1Encode` (4 bits per coefficient,
  16 stream lanes per row) of the four rows of row group `g`, each 64-bit stream lane
  replicated (`rep`) into `FIN` for `kf1`.

Call sites (`MlDsaOpt/87/opt.asm`, segment w): `usehint [ACC]`, `pack [4, FIN + 256, ACC]`,
`usehint [ACC + 0x2000]`, `pack [4, FIN + 256 + 2048, ACC + 0x2000]`.
-/

namespace MlDsaOptGlam87.Proofs

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

-- glam: no `usehint` (UseHint is fused into `intt`)

/-- **pack**: `[4, FIN + 256 + 2048 g, ACC + 0x2000 g, ret]`, `g < 2`.
Row `r < 4` of row group `g` (lane `r` of `ACC_g`) is 4-bit packed; its stream lane
`j < 16` goes to `FIN[8 + 16 (4 g + r) + j]`, replicated. -/
theorem pack_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pack ret tail) (m : ByteArray) {g : Nat} (hg : g < 2) :
    ∃ m', ((∀ t, t < 256 → ∀ r, r < 4 → lane (word m (ACC + 0x2000 * g + 32 * t)) r < 16) →
        ∀ r, r < 4 → ∀ j, j < 16 → word m' (FIN + 256 + 2048 * g + 32 * (16 * r + j)) =
          rep (le64 (Fips204.simpleBitPack (lanesPoly m (ACC + 0x2000 * g) r) 15) (8 * j))) ∧
      FrameExcept m m' [(FIN + 256 + 2048 * g, FIN + 256 + 2048 * g + 2048)] ∧
      Call s Entry.pack [wd 4, wd (FIN + 256 + 2048 * g), wd (ACC + 0x2000 * g)] ret tail m []
        m' (Gas.pack 4) :=
  G5PK.pack_main hs hr m hg (Or.inr rfl)

end MlDsaOptGlam87.Proofs
