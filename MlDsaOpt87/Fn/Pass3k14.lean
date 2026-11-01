import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/-!
# `pass3k14`: Kronecker accumulation of SIMD group 14 (ML-DSA-87)

Open contract (statement only). Group 14 (`MlDsaOpt/87/layout.txt`) samples
`A[7][6], A[7][5], A[7][4], A[7][3]` in slots 0–3, so lane `3 − i` of `ABUF[t]` is
`A[7][3 + i][t]` (`Gen.gen_pass3k "pass3k14" rb = 1, j0 = 3, n = 4`: no candidate mask).
The multiplier word puts `ẑ_3` (lane 3 of `ZH[t]`) into lane 0 and `ẑ_4, ẑ_5, ẑ_6`
(lanes 0–2 of `ZH2[t]`) into lanes 1–3; lane 3 of the product is then
`Σ_i A[7][3 + i][t] · ẑ_{3+i}[t]` (lower lanes are partial sums below `2^53` when the
inputs are in range, masked off), added to lane 3 of the row-group-1 accumulator
`ACC + 0x2000` (row 7). Call site: `pass3k14 []` at the end of group 14 (pc 5585).
The proof mirrors `MlDsaOpt44/Fn/Group/Pass3k4.lean` (`GroupP.pass3k4_reach`).
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- The Kronecker word of group 14 at `t`: `ABUF[t] · ((ZH[t] >> 192) | (ZH2[t] << 64))`,
masked to lane 3. -/
def kronWord14 (m : ByteArray) (t : Nat) : Nat :=
  word m (ABUF + 32 * t) *
      (word m (ZH + 32 * t) / 2 ^ 192 ||| word m (ZH2 + 32 * t) * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&&
    (M64 * 2 ^ 192)

/-- **pass3k14**: `[ret]`; `ACC[0x2000 + 32 t] += kronWord14 t` for `t < 256`. -/
theorem pass3k14_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3k14 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 0x2000 + 32 * t) =
        (word m (ACC + 0x2000 + 32 * t) + kronWord14 m t) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC + 0x2000, ACC + 0x4000)] ∧
      Call s Entry.pass3k14 [] ret tail m [] m' Gas.pass3k14 := by
  sorry

end MlDsaOpt87.Proofs
