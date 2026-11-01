import MlDsaOpt44.Fn.Fix
import MlDsaOpt44.Fn.Sponge
import MlDsaOpt44.Fn.Keccak
import MlDsaOpt44.Fn.Group.Pass3
import MlDsaOpt44.Fn.Group.Pass3m
import MlDsaOpt44.Fn.Group.Pass3k4
import MlDsaOpt44.Fn.Group.Main
/-!
# Fused ExpandA · ẑ: `pass3`, `pass3m`, `pass3k4`, `group` (WP6)

`pass3*` accumulate `ACC[t] += ABUF[t] · ẑ` lane-wise (one `MUL` per word: the
four row lanes of `ABUF[t]` are below `q < 2^23` and `ẑ < 2^28`, so lane
products stay below `2^51` and never carry). The contracts are exact word
equations; the lane reading is a pure lemma.

`group [amask, col, rb, ret] ↦ [ok]` is one pure ExpandA SIMD group (column
`col`, rows `0 … 3`): `ginit`, five `kf4` + `blk`, `gfix`, `pass3`. ML-DSA-44
calls it with `rb = 0`, `amask = 15`, `col ∈ {0, 1}`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **pass3**: `[64 k, ZH, ACC, ret]`; `ACC[t] += ABUF[t] · lane k of ZH[t]`. -/
theorem pass3_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3 ret tail) (m : ByteArray) {k : Nat} (hk : k < 4) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        (word m (ACC + 32 * t) + word m (ABUF + 32 * t) * lane (word m (ZH + 32 * t)) k) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3 [wd (64 * k), wd ZH, wd ACC] ret tail m [] m' Gas.pass3 := by
  exact GroupP.pass3_reach hs hr m hk

/-- **pass3m**: `[lm, 64 k, ZH, ACC, ret]`; as `pass3` with the candidate words
masked by `lm` (the lanes of active slots). -/
theorem pass3m_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3m ret tail) (m : ByteArray) {k lm : Nat} (hk : k < 4)
    (hlm : lm < 2 ^ 256) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) =
        (word m (ACC + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * lane (word m (ZH + 32 * t)) k) %
          2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3m [wd lm, wd (64 * k), wd ZH, wd ACC] ret tail m [] m' Gas.pass3m := by
  exact GroupP.pass3m_reach hs hr m hk hlm

/-- The Kronecker accumulation of the extra group: slots 3 and 2 hold
`A[3][2]`, `A[3][3]`; `ẑ_2, ẑ_3` are shifted into lanes 0, 1; lane 3 of the
product is `A[3][2] ẑ_2 + A[3][3] ẑ_3` (lower lanes are partial sums below
`2^53`, masked off). -/
def kronWord (m : ByteArray) (t : Nat) : Nat :=
  (word m (ABUF + 32 * t) &&& (2 ^ 256 - 2 ^ 128)) * (word m (ZH + 32 * t) / 2 ^ 128) % 2 ^ 256 &&&
    (M64 * 2 ^ 192)

/-- **pass3k4**: `[ret]`; `ACC[t] += kronWord t`. -/
theorem pass3k4_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3k4 ret tail) (m : ByteArray) :
    ∃ m', (∀ t, t < 256 → word m' (ACC + 32 * t) = (word m (ACC + 32 * t) + kronWord m t) % 2 ^ 256) ∧
      FrameExcept m m' [(ACC, ACC + 8192)] ∧
      Call s Entry.pass3k4 [] ret tail m [] m' Gas.pass3k4 := by
  exact GroupP.pass3k4_reach hs hr m

/-- `RHO1[x] = spread(ρ lane x)`, `RHO1[4 + x] = spread(c̃ lane x)` (`init_rho1`). -/
def Rho1At (m : ByteArray) (cd : ByteArray) : Prop :=
  ∀ x, x < 4 → word m (RHO1 + 32 * x) = spread (le64 cd (8 * x)) ∧
    word m (RHO1 + 32 * (4 + x)) = spread (le64 cd (CTOFF + 8 * x))

/-- Regions a SIMD group may write. -/
def groupFrame : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (BK, BK + 800),
    (ACC, ACC + 8192)]

/-- **group**: `[15, col, 0, ret] ↦ [ok]`; `ok` iff `A[r][col]` exists for all
rows, and then `ACC[t] += (A[0][col][t], …, A[3][col][t]) · ẑ_col[t]`. -/
theorem group_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {col : Nat} (hcol : col < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome) = true →
        ∀ t, t < 256 → word m' (ACC + 32 * t) =
          (word m (ACC + 32 * t) +
            pack4 (fun r => ((aD s.executionEnv.calldata r col)[t]!).toNat) *
              lane (word m (ZH + 32 * t)) col) % 2 ^ 256) ∧
      FrameExcept m m' groupFrame ∧
      Call s Entry.group [wd 15, wd col, wd 0] ret tail m
        [flag ((List.range 4).all fun r => (aOf s.executionEnv.calldata r col).isSome)] m'
        Gas.group := by
  exact GroupP.group_reach hs hr m hrc hrho hcol hcd

end MlDsaOpt44.Proofs
