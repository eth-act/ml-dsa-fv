import MlDsaOpt65.Fn.Group.Defs
import MlDsaOpt65.Fn.Ginit.Call
import MlDsaOpt65.Fn.Fix
import MlDsaOpt65.Fn.Keccak
import MlDsaOpt65.Fn.Blk
/-!
# ExpandA groups and the fused accumulation (ML-DSA-65, v4)

`group [amask, col, rb, ret] ↦ [ok]` is one pure ExpandA SIMD group: column
`col`, slot `r` the row `4 rb + r` when bit `r` of `amask` is set: `ginit`, five
`kf4` with `blk` (`blkh` for the last block), `gfix amask`. v4: the group's
fixed-up candidates are left in `ABUF[0, 256)`; the main flow copies them to a
side buffer, and the fused passes `pass3f*` (generator `gen_pass3f`,
`plan_accumulation`) store or add every product of a batch into one
accumulator table, reading and writing each word once.

`ginit` (`Fn/Ginit/Call.lean`); `ginitWord`, `Rho1At`, `gOk`, `groupFrame`,
`zl` are in `Fn/Group/Defs.lean`.
-/

namespace MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **group**: `[amask, col, rb, ret] ↦ [ok]`; `ok` iff the active slots' rows
of column `col` exist, and then lane `r` of `ABUF[t]` is `A[4 rb + r][col][t]`
for the active slots `r` (other lanes hold values below `2^23`). -/
theorem group_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.group ret tail) (m : ByteArray) (hrc : RC4Table m)
    (hrho : Rho1At m s.executionEnv.calldata) {amask col rb : Nat} (hamask : amask < 16)
    (hcol : col < 8) (hrb : rb < 2) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (gOk s.executionEnv.calldata amask col rb = true →
        ∃ junk : Nat → Nat → Nat, (∀ r t, junk r t < 2 ^ 23) ∧
        ∀ t, t < 256 → word m' (ABUF + 32 * t) =
          pack4 (fun r => if amask.testBit r then
            ((aD s.executionEnv.calldata (4 * rb + r) col)[t]!).toNat else junk r t)) ∧
      FrameExcept m m' (groupFrame rb) ∧
      Call s Entry.group [wd amask, wd col, wd rb] ret tail m
        [flag (gOk s.executionEnv.calldata amask col rb)] m' Gas.group :=
  sorry

/-- A fused pass's frame and call, given the word it stores at `acc[t]`. -/
def FusedPass (s : State) (entry ret : Nat) (tail : List UInt256) (m : ByteArray) (acc gas : Nat)
    (W : ByteArray → Nat → Nat) : Prop :=
  ∃ m', (∀ t, t < 256 → word m' (acc + 32 * t) = W m t) ∧
    FrameExcept m m' [(acc, acc + 8192)] ∧ Call s entry [] ret tail m [] m' gas

/-- `x · ẑ_j` of buffer word `t` (lane-wise product, one `MUL`). -/
def bz (m : ByteArray) (b j t : Nat) : Nat := word m (b + 32 * t) * zl m j t

/-- As `bz` with the buffer word masked by `msk` and shifted left by `64 d`. -/
def bzl (m : ByteArray) (b msk d j t : Nat) : Nat :=
  (word m (b + 32 * t) &&& msk) * 2 ^ (64 * d) % 2 ^ 256 * zl m j t

/-- As `bz` with the buffer word masked by `msk` and shifted right by `64 d`. -/
def bzr (m : ByteArray) (b msk d j t : Nat) : Nat :=
  (word m (b + 32 * t) &&& msk) / 2 ^ (64 * d) * zl m j t

/-- `pass3f4`: row group 0, columns 0 … 4 (side buffers `CW`, `HP`,
`HP + 0x2000`, `ACC + 0x2000`, and `ABUF`). -/
def p3f4Word (m : ByteArray) (t : Nat) : Nat :=
  (bz m CW 0 t + bz m HP 1 t + bz m (HP + 8192) 2 t + bz m (ACC + 8192) 3 t + bz m ABUF 4 t) % 2 ^ 256

/-- `pass3f8`: row group 1 (rows 4, 5): the instances of groups 5 … 8 in slots
0 … 2, moved to their rows' lanes. -/
def p3f8Word (m : ByteArray) (t : Nat) : Nat :=
  (bzl m CW (2 ^ 128 - 1) 0 0 t + bzr m CW (2 ^ 192 - 2 ^ 128) 2 1 t +
    bzl m HP (2 ^ 64 - 1) 1 1 t + bzr m HP (2 ^ 192 - 2 ^ 64) 1 2 t +
    bzl m (HP + 8192) (2 ^ 128 - 1) 0 3 t + bzr m (HP + 8192) (2 ^ 192 - 2 ^ 128) 2 4 t +
    bzl m ABUF (2 ^ 64 - 1) 1 4 t) % 2 ^ 256

theorem pass3f4_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f4 ret tail m ACC Gas.pass3f4 p3f4Word :=
  sorry

theorem pass3f8_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f8 ret tail m (ACC + 8192) Gas.pass3f8 p3f8Word :=
  sorry

end MlDsaOpt65.Proofs
