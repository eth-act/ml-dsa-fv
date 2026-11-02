import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Fn.Ginit.Call
import MlDsaOpt87.Fn.Fix
import MlDsaOpt87.Fn.Keccak
import MlDsaOpt87.Fn.Blk
import MlDsaOpt87.Fn.GroupV4.Main
/-!
# ExpandA groups and the fused accumulation (ML-DSA-87, v4)

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

namespace MlDsaOpt87.Proofs

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
  group_call_aux hs hr m hrc hrho hamask hcol hrb hcd

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

/-- `pass3f4`: row group 0, columns 0 … 4 (stores). -/
def p3f4Word (m : ByteArray) (t : Nat) : Nat :=
  (bz m CW 0 t + bz m HP 1 t + bz m (HP + 8192) 2 t + bz m (ACC + 8192) 3 t + bz m ABUF 4 t) % 2 ^ 256

/-- `pass3f6`: row group 0, columns 5, 6 (adds). -/
def p3f6Word (m : ByteArray) (t : Nat) : Nat :=
  (word m (ACC + 32 * t) + bz m CW 5 t + bz m ABUF 6 t) % 2 ^ 256

/-- `pass3f10`: row group 1, columns 0 … 2 and column 3 rows 4 … 6 (stores). -/
def p3f10Word (m : ByteArray) (t : Nat) : Nat :=
  (bz m CW 0 t + bz m HP 1 t + bz m (HP + 8192) 2 t + bzl m ABUF (2 ^ 192 - 1) 0 3 t) % 2 ^ 256

/-- The Kronecker term of `pass3f14`: lane 3 of `ABUF[t] · (ẑ_3, ẑ_4, ẑ_5, ẑ_6)`. -/
def kron14 (m : ByteArray) (t : Nat) : Nat :=
  word m (ABUF + 32 * t) *
      (word m (ZH + 32 * t) / 2 ^ 192 ||| word m (ZH + 8192 + 32 * t) * 2 ^ 64 % 2 ^ 256) % 2 ^ 256 &&&
    (M64 * 2 ^ 192)

/-- `pass3f14`: row group 1, columns 4 … 6 rows 4 … 6, and row 7 columns 3 … 6
(adds). -/
def p3f14Word (m : ByteArray) (t : Nat) : Nat :=
  (word m (ACC + 8192 + 32 * t) + bzl m CW (2 ^ 192 - 1) 0 4 t + bzl m HP (2 ^ 192 - 1) 0 5 t +
    bzl m (HP + 8192) (2 ^ 192 - 1) 0 6 t + kron14 m t) % 2 ^ 256

theorem pass3f4_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f4 ret tail m ACC Gas.pass3f4 p3f4Word :=
  sorry

theorem pass3f6_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f6 ret tail m ACC Gas.pass3f6 p3f6Word :=
  sorry

theorem pass3f10_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f10 ret tail m (ACC + 8192) Gas.pass3f10 p3f10Word :=
  sorry

theorem pass3f14_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.pass3f ret tail) (m : ByteArray) :
    FusedPass s Entry.pass3f14 ret tail m (ACC + 8192) Gas.pass3f14 p3f14Word :=
  sorry

end MlDsaOpt87.Proofs
