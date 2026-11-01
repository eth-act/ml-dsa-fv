import MlDsaOpt44.Fn.Sponge.Ginit
import MlDsaOpt44.Fn.Sponge.Cext
import MlDsaOpt44.Fn.Sponge.Absorb
import MlDsaOpt44.Fn.Sponge.Mu0
/-!
# Sponge glue: `spr`, `ginit`, `trabs`, `cext`, `absorb17`, `mu0` (WP4)

All contracts are exact word-level statements; the sponge meaning (spread /
compress are bit permutations, `ginit` builds the padded absorbed states,
`trabs` absorbs `tr`'s input into one slot) lives in pure lemmas
(`Math/Sponge.lean`). The proofs are in `Fn/Sponge/*.lean` (namespace
`WP4`): block lemmas per straight-line path (`Ginit`, `Absorb`, `Trabs`,
`MuBlocks` are generated one block per lane / group), the networks
`sprNet`/`compNet` (`Bits`, `Cext`), and μ's padded block lane by lane
(`MuMath`, `MuVal`, `MuFinal`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **spr**: `[v, ret] ↦ [spread v]`. -/
theorem spr_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr :=
  WP4.spr_call_lane hs hr m hv

/-- **ginit**: `[l4, cmult, amult, keep, ret]`; initialise the kf4 state of a
SIMD group. -/
theorem ginit_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit :=
  WP4.ginit_call_aux hs hr m hk ha hc hl

/-- **trabs**: `[kp, lm, n4, sh, off, ret]`; slot `sh` of the `4 n4` state words
from `kp` absorbs the spread calldata lanes. -/
theorem trabs_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.trabs ret tail) (m : ByteArray) {off sh n4 lm kp : Nat}
    (hoff : off < 2 ^ 64) (hsh : sh < 4) (hn4 : 1 ≤ n4) (hlm : lm < 2 ^ 256)
    (hkp : kp + 128 * n4 ≤ KS + 800) (hkp' : KS ≤ kp) (hkp32 : kp % 32 = 0) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if kp ≤ KS + 32 * x ∧ KS + 32 * x < kp + 128 * n4 then
          word m (KS + 32 * x) ^^^
            spread (trLane s.executionEnv.calldata off lm n4 ((KS + 32 * x - kp) / 32)) * 2 ^ sh
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(kp, kp + 128 * n4)] ∧
      Call s Entry.trabs [wd kp, wd lm, wd n4, wd sh, wd off] ret tail m [] m' (Gas.trabs n4) :=
  WP4.trabs_call_aux hs hr m hoff hsh hn4 hlm hkp hkp' hkp32

/-- **cext**: `[n, sh, dst, ret]`; `dst[x] := lane x of slot sh`, de-interleaved and
un-complemented, `x < n`. -/
theorem cext_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.cext ret tail) (m : ByteArray) {dst sh n : Nat}
    (hsh : sh < 4) (hn : 1 ≤ n) (hn' : n ≤ 25) (hdst : KS + 800 ≤ dst)
    (hdm : dst + 32 * n ≤ TOP) :
    ∃ m', (∀ x, x < n → word m' (dst + 32 * x) =
        cpl x (compress (word m (KS + 32 * x) / 2 ^ sh &&& spread M64))) ∧
      FrameExcept m m' [(dst, dst + 32 * n)] ∧
      Call s Entry.cext [wd n, wd sh, wd dst] ret tail m [] m' (Gas.cext n) :=
  WP4.cext_call_aux hs hr m hsh hn hn' hdst hdm

/-- **absorb17**: `[off, ret]`; `KS[x] ^= rep(LE64(cd[off + 8x …]))`, `x < 17`. -/
theorem absorb17_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.absorb17 ret tail) (m : ByteArray) {off : Nat} (hoff : off < 2 ^ 64) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if x < 17 then word m (KS + 32 * x) ^^^ rep (le64 s.executionEnv.calldata (off + 8 * x))
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(KS, KS + 544)] ∧
      Call s Entry.absorb17 [wd off] ret tail m [] m' Gas.absorb17 :=
  WP4.absorb17_call_aux hs hr m hoff

/-- **mu0**: `[sh, ret]`; for `|M| ≤ 69` slot `sh` absorbs μ's single block
(with `tr` read from `TRL`), otherwise nothing. -/
theorem mu0_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.mu0 ret tail) (m : ByteArray) {sh : Nat} (hsh : sh < 4)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (mlenOf s.executionEnv.calldata ≤ 69 → ∀ tr : ByteArray, tr.size = 64 →
        (∀ x, x < 8 → word m (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (muBlock tr s.executionEnv.calldata) (8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      (69 < mlenOf s.executionEnv.calldata → m' = m) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.mu0 [wd sh] ret tail m [] m' Gas.mu0 :=
  WP4.mu0_call_aux hs hr m hsh hcd

end MlDsaOpt44.Proofs
