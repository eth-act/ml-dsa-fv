import MlDsaOpt65.Fn.Sponge.Spr
import MlDsaOpt65.Fn.Sponge.Trabs
import MlDsaOpt65.Fn.Sponge.Cext
import MlDsaOpt65.Fn.Sponge.Absorb
set_option warningAsError true
/-!
# Sponge glue shared with ML-DSA-44: `spr`, `trabs`, `cext`, `absorb17` (ML-DSA-65)

The code of these four subroutines is the ML-DSA-44 code up to absolute jump
targets, and the statements are the ML-DSA-44 ones (with this artifact's
`Entry`, `Gas`, `TOP`). The proofs are the 44 proofs ported to this artifact
by `scripts/proofgen_port.py 65` (`Fn/Sponge/{Spr,Trabs,Cext,Absorb}.lean`;
the pure lemmas are the 44 modules `Fn/Sponge/{Bits,Lanes,Fold,Mem,Defs}`).
`ginit` and `mu0` differ from 44 and live in their own files.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs (trLane)

/-- **spr**: `[v, ret] ↦ [spread v]`. -/
theorem spr_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.spr ret tail) (m : ByteArray) {v : Nat} (hv : v < 2 ^ 64) :
    Call s Entry.spr [wd v] ret tail m [wd (spread v)] m Gas.spr :=
  WP4.spr_call_lane hs hr m hv

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

end MlDsaOpt65.Proofs
