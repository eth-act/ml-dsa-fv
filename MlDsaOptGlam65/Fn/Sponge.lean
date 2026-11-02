import MlDsaOptGlam65.Fn.Sponge.Spr
import MlDsaOptGlam65.Fn.Sponge.Cext
import MlDsaOptGlam65.Fn.Sponge.Absorb
import MlDsaOptGlam65.Fn.Sponge.TrabsRun
import MlDsaOptGlam65.Fn.Sponge.Mub0
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Sponge.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# Sponge glue shared with ML-DSA-44: `spr`, `trabs`, `cext`, `absorb17` (ML-DSA-65)

The code of these four subroutines is the ML-DSA-44 code up to absolute jump
targets, and the statements are the ML-DSA-44 ones (with this artifact's
`Entry`, `Gas`, `TOP`). The proofs are the 44 proofs ported to this artifact
by `scripts/proofgen_port.py 65` (`Fn/Sponge/{Spr,Trabs,Cext,Absorb}.lean`;
the pure lemmas are the 44 modules `Fn/Sponge/{Bits,Lanes,Fold,Mem,Defs}`).
`ginit` lives in `Fn/Ginit`. v4: `trabs` is a new delta-swap network
(`Fn/Sponge/TrabsRun.lean`, ported from 44; lane-aligned mask hypothesis `hlmL`).
-/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

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
    (hlmL : ∀ k, k < 4 → lane lm k = 0 ∨ lane lm k = M64)
    (hkp : kp + 128 * n4 ≤ KS + 800) (hkp' : KS ≤ kp) (hkp32 : kp % 32 = 0) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        if kp ≤ KS + 32 * x ∧ KS + 32 * x < kp + 128 * n4 then
          word m (KS + 32 * x) ^^^
            spread (trLane s.executionEnv.calldata off lm n4 ((KS + 32 * x - kp) / 32)) * 2 ^ sh
        else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(kp, kp + 128 * n4)] ∧
      Call s Entry.trabs [wd kp, wd lm, wd n4, wd sh, wd off] ret tail m [] m' (Gas.trabs n4) :=
  WP4.trabs_call_v4 hs hr m hoff hsh hn4 hlm hlmL hkp hkp' hkp32

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

/-- μ's sponge input `tr ‖ 0 ‖ 0 ‖ M` (unpadded and padded). -/
def muIn (tr cd : ByteArray) : ByteArray := tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)
def muPadded (tr cd : ByteArray) : ByteArray := Fips202.pad 136 0x1F (muIn tr cd)

/-- μ's first SHAKE256 block in a SIMD slot, padded when it is the only one. -/
def mu0Bytes (tr : ByteArray) (cd : ByteArray) : ByteArray :=
  if mlenOf cd ≤ 69 then muPadded tr cd else muIn tr cd

/-- **mub0**: `[sh, rs, rl]`; slot `sh` absorbs μ's block 0 (with `tr` read
from `TRL`), padded for `|M| ≤ 69`; then returns to `rs` with `[rl]` left on
the stack (`|M| ≤ 69`) or to `rl`. -/
theorem mub0_call {s : State} (hs : Ctx s) {rl rs : Nat} {tail : List UInt256}
    (hrl : RetOK Stack.mub0 rl tail) (hrs : RetOK Stack.mub0 rs (wd rl :: tail)) (m : ByteArray)
    {sh : Nat} (hsh : sh < 4) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ tr : ByteArray, tr.size = 64 → (∀ x, x < 8 → word m (TRL + 32 * x) = le64 tr (8 * x)) →
        ∀ x, x < 25 → word m' (KS + 32 * x) =
          if x < 17 then word m (KS + 32 * x) ^^^
            spread (le64 (mu0Bytes tr s.executionEnv.calldata) (8 * x)) * 2 ^ sh
          else word m (KS + 32 * x)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Reach (callState s Entry.mub0 (wd sh :: wd rs :: wd rl :: tail) m)
        (if mlenOf s.executionEnv.calldata ≤ 69 then callState s rs (wd rl :: tail) m'
          else callState s rl tail m') Gas.mub0 :=
  WP4.mub0_call_aux hs hrl hrs m hsh hcd trabs_call

-- glam: no `mub` (unreachable in the 42-call schedule)

end MlDsaOptGlam65.Proofs
