import MlDsaOptGlam44.Fn.Sponge.Ginit
import MlDsaOptGlam44.Fn.Sponge.Cext
import MlDsaOptGlam44.Fn.Sponge.Absorb
import MlDsaOptGlam44.Fn.Sponge.Spr
import MlDsaOptGlam44.Fn.Sponge.TrabsRun
import MlDsaOptGlam44.Fn.Sponge.Kmove
import MlDsaOptGlam44.Fn.Sponge.Lmerge
import MlDsaOptGlam44.Fn.Sponge.Mub0
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
/- Ported from `MlDsaOpt44/Fn/Sponge.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/-!
# Sponge glue: `spr`, `ginit`, `trabs`, `cext`, `absorb17`, `mub0`, `kmove`, `lmerge` (WP4)

All contracts are exact word-level statements; the sponge meaning (spread /
compress are bit permutations, `ginit` builds the padded absorbed states,
`trabs` absorbs `tr`'s input into one slot) lives in pure lemmas
(`Math/Sponge.lean`). The proofs are in `Fn/Sponge/*.lean` (namespace
`WP4`): block lemmas per straight-line path (`Ginit`, `Absorb`, `Trabs`,
`MuBlocks` are generated one block per lane / group), the networks
`sprNet`/`compNet` (`Bits`, `Cext`), and μ's padded block lane by lane
(`MuMath`, `MuVal`, `MuFinal`).
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

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
from `kp` absorbs the spread calldata lanes. v4 masks the calldata word before
the byte swap, so `lm` must be lane-aligned (`hlmL`; proof in `Fn/Sponge/TrabsRun.lean`). -/
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

/-- μ's first SHAKE256 block in a SIMD slot: `tr ‖ 0 ‖ 0 ‖ M`, padded when it
is the only one (`|M| ≤ 69`). -/
def mu0Bytes (tr : ByteArray) (cd : ByteArray) : ByteArray :=
  if mlenOf cd ≤ 69 then muBlock tr cd else tr ++ (ByteArray.mk #[0, 0] ++ msgOf cd)

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

/-- **kmove**: `[keep, msk, sr, sl, src, ret]`; for every lane `x < 25`,
`KS[x] := (((src[x] << sl) >> sr) & msk) | (KS[x] & keep)` (moves states
between slots, or restores them from a saved image; `src` may be `KS`). -/
theorem kmove_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (m : ByteArray) {src sl sr msk keep : Nat}
    (hsrc : src = KS ∨ KS + 800 ≤ src) (hsrc' : src + 800 ≤ TOP) (hsl : sl < 256) (hsr : sr < 256)
    (hmsk : msk < 2 ^ 256) (hkeep : keep < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        (word m (src + 32 * x) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (KS + 32 * x) &&& keep)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.kmove [wd keep, wd msk, wd sr, wd sl, wd src] ret tail m [] m' Gas.kmove :=
  WP4.kmove_call_aux hs hr m hsrc hsrc' hsl hsr hmsk hkeep

/-- **lmerge**: `[a, a + 32 n, sl, b − a, ma, dst − a, ret]` (offsets mod
`2^256`), `n = 11 k`; for `w < n`, `dst[w] := the lanes `ma` of `a[w]`, the
others of `b[w] << sl`. -/
theorem lmerge_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (m : ByteArray) {dst a b ma sl k : Nat}
    (hk : 1 ≤ k) (hdst : dst + 352 * k ≤ TOP) (ha : a + 352 * k ≤ TOP) (hb : b + 352 * k ≤ TOP)
    (hda : dst = a ∨ dst + 352 * k ≤ a ∨ a + 352 * k ≤ dst)
    (hdb : dst + 352 * k ≤ b ∨ b + 352 * k ≤ dst) (hma : ma < 2 ^ 256) (hsl : sl < 256) :
    ∃ m', (∀ w, w < 11 * k → word m' (dst + 32 * w) =
        let b' := word m (b + 32 * w) * 2 ^ sl % 2 ^ 256
        b' ^^^ ((word m (a + 32 * w) ^^^ b') &&& ma)) ∧
      FrameExcept m m' [(dst, dst + 352 * k)] ∧
      Call s Entry.lmerge [wd a, wd (a + 352 * k), wd sl, wd ((b + 2 ^ 256 - a) % 2 ^ 256), wd ma,
        wd ((dst + 2 ^ 256 - a) % 2 ^ 256)] ret tail m [] m' (Gas.lmerge k) :=
  WP4.lmerge_call_aux hs hr m hk hdst ha hb hda hdb hma hsl

end MlDsaOptGlam44.Proofs
