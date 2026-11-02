import MlDsaOpt65.Fn.Group.Defs
import MlDsaOpt65.Fn.Ginit.Lanes
import MlDsaOpt65.Budget
/-!
# `ginit`: initialise the kf4 state of a SIMD group (ML-DSA-65)

Entry `[l4, cmult, amult, keep, ret]` (`gen_ginit`). ML-DSA-65's `ginit`
differs from ML-DSA-44's: `RHO1` moved, the c̃ slot absorbs six c̃ lanes
(48 bytes) with its domain byte in lane 6. The stored words are `ginitWord`
(`Fn/Group/Defs.lean`). Straight line, 25 lane blocks (`Fn/Ginit/Lanes.lean`),
exactly `Gas.ginit`.
-/

namespace MlDsaOpt65.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

set_option linter.unusedVariables false in
/-- **ginit**: `[l4, cmult, amult, keep, ret]`; `KS[x] := ginitWord m keep
amult cmult l4 x` for every lane `x < 25`, nothing else written, no results,
gas `Gas.ginit`. Covers every call site: `group` (`keep = 0`, `amult = 15`,
`cmult = 0`) and the mixed groups of the main flow (`keep`, `amult`,
`cmult = 2^cslot` or `0`). Proof: `G1.ginit_reach` (`Fn/Ginit/Lanes.lean`, one block
lemma per lane, generated from the ML-DSA-65 listing, pcs 11987–12083). -/
theorem ginit_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit :=
  G1.ginit_reach hs hr m hk hl

end MlDsaOpt65.Proofs
