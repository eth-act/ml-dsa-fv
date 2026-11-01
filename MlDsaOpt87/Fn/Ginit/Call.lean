import MlDsaOpt87.Fn.Group.Defs
import MlDsaOpt87.Budget
/-!
# `ginit`: initialise the kf4 state of a SIMD group (ML-DSA-87; open)

Entry `[l4, cmult, amult, keep, ret]` (`gen_ginit`). ML-DSA-87's `ginit`
differs from ML-DSA-44's: `RHO1` moved and there is no c̃ rider (no c̃ lanes,
`cmult` is read from the stack but unused). The stored words are `ginitWord`
(`Fn/Group/Defs.lean`). Straight line, 25 lane blocks, exactly `Gas.ginit`.
-/

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

/-- **ginit** (open): `[l4, cmult, amult, keep, ret]`; `KS[x] := ginitWord m keep
amult cmult l4 x` for every lane `x < 25`, nothing else written, no results,
gas `Gas.ginit`. Covers every call site: `group` (`keep = 0`, `amult = 15`,
`cmult = 0`) and the mixed groups of the main flow (`keep`, `amult`,
`cmult = 0`). Proof to do: port `MlDsaOpt44/Fn/Sponge/Ginit.lean`
(one block lemma per lane) against the ML-DSA-87 listing (pcs 12945–13300). -/
theorem ginit_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.ginit ret tail) (m : ByteArray) {keep amult cmult l4 : Nat}
    (hk : keep < 2 ^ 256) (ha : amult < 2 ^ 256) (hc : cmult < 2 ^ 256) (hl : l4 < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) = ginitWord m keep amult cmult l4 x) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.ginit [wd l4, wd cmult, wd amult, wd keep] ret tail m [] m' Gas.ginit := by
  sorry

end MlDsaOpt87.Proofs
