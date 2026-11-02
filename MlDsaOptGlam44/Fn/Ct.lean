import MlDsaOptGlam44.Fn.Ball
import MlDsaOpt44.Fn.Ct.Defs
import MlDsaOptGlam44.Fn.Ct.TBuildRun
import MlDsaOptGlam44.Fn.Ct.Csum4Main
/-!
# Sparse `c · t1` in the normal domain: `tbuild`, `csum` (WP10)

`tbuild [TT, 32, ret]` writes the window table of the four `t1` rows: 768
16-bit fields per row, interleaved by row (field `(e, r)` big-endian at byte
`TT + 6142 − 8e − 2r`): `e < 256` and `e ≥ 512` hold `1023 − t1_r[e mod 256]`,
`256 ≤ e < 512` hold `t1_r[e − 256]`.

`csum [SP, TT, ret]` sums, for every `t`, the window entries
`e = t + 256 − p (+ 256 if c_p = −1)` over the nonzero positions `p` of `c`
(one unaligned `MLOAD` reads 4 coefficients × 4 rows), transposes, and stores
`spOff − (2^13 S'_r(t) + n_neg(t))` per lane (v4: the count is kept replicated
and pre-negated; `spOff = 128 q + γ2 − 1` carries UseHint's rounding term).
Since `2^13 · 1023 = q − 1`, `2^13 S' + n_neg ≡ 2^13 (c · t1_r)(t) (mod q)`
(pure lemma `Math.csum_congr`).
-/

/-! Glamsterdam: `tbuild` is v4's code (ported proof). `csum` keeps all τ window bases on
the stack (`CSUM_DEEP`, DUPN); its contract is v4's (blocks and loop: `Fn/Ct/gen_csum.py`,
the rest v4's `Csum4Main` ported). -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- **tbuild**: `[TT, 32, ret]`. -/
theorem tbuild_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.tbuild ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', TTable m' TT s.executionEnv.calldata ∧
      FrameExcept m m' [(TT, TT + 6144)] ∧
      Call s Entry.tbuild [wd TT, wd 32] ret tail m [] m' Gas.tbuild := by
  unfold TTable tEntry; exact TB.tbuild_main hs hr m hcd

/-- **csum**: `[SP, TT, ret]` (proof: `Fn/Ct/Csum4*.lean`). -/
theorem csum_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray)
    (hb : ∀ i, i < Fips204.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ c : Fips204.Poly, c.size = 256 → (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m TT s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 32 * t) =
          pack4 fun r => spOff - (2 ^ 13 * sPrime c s.executionEnv.calldata r t + nNeg c t)) ∧
      FrameExcept m m' [(SP, SP + 8192)] ∧
      Call s Entry.csum [wd SP, wd TT] ret tail m [] m' Gas.csum :=
  CS4.csum_main hs hr m hb

end MlDsaOptGlam44.Proofs
