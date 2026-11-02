import MlDsaOpt65.Fn.Csum.Main
import MlDsaOpt65.Budget
/-!
# Sparse `c · t1` in the normal domain: `csum` (ML-DSA-65)

Proved in `Fn/Csum/*` (v4). `csum [sp, tt, ret]` sums, for every `t`, the window
entries `e = t + 256 − p (+ 256 if c_p = −1)` of the table at `tt` over the `τ = 49`
nonzero positions `p` of `c` (one unaligned `MLOAD` at `BASES[i] + tt − 32 u` reads
4 coefficients × 4 rows), transposes, and stores `spOff − (2^13 S'_r(t) + n_neg(t))` per lane at `sp` (the
running count is kept replicated and pre-negated). Since `2^13 · 1023 = q − 1`,
`2^13 S'_r(t) + n_neg(t) ≡ 2^13 (c · t1_r)(t) (mod q)`.

Call sites (`MlDsaOpt/65/opt.asm`, segment ct): `csum [SP, TT]` (rows 0–3, table built by
`tbuild [TT, 32]`) and `csum [SP + 0x2000, TT + 0x1800]` (rows 4–7, `tbuild [TT + 0x1800,
0x520]`), i.e. `g = 0, 1` below. The proof (`G4.csum_main`, `Fn/Csum/Main.lean`) mirrors
`MlDsaOpt44/Fn/Ct/Csum4*.lean` with 49 unrolled loads (the first 11 window bases on the
stack) and the pointers as parameters.
-/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **csum**: `[SP + 0x2000 g, TT + 0x1800 g, ret]`, `g < 2`. For every `c ∈ {0, ±1}^256`
represented by `sib` (`CRep`) and every t1 offset `off` of the table at `TT + 0x1800 g`,
lane `r` of `SP_g[t]` is `spOff − (2^13 S'_r(t) + n_neg(t))` (v4). -/
theorem csum_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.csum ret tail) (m : ByteArray) {g : Nat} (hg : g < 2)
    (hb : ∀ i, i < P.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ (off : Nat) (c : Fips204.Poly), c.size = 256 →
        (∀ t, t < 256 → c[t]! = 0 ∨ c[t]! = 1 ∨ c[t]! = -1) →
        CRep m c → TTable m (TT + 0x1800 * g) off s.executionEnv.calldata →
        ∀ t, t < 256 → word m' (SP + 0x2000 * g + 32 * t) =
          pack4 fun r => spOff - (2 ^ 13 * sPrime c s.executionEnv.calldata off r t + nNeg c t)) ∧
      FrameExcept m m' [(SP + 0x2000 * g, SP + 0x2000 * g + 8192)] ∧
      Call s Entry.csum [wd (SP + 0x2000 * g), wd (TT + 0x1800 * g)] ret tail m [] m' Gas.csum :=
  G4.csum_main hs hr m hg hb

end MlDsaOpt65.Proofs
