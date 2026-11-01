import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
/-!
# `sib`: SampleInBall from the squeezed stream in `CB` (WP9)

`sib [ret] ↦ [ok]` scans bytes `8 … 271` of the 272-byte stream (34 lanes in
`CB`, squeezed by `cext` from a SIMD slot) as FIPS 204 Algorithm 29 with the
Appendix C limit. Instead of the coefficient array it keeps:

* `CW[t]`: a code word per position (`0`; `1` for `c_t = −1`; `2^256 − 1`
  for `c_t = +1`), read by `csum` as the running `n_neg` correction;
* `BASES[i]`, `i < τ`: the window base `4064 + 8 p − 2048 [c_p = −1]` of
  every nonzero position `p` (moved when SampleInBall moves a coefficient);
* `IDX` (one byte per position: slot + 1 in `BASES`), `NNEG`, `CNT`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- `CW` code of a coefficient of `c`. -/
def codeOf (v : Int) : Nat := if v = 0 then 0 else if v = -1 then 1 else 2 ^ 256 - 1

/-- Window base of a nonzero coefficient at `p`. -/
def baseOf (c : Fips204.Poly) (p : Nat) : Nat := 4064 + 8 * p - if c[p]! = -1 then 2048 else 0

/-- Number of `−1` coefficients. -/
def negCount (c : Fips204.Poly) : Nat := ((List.range 256).filter fun p => c[p]! = -1).length

/-- `c` as `sib` leaves it in memory. -/
def CRep (m : ByteArray) (c : Fips204.Poly) : Prop :=
  (∀ t, t < 256 → word m (CW + 32 * t) = codeOf c[t]!) ∧
  word m NNEG = negCount c ∧
  ∃ ps : List Nat, ps.length = Fips204.tau ∧ ps.Nodup ∧
    (∀ p, p ∈ ps ↔ p < 256 ∧ c[p]! ≠ 0) ∧
    ∀ i, i < Fips204.tau → word m (BASES + 32 * i) = baseOf c ps[i]!

/-- `sib`'s scratch regions start zeroed. -/
def SibFresh (m : ByteArray) : Prop :=
  ZeroOn m CW (CW + 8192) ∧ ZeroOn m IDX (IDX + 256) ∧ ZeroOn m NNEG (NNEG + 64)

theorem sib_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x)) (hz : SibFresh m) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      FrameExcept m m' [(CW, CW + 8192), (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib := by
  sorry

end MlDsaOpt44.Proofs
