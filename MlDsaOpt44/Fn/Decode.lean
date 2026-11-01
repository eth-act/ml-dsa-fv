import MlDsaOpt44.Layout
import MlDsaOpt44.Budget
import MlDsaOpt44.Fn.Decode.ZLoop
import MlDsaOpt44.Fn.Decode.HintMain
/-!
# Signature decoding: `dz` (z with norm flags) and `dhint` (HintBitUnpack) (WP8)

* `dz [ZH, Z0, ret] ↦ [f]`: decodes the four 18-bit packed z polynomials into
  lane-packed words (`lane k of ZH[t] = γ1 + q − raw = zLane`) and returns the
  OR of the SIMD norm-flag words; bits `50 + 64k` and `25 + 64k` of `f` stay
  clear iff `‖z‖∞ < γ1 − β`.
* `dhint [ret] ↦ [ok]`: FIPS 204 Algorithm 21 on the hint bytes; ORs bit
  `64 i` into `HP[y]` for every index `y` of row `i`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

/-- The norm-flag bits checked by `flag_check`. -/
def zBits : Nat := pack4 fun _ => 2 ^ 50 + 2 ^ 25

/-- **dz**: `[ZH, Z0, ret] ↦ [f]`. -/
theorem dz_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dz ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', ∃ f, f < 2 ^ 256 ∧ ((f &&& zBits = 0) ↔ okZ s.executionEnv.calldata = true) ∧
      (∀ t, t < 256 → word m' (ZH + 32 * t) = pack4 fun k => zLane s.executionEnv.calldata k t) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.dz [wd ZH, wd Z0] ret tail m [wd f] m' Gas.dz :=
  DecodeZ.dz_main hs hr m hcd

/-- **dhint**: `[ret] ↦ [ok]`, `HP` initially zero. Every `HP` word is four
bit lanes; if the hint decodes, lane `r` of `HP[t]` is `h[r][t]`. -/
theorem dhint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dhint ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hz : ZeroOn m HP (HP + 8192)) :
    ∃ m', (∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧ word m' (HP + 32 * t) = pack4 b) ∧
      (∀ h, hintOf s.executionEnv.calldata = some h →
        ∀ t, t < 256 → ∀ r, r < 4 → lane (word m' (HP + 32 * t)) r = (h[r]![t]!).toNat) ∧
      FrameExcept m m' [(HP, HP + 8192)] ∧
      Call s Entry.dhint [] ret tail m [flag (okH s.executionEnv.calldata)] m' Gas.dhint :=
  DecodeH.dhint_main hs hr m hcd hz

end MlDsaOpt44.Proofs
