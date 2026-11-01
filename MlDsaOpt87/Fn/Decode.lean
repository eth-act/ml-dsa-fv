import MlDsaOpt87.Fn.Decode.Defs
import MlDsaOpt87.Fn.Decode.ZLoop
import MlDsaOpt87.Fn.Decode.ZSpec
import MlDsaOpt87.Fn.Decode.HintMain
/-!
# Signature decoding: `dz` (z with norm flags) and `dhint` (HintBitUnpack), ML-DSA-87

Open contracts (statements only); the proofs mirror `MlDsaOpt44/Fn/Decode.lean` and
`MlDsaOpt44/Fn/Decode/*` (`ZBlocks`, `ZLoop`, `ZMath`, `HintBlocks`, `HintLoop`,
`HintMain`), with the ML-DSA-87 parameters: 20-bit z fields (`G = 3` per 64-bit
gather, `C = 12` per 32-byte load), `k = 8` unrolled hint rows, `ω = 75`.

Call sites (`MlDsaOpt/87/opt.asm`, segment zh): `dz [ZH, Z0]`, `dz [ZH2, Z0 + 2560]`
(`ZH2 = ZH + 0x2000`, i.e. `g = 0, 1` below), `dhint []`.
-/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

/-- **dz**: `[ZH + 0x2000 g, Z0 + 2560 g, ret] ↦ [f]`, `g < 2`. Decodes the four
20-bit packed polynomials `4g … 4g + 3` of the z stream (for `g = 1` lanes 0–2 are
`z_4, z_5, z_6`; lane 3 holds `zLane` of the bytes behind `z_6` (hint bytes, message, zero
past the end of the calldata)) into lane-packed words, `lane j of ZH_g[t] = γ1 + q − raw = zLane`, and
returns the OR of the SIMD flag words: the lane-`j` flag bits `zFlagBit j` of `f` are
clear iff every field of polynomial `4g + j` is in `(β, 2γ1 − β)`.
Mirror `MlDsaOpt44/Fn/Decode/ZLoop.lean` (`DecodeZ.dz_main`), generic in the base. -/
theorem dz_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dz ret tail) (m : ByteArray) {g : Nat} (hg : g < 2) :
    ∃ m', ∃ f, f < 2 ^ 256 ∧
      (∀ j, j < 4 → ((f &&& zFlagBit j = 0) ↔ zNormOk s.executionEnv.calldata (4 * g + j))) ∧
      (∀ t, t < 256 → word m' (ZH + 0x2000 * g + 32 * t) =
        pack4 fun j => zLane s.executionEnv.calldata (4 * g + j) t) ∧
      FrameExcept m m' [(ZH + 0x2000 * g, ZH + 0x2000 * g + 8192)] ∧
      Call s Entry.dz [wd (ZH + 0x2000 * g), wd (Z0 + 2560 * g)] ret tail m [wd f] m' Gas.dz :=
  DecodeZ.dz_main hs hr m hg

/-- Pure (open): the norm check of `z ∈ R^ℓ` is the conjunction of the per-polynomial
field checks of the first `ℓ = 7` polynomials of the stream. Together with `dz_call`
this gives the segment-zh flag `(f₀ ||| (f₁ &&& (2^192 − 1))) &&& zBits = 0 ↔ okZ`.
Proof: unfold `sigDecode`/`bitUnpack` (`bitlen (2γ1 − 1) = 20`), `extract_extract`
(`CTOFF + 64 + 640 k = Z0 + 640 k ≤ HDR`), `|γ1 − raw| < γ1 − β ↔ β < raw < 2γ1 − β`. -/
theorem okZ_iff_zNormOk (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    okZ cd = true ↔ ∀ k, k < P.l → zNormOk cd k :=
  DecodeZ.okZ_iff_zNormOk cd hcd

/-- **dhint**: `[ret] ↦ [okH]`, `HP` (two row groups, `HP + 0x2000 g`) initially zero.
FIPS 204 Algorithm 21 on the hint bytes; row `r < 8` ORs bit `64 (r % 4)` into
`HP + 0x2000 (r / 4) + 32 y` for every index `y` of the row. Every `HP` word is four bit
lanes; if the hint decodes, lane `r % 4` of row group `r / 4` is `h[r][t]`.
Mirror `MlDsaOpt44/Fn/Decode/HintMain.lean` (`DecodeH.dhint_main`) with eight rows. -/
theorem dhint_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.dhint ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (hz : ZeroOn m HP (HP + 0x4000)) :
    ∃ m', (∀ g, g < 2 → ∀ t, t < 256 → ∃ b : Nat → Nat, (∀ r, r < 4 → b r ≤ 1) ∧
        word m' (HP + 0x2000 * g + 32 * t) = pack4 b) ∧
      (∀ h, hintOf s.executionEnv.calldata = some h → ∀ r, r < 8 → ∀ t, t < 256 →
        lane (word m' (HP + 0x2000 * (r / 4) + 32 * t)) (r % 4) = (h[r]![t]!).toNat) ∧
      FrameExcept m m' [(HP, HP + 0x4000)] ∧
      Call s Entry.dhint [] ret tail m [flag (okH s.executionEnv.calldata)] m' Gas.dhint :=
  -- `hcd` is not needed: the hint bytes are read through `extract` (zeros past the end)
  (fun _ => DecodeH.dhint_main hs hr m hz) hcd

end MlDsaOpt87.Proofs
