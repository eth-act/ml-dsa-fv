import MlDsaOpt44.Fn.Ntt.Step
import MlDsaOpt44.Fn.Hint.Lanes
import MlDsaOpt44.Math.NttV4
/-!
# Definitions for the v4 `ntt` / `intt` proofs (WP G, H)

The v3 development (`Fn/Ntt/{Defs,Sem,Step,Model}`: `F`, `montU`, `LOK`, the
layer models `fwdL`/`invL`, `gsA`/`gsAs`, the zeta records) is reused; this
file adds the word expressions of the v4 code (`scripts/opt_ntt.py` with
`biased`, `gen_opt.py` `uh_word`), in the shape `opt44_block` produces:

* forward: Shoup's product `shU zs zt b` (pass A), the butterfly outputs
  `ftA xa u = u + a` and `ftB xa u = a − u` (no `+2q`: the inputs carry `8q`);
* inverse: `gsB4 C xa xb z = mont(z ((C − a) + b))` (no swap);
* the fused UseHint word `uh4W x s h` (`x` the output word, `s` the `SP` word,
  `h` the `HP` word);
* `LI x L g`: the lanes of `x` lie in the forward interval of layer `L` and are
  congruent to `g k`; `PI`: a per-word pass invariant with arbitrary
  predicates; `UHP`: the lanes of a stored word are the fused UseHint of a
  coefficient congruent to the model.
-/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW MlDsaOpt44.Proofs.NttV4

/-! ## Words produced by the symbolic execution -/

/-- Shoup product `zt · b − q · (M32 & ((zs · b) >> 32))`. -/
def shU (zs zt : Nat) (b : UInt256) : UInt256 :=
  UInt256.ofNat zt * b - UInt256.ofNat 8380417 *
    UInt256.land (UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855)
      (UInt256.shiftRight (UInt256.ofNat zs * b) (UInt256.ofNat 32))

/-- Forward butterfly outputs: `a' = u + a`, `b' = a − u`. -/
def ftA (xa u : UInt256) : UInt256 := u + xa
def ftB (xa u : UInt256) : UInt256 := xa - u

/-- Inverse `b' = mont(z ((C − a) + b))`. -/
def gsB4 (C xa xb z : UInt256) : UInt256 := montU (z * ((C - xa) + xb))

/-! ### The fused UseHint word (`uh_word`) -/

/-- `x = SP + W`. -/
def uX (x : UInt256) (s : Nat) : UInt256 := UInt256.ofNat s + x
/-- `⌊x / q⌋` (9 bits per lane). -/
def uQ (x : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 3207598986782593870493972684755717093467514342740420773020159)
    (UInt256.shiftRight (UInt256.ofNat 1074791297 * x) (UInt256.ofNat 53))
/-- `y = x − ⌊x / q⌋`. -/
def uY (x : UInt256) : UInt256 := x - uQ x
/-- `D' = (y · 738919105) >> 46`, not masked. -/
def uD (y : UInt256) : UInt256 := UInt256.shiftRight (UInt256.ofNat 738919105 * y) (UInt256.ofNat 46)
/-- `v = ((D' >> 1) & M14) + ((m − h) + 2 (h & D'))`. -/
def uV (d : UInt256) (h : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat 102837757730839990959496584137676933742227568448368519617200127)
      (UInt256.shiftRight d (UInt256.ofNat 1)) +
    ((UInt256.ofNat 276192476357013953623747158765658614701703779022658540142636 - UInt256.ofNat h) +
      (UInt256.land (UInt256.ofNat h) d + UInt256.land (UInt256.ofNat h) d))
/-- `v mod 44 = v − 44 (((v · 2979) >> 17) & M10)`. -/
def uF (v : UInt256) : UInt256 :=
  v - UInt256.ofNat 44 *
    UInt256.land (UInt256.ofNat 6421475075300574421752121441301562791814612862276811058316287)
      (UInt256.shiftRight (UInt256.ofNat 2979 * v) (UInt256.ofNat 17))

/-- The word `uh_word` stores for the inverse NTT output `x`, `SP` word `s`, `HP` word `h`. -/
def uh4W (x : UInt256) (s h : Nat) : UInt256 := uF (uV (uD (uY (uX x s))) h)

/-! ## Invariants -/

/-- Forward lane invariant after `L` layers: lanes in `[lo4 L, hi4 L]`, congruent to `g k`. -/
def LI (x : UInt256) (L : Nat) (g : Nat → F) : Prop :=
  ∀ k, k < 4 → lo4 L ≤ lane x.toNat k ∧ lane x.toNat k ≤ hi4 L ∧ ((lane x.toNat k : Nat) : F) = g k

/-- Pass invariant: word `t` of the polynomial at `P` satisfies `Post t` if `D t`
(already processed), else `Pre t`. -/
def PI (M : ByteArray) (P : Nat) (D : Nat → Prop) [DecidablePred D] (Pre Post : Nat → Nat → Prop) : Prop :=
  ∀ t, t < 256 → if D t then Post t (word M (P + 32 * t)) else Pre t (word M (P + 32 * t))

/-- The stored word `w` at coefficient `t`: lane `r` is the fused UseHint of a value
`W < 2^26 + q` congruent to `g r`, against the `SP` and `HP` words of `m0`. -/
def UHP (m0 : ByteArray) (t w : Nat) (g : Nat → F) : Prop :=
  ∀ r, r < 4 → ∃ W, W < Bu ∧ ((W : Nat) : F) = g r ∧
    lane w r = uh4L (lane (word m0 (SP + 32 * t)) r + W) (lane (word m0 (HP + 32 * t)) r)

/-- Shoup constants for `ζ_m`: `zs = ⌊zt 2^32 / q⌋`, `zt = ζ_m`. -/
structure ShoupOK (zs zt m : Nat) : Prop where
  lo : zs * 8380417 ≤ zt * 2 ^ 32
  hi : zt * 2 ^ 32 < zs * 8380417 + 8380417
  zs_lt : zs < 2 ^ 32
  zt_lt : zt < 2 ^ 23
  cast : ((zt : Nat) : F) = ζ m

end MlDsaOpt44.Proofs.Ntt4
