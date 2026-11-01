import MlDsaOpt44.Layout
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
/-!
# Definitions for the `ntt` / `intt` proofs (WP7)

* the coefficient field `F = ZMod q` and index-wise models of one forward
  (Cooley–Tukey) and one inverse (Gentleman–Sande) layer, `fwdL`/`invL`;
* the word-level expressions the symbolic execution produces: `montU` (lane-wise
  Montgomery reduction of a stack word), the butterfly outputs `ctA`/`ctB`
  (forward), `gsA`/`gsB`/`gsAs` (inverse), `montE` (Montgomery reduction of a
  loaded word, `premont`), and the store `wrU`;
* `LOK x B g`: the four lanes of the stack word `x` are below `B` and congruent
  to `g k`; `PassInv`: the same for the 256 words of a polynomial in memory.
-/

namespace MlDsaOpt44.Proofs.NttW

open EvmSemantics MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs

abbrev F := ZMod 8380417

/-- `ζ^{brv8 m}` in `F`. -/
def ζ (m : Nat) : F := ((Fips204.zetas m : ℤ) : F)

/-- The Montgomery radix `2^32` and its inverse in `F`. -/
def R : F := 4294967296
def Rinv : F := 8265825

/-- Scale of the last inverse layer: `256⁻¹ · 2^32`. -/
def Sc : F := 8347681 * R

/-! ## Layer models -/

/-- One layer of Algorithm 41 with block length `len`, index-wise. -/
def fwdLayer (len : Nat) (h : Nat → F) (i : Nat) : F :=
  if i % (2 * len) < len then h i + ζ (128 / len + i / (2 * len)) * h (i + len)
  else h (i - len) - ζ (128 / len + i / (2 * len)) * h i

/-- The first `L` layers of Algorithm 41. -/
def fwdL (h : Nat → F) : Nat → Nat → F
  | 0 => h
  | L + 1 => fwdLayer (128 / 2 ^ L) (fwdL h L)

/-- One layer of Algorithm 42 with block length `len` and `m = m0` before. -/
def invLayer (len m0 : Nat) (h : Nat → F) (i : Nat) : F :=
  if i % (2 * len) < len then h i + h (i + len)
  else ζ (m0 - i / (2 * len) - 1) * (h i - h (i - len))

/-- The first `L` layers of Algorithm 42 (without the final scaling). -/
def invL (h : Nat → F) : Nat → Nat → F
  | 0 => h
  | L + 1 => invLayer (2 ^ L) (2 ^ (8 - L)) (invL h L)

/-- Inputs scaled by `2^-32` (the `premont` load). -/
def scaleR (h : Nat → Nat → F) (k t : Nat) : F := h k t * Rinv

/-! ## Bounds -/

/-- Forward lane bound after `L` layers. -/
def Bf (L : Nat) : Nat := 2 ^ 25 + 2 * 8380417 * L

/-- Montgomery output bound `2^26 + q`, and the inverse bound before layer `L`. -/
def Bu : Nat := 2 ^ 26 + 8380417
def Bi (L : Nat) : Nat := 2 ^ L * Bu

/-! ## Words produced by the symbolic execution -/

/-- Lane-wise Montgomery reduction of a stack word (`mont` in `opt_ntt.py`). -/
def montU (t : UInt256) : UInt256 :=
  (UInt256.ofNat 8380417 *
        UInt256.land (UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855)
          (UInt256.ofNat 4236238847 *
            UInt256.land (UInt256.ofNat 26959946660873538060741835960174461801791452538186943042387869433855) t) +
      t).shiftRight (UInt256.ofNat 32)

/-- `montU` on a loaded word, in the `Nat` form `opt44_block` produces. -/
def montE (t : Nat) : Nat :=
  (8380417 * (26959946660873538060741835960174461801791452538186943042387869433855 &&&
      4236238847 * (26959946660873538060741835960174461801791452538186943042387869433855 &&& t)) + t) %
    2 ^ 256 / 2 ^ 32

/-- Forward butterfly: `a + mont(b z)` and `(C + a) − mont(b z)`. -/
def ctA (xa xb z : UInt256) : UInt256 := montU (z * xb) + xa
def ctB (C xa xb z : UInt256) : UInt256 := C + xa - montU (z * xb)

/-- Inverse butterfly: `a + b` and `mont(z ((C + b) − a))`; `gsAs` is the
scaled sum of the last layer. -/
def gsA (xa xb : UInt256) : UInt256 := xb + xa
def gsB (C xa xb z : UInt256) : UInt256 := montU (z * (C + xb - xa))
def gsAs (f xa xb : UInt256) : UInt256 := montU (f * (xb + xa))

/-- `MSTORE` of a stack word. -/
def wrU (m : ByteArray) (a : Nat) (v : UInt256) : ByteArray :=
  MachineState.writeBytes m (Data.Bytes.natToBytesPadded v.toNat 32) a

/-! ## Lane invariants -/

/-- The lanes of `x` are below `B` and congruent to `g k`. -/
def LOK (x : UInt256) (B : Nat) (g : Nat → F) : Prop :=
  ∀ k, k < 4 → lane x.toNat k < B ∧ ((lane x.toNat k : Nat) : F) = g k

/-- Pass invariant: word `t` of the polynomial at `P` satisfies `LOK` with the
`Post` model and bound if `D t` (already processed), else with `Pre`. -/
def PassInv (M : ByteArray) (P : Nat) (D : Nat → Prop) [DecidablePred D] (Bin Bout : Nat)
    (Pre Post : Nat → Nat → F) : Prop :=
  ∀ t, t < 256 → LOK (UInt256.ofNat (word M (P + 32 * t))) (if D t then Bout else Bin)
    (fun k => if D t then Post k t else Pre k t)

end MlDsaOpt44.Proofs.NttW
