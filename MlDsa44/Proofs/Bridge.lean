import MlDsa44.Proofs.Fn.Row
import MlDsa44.Proofs.Fn.Hint
/-!
# Pure bridges between the spec and the implementation's data flow

No EVM reasoning here. These restate parts of FIPS 202/204 in the shape the
bytecode computes them:

* squeezing whole blocks and truncating is SHAKE;
* reducing coefficients mod `q` before the NTT does not change it;
* `verifyInternal` equals a flat conjunction of independently computed
  checks, where every `⊥` turns its flag false and all values are total
  (`getD` defaults), matching the bytecode's flag accumulation.
-/

namespace MlDsa44.Proofs

open EvmSemantics

theorem squeeze_extract_eq_shake (rate : Nat) (msg : ByteArray) (n blocks : Nat)
    (hrate : rate = 136 ∨ rate = 168) (hn : n ≤ blocks * rate) :
    (Fips202.squeeze rate (Fips202.absorb rate (Fips202.pad rate 0x1F msg)) blocks).extract 0 n =
      Fips202.shake rate msg n := by
  sorry

theorem squeeze_size (rate : Nat) (st : Fips202.SpongeState) (blocks : Nat)
    (hrate : rate = 136 ∨ rate = 168) :
    (Fips202.squeeze rate st blocks).size = blocks * rate := by
  sorry

theorem ntt_mod (f : Fips204.Poly) (hf : f.size = 256) :
    Fips204.ntt (f.map (· % (Fips204.q : Int))) = Fips204.ntt f := by
  sorry

/-- The verification result as the bytecode assembles it: independent
validity flags and a commitment hash over total (defaulted) values. -/
def flatAccepts (pk M' sig : ByteArray) : Bool :=
  let rho := pk.extract 0 32
  let z := (Fips204.sigDecode sig).2.1
  let hint? := Fips204.hintBitUnpack (sig.extract 2336 2420)
  let c? := Fips204.sampleInBall (sig.extract 0 32)
  let okA := (List.range 4).all fun i => (List.range 4).all fun j => (aEntry rho i j).isSome
  let h := hint?.getD (Array.replicate 4 Fips204.zeroPoly)
  let cHat := Fips204.ntt ((c?.getD Fips204.zeroPoly).map (· % (Fips204.q : Int)))
  let zHat := (Array.range 4).map fun i => Fips204.ntt (z[i]!.map (· % (Fips204.q : Int)))
  let rows := (Array.range 4).map fun i =>
    rowApprox ((Array.range 4).map fun j => (aEntry rho i j).getD Fips204.zeroPoly)
      zHat cHat (t1Hat pk i)
  let w1 := (Array.range 4).map fun i =>
    (Array.range 256).map fun j => Fips204.useHint h[i]![j]! rows[i]![j]!
  let mu := Fips204.H (Fips204.H pk 64 ++ M') 64
  Fips204.normBelow z (Fips204.gamma1 - Fips204.beta) && hint?.isSome && c?.isSome && okA &&
    (sig.extract 0 32 == Fips204.H (mu ++ Fips204.w1Encode w1) (Fips204.lambda / 4))

theorem verifyInternal_eq_flat (pk M' sig : ByteArray) (hpk : pk.size = 1312)
    (hsig : sig.size = 2420) :
    Fips204.verifyInternal pk M' sig = flatAccepts pk M' sig := by
  sorry

end MlDsa44.Proofs
