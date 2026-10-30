import MlDsa44.Proofs.Fn.Row
import MlDsa44.Proofs.Fn.Hint
import MlDsa44.Proofs.Math.Sponge
import MlDsa44.Proofs.Math.NttMod
import MlDsa44.Proofs.Math.Verify
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
      Fips202.shake rate msg n :=
  Math.squeeze_extract_shake rate msg n blocks hrate hn

theorem squeeze_size (rate : Nat) (st : Fips202.SpongeState) (blocks : Nat)
    (hrate : rate = 136 ∨ rate = 168) :
    (Fips202.squeeze rate st blocks).size = blocks * rate :=
  Math.squeeze_size_of_rate rate st blocks hrate

theorem ntt_mod (f : Fips204.Poly) (hf : f.size = 256) :
    Fips204.ntt (f.map (· % (Fips204.q : Int))) = Fips204.ntt f :=
  Math.ntt_map_emod f hf

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

set_option linter.unusedVariables false in
theorem verifyInternal_eq_flat (pk M' sig : ByteArray) (hpk : pk.size = 1312)
    (hsig : sig.size = 2420) :
    Fips204.verifyInternal pk M' sig = flatAccepts pk M' sig := by
  have hb : Fips204.bitlen (Fips204.gamma1 - 1) = 17 := by decide
  unfold Fips204.verifyInternal flatAccepts
  split
  rename_i rho t1 hp
  split
  rename_i cT z hint? hs
  have hrho : rho = pk.extract 0 32 := by
    have := congrArg Prod.fst hp
    exact this.symm
  have hct : cT = sig.extract 0 32 := by
    have := congrArg Prod.fst hs
    exact this.symm
  have hhint : hint? = Fips204.hintBitUnpack (sig.extract 2336 2420) := by
    have := congrArg (fun x => x.2.2) hs
    simp only at this
    rw [← this]
    simp [Fips204.sigDecode, hb, Fips204.lambda, Fips204.l, Fips204.omega, Fips204.k]
  have hz : (Fips204.sigDecode sig).2.1 = z := by rw [hs]
  have ht1 : (Fips204.pkDecode pk).2 = t1 := by rw [hp]
  rw [hz]
  subst hrho hct hhint
  -- Split the `match` before any zeta/dsimp step: reducing the `let`s under the
  -- matcher makes the kernel unfold it and the declaration check takes ~100 s.
  split
  · rename_i h A c hH hA hC
    rw [Math.expandA_eq] at hA
    by_cases hok : ((List.range 4).all fun r => (List.range 4).all fun s =>
        (Fips204.rejNTTPoly (pk.extract 0 32 ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
    · rw [if_pos hok] at hA
      cases hA
      simp only [aEntry, hH, hC, hok, Option.isSome_some, Option.getD_some, Bool.and_true]
      have hcs : c.size = 256 := Math.sampleInBallOf_size _ _ hC
      have hzdef : z = (Array.range 4).map fun i =>
          Fips204.bitUnpack (sig.extract (32 + 576 * i) (32 + 576 * (i + 1)))
            (Fips204.gamma1 - 1) Fips204.gamma1 := by
        rw [← hz]
        simp [Fips204.sigDecode, hb, Fips204.lambda, Fips204.l]
      have hzHat : (Array.range 4).map (fun i => Fips204.ntt (z[i]!.map (· % (Fips204.q : Int)))) =
          z.map Fips204.ntt := by
        apply Array.ext (by simp [hzdef])
        intro i h1 _
        simp only [Array.size_map, Array.size_range] at h1
        simp only [Array.getElem_map, Array.getElem_range]
        rw [Math.ntt_map_emod]
        · simp [hzdef, getElem!_pos, h1]
        · simp [hzdef, getElem!_pos, h1, Fips204.bitUnpack]
      have ht1s : t1.size = 4 := by rw [← ht1]; simp [Fips204.pkDecode, Fips204.k]
      rw [Math.ntt_map_emod c hcs, hzHat, Math.w1_congr]
      intro i hi
      simp only [rowApprox, Fips204.matrixVectorNTT, t1Hat, ht1,
        Math.getElem!_map_range Fips204.k i _ hi, Math.getElem!_map_range 4 i _ hi,
        Math.getElem!_map _ _ _ (ht1s ▸ hi)]
    · rw [if_neg hok] at hA
      cases hA
  · rename_i hnone
    simp only [aEntry]
    cases hH : Fips204.hintBitUnpack (sig.extract 2336 2420) with
    | none => simp
    | some h =>
      cases hC : Fips204.sampleInBall (sig.extract 0 32) with
      | none => simp
      | some c =>
        by_cases hok : ((List.range 4).all fun r => (List.range 4).all fun s =>
            (Fips204.rejNTTPoly (pk.extract 0 32 ++ ByteArray.mk #[UInt8.ofNat s, UInt8.ofNat r])).isSome) = true
        · exact (hnone h _ c hH (by rw [Math.expandA_eq, if_pos hok]) hC).elim
        · simp only [Bool.not_eq_true] at hok
          simp [hok]

end MlDsa44.Proofs
