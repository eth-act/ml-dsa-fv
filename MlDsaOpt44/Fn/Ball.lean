import MlDsaOpt44.Fn.Ball.Proof
/-! # `sib` contract (WP9)

Definitions (`codeOf`, `baseOf`, `negCount`, `CRep`, `SibFresh`) in `Fn/Ball/Defs.lean`;
block lemmas in `Fn/Ball/Blocks.lean`; loop invariant and scan in `Fn/Ball/Proof.lean`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem sib_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x)) (hz : SibFresh m) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      (∀ i, i < Fips204.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(CW, CW + 8192), (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib :=
  sib_call_proof hs hr m bs hbs hcb hz

end MlDsaOpt44.Proofs
