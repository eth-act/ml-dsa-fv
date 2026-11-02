import MlDsaOpt44.Fn.Ball.Defs
import MlDsaOpt44.Fn.Keccak
import MlDsaOpt44.Fn.Ball.V4Loop
/-! # `sib` contract (WP9)
Definitions (`codeOf`, `baseOf`, `negCount`, `CRep`, `SibFresh`) in `Fn/Ball/Defs.lean`.

The stream `bs` (272 bytes): its first block (lanes 0 … 16) is in `CB`; the
second block is lanes 0 … 16 of slot 0 of the saved kf4 states `S` (at `SC`)
after one more permutation. `KS`, `KB` and `CB[17, 34)` are scratch.

The proof is `sib_main` (`Fn/Ball/V4*.lean`). On the failure path `sibz`
zeroes `BASES[cnt, τ)`, so every slot ends in range. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

theorem sib_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (hrc : RC4Table m)
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hsc : St4At m SC S)
    (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 17 → word m (CB + 32 * x) = le64 bs (8 * x))
    (hc2 : ∀ x, x < 17 → le64 bs (136 + 8 * x) = laneOf (EvmSemantics.Crypto.Keccak.permute (S 0)) x)
    (hz : SibFresh m) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      (∀ i, i < Fips204.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (LIM, LIM + 32), (CW, CW + 8192),
        (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64), (CB + 544, CB + 1088)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib :=
  sib_main hs hr m hrc S hS hsc bs hbs hcb hc2 hz

end MlDsaOpt44.Proofs
