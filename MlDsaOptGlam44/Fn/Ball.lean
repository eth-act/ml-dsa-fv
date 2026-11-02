import MlDsaOpt44.Fn.Ball.Defs
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOptGlam44.Fn.Ball.Loop
set_option linter.unusedVariables false
/-! # `sib` contracts (glam)
Definitions (`codeOf`, `baseOf`, `negCount`, `CRep`, `SibFresh`) in v4's `Fn/Ball/Defs.lean`.

SampleInBall has two copies of v4's lane loop (R4-7 with the long-message switch):
copy 0 scans lanes 1 … 16 of the stream `bs` (272 bytes) and stops at block 1's end,
where `sibext` reads `FLAG`; copy 1 scans lanes 17 … 33.

* `sib_call` (`FLAG = 1`, packed schedule): `CB` holds block 1; block 2 is squeezed on
  demand from the saved kf4 states `S` at `SC` (`MCOPY` to `KS`, `kf4`, `cext 17`).
* `sib_call0` (`FLAG = 0`, long-message schedule): `CB` holds both blocks; `sibext`
  jumps straight to copy 1.

Both are `Ball4.sib_main_gen` (`Fn/Ball/{Blocks,Proof,Scan,Run,Loop}.lean`) with the
frame `sibRegions4` resp. `sibRegions`. On the failure path `sibz` zeroes
`BASES[cnt, τ)`, so every slot ends in range. `Gas.sib` bounds both paths. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

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
    (hz : SibFresh m) (hfl : word m FLAG = 1) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      (∀ i, i < Fips204.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (LIM, LIM + 32), (CW, CW + 8192),
        (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64), (CB + 544, CB + 1088)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib :=
  Ball4.sib_main_gen hs hr (fl := 1) (rs := Ball4.sibRegions4) (S := S)
    ⟨Or.inr rfl, hfl, fun a ha => Ball4.sub_regions ha,
      by simp [Ball4.sibRegions4, KS, KB, LIM, CW, BASES, IDX, NNEG, CB, FLAG],
      fun _ a ha r hr => by
        simp only [Ball4.extRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ha _ (by simp),
      fun _ => ⟨hS, hsc, by simp [Ball4.sibRegions4, KS, KB, LIM, CW, BASES, IDX, NNEG, CB, SC],
        hc2⟩⟩
    (fun x hx h => hcb x (by omega)) hz

/-- **sib on the long-message schedule** (`FLAG = 0`): c's second block (stream
bytes `136 … 271`) is already in `CB[17, 34)` (the alt schedule squeezes c's
slot twice), so the extension at block 1's end goes straight to the second loop
copy. Nothing is squeezed: only the accept step's scratch and `sibz` write
memory, so the frame is smaller than `sib_call`'s. Same postcondition and
budget (`Gas.sib` bounds this cheaper path too). **Open item**. -/
theorem sib_call0 {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray)
    (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x))
    (hz : SibFresh m) (hfl : word m FLAG = 0) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      (∀ i, i < Fips204.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(CW, CW + 8192), (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib :=
  Ball4.sib_main_gen hs hr (fl := 0) (rs := Ball4.sibRegions) (S := fun _ => #[])
    ⟨Or.inl rfl, hfl, fun a ha => ha,
      by simp [Ball4.sibRegions, CW, BASES, IDX, NNEG, FLAG],
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    (fun x hx _ => hcb x hx) hz

end MlDsaOptGlam44.Proofs
