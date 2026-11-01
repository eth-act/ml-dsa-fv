import MlDsaOpt44.Fn.Blk.Defs
set_option warningAsError true
/-!
# Vocabulary of the RejNTTPoly fix-ups

`candI`, `aI`, `flagBit`, `SlotBlocks`, `Pending` (see `Fn/Fix.lean`). Light
module, so `Math/Sponge.lean` need not wait for the `fix` proofs.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open MlDsaOptCommon
open MlDsa44

/-- Candidate `t` of the positional stream of a slot started from `I`. -/
def candI (I : Fips202.SpongeState) (t : Nat) : Nat := cand (permN (t / 56 + 1) I) (t % 56)

/-- RejNTTPoly over the six squeezed blocks of a slot started from `I`. -/
def aI (I : Fips202.SpongeState) : Option Fips204.Poly :=
  Fips204.rejNTTPolyOf (Fips202.squeeze 168 (EvmSemantics.Crypto.Keccak.permute I) 6)

/-- Bit 23 of lane `s` of a flag word. -/
def flagBit (w s : Nat) : Nat := w / 2 ^ (64 * s + 23) % 2

/-- Candidates `[0, 56 nb)` of slot `s` and their flags `[0, 7 nb)` are in
`ABUF` / `FL`. -/
def SlotBlocks (m : ByteArray) (s : Nat) (I : Fips202.SpongeState) (nb : Nat) : Prop :=
  (∀ t, t < 56 * nb → lane (word m (ABUF + 32 * t)) s = candI I t) ∧
  (∀ g, g < 7 * nb → flagBit (word m (FL + 32 * g)) s =
    if ((List.range 8).any fun i => decide (Fips204.q ≤ candI I (8 * g + i))) then 1 else 0)

/-- A slot still to be fixed: its first five blocks are in place, and either
the sixth squeeze has not been made (`HAVE6 = 0`, and the kf4 state `S` in
`KS` is slot-wise five permutations past `I`) or it has (all six blocks in
place). -/
def Pending (m : ByteArray) (S : Nat → Fips202.SpongeState) (s : Nat)
    (I : Fips202.SpongeState) : Prop :=
  SlotBlocks m s I 5 ∧
  (word m HAVE6 = 0 → S s = permN 5 I) ∧
  (word m HAVE6 ≠ 0 → SlotBlocks m s I 6)

end MlDsaOpt44.Proofs
