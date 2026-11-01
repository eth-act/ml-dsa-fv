import MlDsaOpt44.Fn.Blk
/-!
# RejNTTPoly fix-ups: `fix`, `gfix` (WP5)

After the five squeezes of a SIMD group, `ABUF` holds (lane = slot) the 280
positional candidates of every slot and `FL` one rejection-flag word per 8
candidates. A slot with a rejection among its first 256 candidates is
compacted in place by `fix` (branch-free flagged groups, masked word copies
for clean ones); the sixth squeeze is made on demand, saving and restoring
the kf4 state through `BK` (`MCOPY`), and recorded in `HAVE6`.

Notation: slot `s` of the group started from the absorbed state `I s`
(before the first permutation); its block `b` is `permN (b + 1) (I s)`, its
candidate `t < 336` is `candI (I s) t`, and its RejNTTPoly result over the
1008-byte stream is `aI (I s)` (`= rejNTTPoly seed` when `I s` is the padded
seed, `Math/Sponge.lean`).
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
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

/-- **fix**: `[64 s, ret] ↦ [ok]`. Compacts lane `s` of `ABUF` to the slot's
RejNTTPoly result; other pending slots stay pending; the `KS` state is
restored. The caller has seen a flag of slot `s` among the first 32 groups.
The cost is `Gas.fixSq` if this call made the sixth squeeze, else
`Gas.fixNo`. -/
theorem fix_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.fix ret tail) (m : ByteArray) (hrc : RC4Table m)
    {sl : Nat} (hsl : sl < 4) (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hks : KS4 m S)
    (I : Fips202.SpongeState) (hp : Pending m S sl I)
    (hflag : ∃ g, g < 32 ∧ flagBit (word m (FL + 32 * g)) sl = 1) :
    ∃ m', (∀ a, aI I = some a → ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat) ∧
      (∀ sl' I', sl' < 4 → sl' ≠ sl → Pending m S sl' I' → Pending m' S sl' I') ∧
      (∀ sl', sl' < 4 → sl' ≠ sl → ∀ t, t < 280 →
        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      KS4 m' S ∧ (word m HAVE6 ≠ 0 → word m' HAVE6 ≠ 0) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.fix [wd (64 * sl)] ret tail m [flag (aI I).isSome] m'
        (if word m HAVE6 = 0 ∧ word m' HAVE6 ≠ 0 then Gas.fixSq else Gas.fixNo) := by
  sorry

/-- **gfix**: `[amask, ret] ↦ [ok]`. Every active slot (bit `s` of `amask`)
ends with its RejNTTPoly result in lane `s` of `ABUF[0, 256)`; `ok` iff all
active slots succeeded. -/
theorem gfix_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.gfix ret tail) (m : ByteArray) (hrc : RC4Table m)
    {amask : Nat} (hamask : amask < 16)
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hks : KS4 m S)
    (I : Nat → Fips202.SpongeState) (h6 : word m HAVE6 = 0)
    (hp : ∀ sl, sl < 4 → amask.testBit sl → Pending m S sl (I sl)) :
    ∃ m', (∀ sl, sl < 4 → amask.testBit sl → ∀ a, aI (I sl) = some a →
        ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat) ∧
      KS4 m' S ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.gfix [wd amask] ret tail m
        [flag ((List.range 4).all fun sl => !amask.testBit sl || (aI (I sl)).isSome)] m'
        (Gas.gfix 4) := by
  sorry

end MlDsaOpt44.Proofs
