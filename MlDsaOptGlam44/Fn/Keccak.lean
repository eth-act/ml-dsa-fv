import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Fn.Kf4.Main
import MlDsaOptGlam44.Fn.Kf1.Main
/-!
# `kf4` and `kf1`: Keccak-f[1600], Glamsterdam kernels

The stack-resident, fully unrolled kernels (`scripts/opt_keccak_glam.py`),
proved in `Fn/Kf4/Main.lean` (`kf4_spec`) and `Fn/Kf1/Main.lean` (`kf1_spec`).
They are restated here in the shape of v4's contracts (`MlDsaOpt44/Fn/Keccak.lean`)
so that the ported callers use them unchanged: iota is a `PUSH` immediate, so
the table hypotheses `RC4Table` / `RC1Table` are `True` in this artifact
(`MlDsaOptGlam44.Proofs.RC4Table`), and only `KS` is written, a smaller frame
than v4's (`KB`, and for `kf1` `KZ`, are untouched).
-/

namespace MlDsaOptGlam44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs
open MlDsa44

/-- **kf4**: Keccak-f on each of the four interleaved states in `KS`. -/
theorem kf4_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kf4 ret tail) (m : ByteArray) (_hrc : RC4Table m) :
    ∃ m', (∀ S, Sized4 S → KS4 m S →
        KS4 m' fun k => EvmSemantics.Crypto.Keccak.permute (S k)) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800)] ∧
      Call s Entry.kf4 [] ret tail m [] m' Gas.kf4 := by
  obtain ⟨m', h1, h2, h3⟩ := Kf4.kf4_spec hs hr m
  exact ⟨m', h1, h2.mono (by simp), h3⟩

/-- **kf1**: Keccak-f on the replicated state in `KS`. -/
theorem kf1_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kf1 ret tail) (m : ByteArray) (_hrc : RC1Table m) :
    ∃ m', (∀ S : Fips202.SpongeState, S.size = 25 → KS1 m S →
        KS1 m' (EvmSemantics.Crypto.Keccak.permute S)) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] ∧
      Call s Entry.kf1 [] ret tail m [] m' Gas.kf1 := by
  obtain ⟨m', h1, h2, h3⟩ := Kf1.kf1_spec hs hr m
  exact ⟨m', h1, h2.mono (by simp), h3⟩

end MlDsaOptGlam44.Proofs
