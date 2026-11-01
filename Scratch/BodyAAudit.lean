import Scratch.BodyAReflect
import MlDsaOpt44.Fn.Blk.BodyA

-- Equality of proof terms forces identical theorem types; proof irrelevance
-- then closes the equality. No casting or weaker wrapper statement.
example : @MemoryReflection.BodyA.bodyA = @MlDsaOpt44.Proofs.Blk.bodyA := rfl
#print axioms MemoryReflection.BodyA.bodyA
#print axioms MlDsaOpt44.Proofs.Blk.bodyA

namespace MemoryReflection
open EvmSemantics EvmSemantics.EVM MlDsaOptCommon
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Exact peak and obligations are part of the checked certificate.
example : run BodyA.program BodyA.input = some ⟨BodyA.output, 17, BodyA.bounds⟩ :=
  BodyA.certificate
example : run BodyA.program BodyA.input ≠ some ⟨BodyA.output, 16, BodyA.bounds⟩ := by
  rw [BodyA.certificate]
  decide +kernel
example : run BodyA.program BodyA.input ≠ some ⟨BodyA.output, 17, []⟩ := by
  rw [BodyA.certificate]
  decide +kernel

-- Read-after-write keeps the exact memory version, without assuming disjointness.
example : step .load ⟨[.var 1], .store .initial (.var 0) (.var 2)⟩ =
    some ⟨[.load (.store .initial (.var 0) (.var 2)) (.var 1)],
      .store .initial (.var 0) (.var 2)⟩ := rfl
example : step .store ⟨[.var 0], .initial⟩ = none := rfl
example : step (.dup 1) ⟨[.var 0], .initial⟩ = none := rfl
example : step (.push 0 999) ⟨[], .initial⟩ = some ⟨[.lit 0], .initial⟩ := rfl
example : 17 + 1006 < 1024 := by decide
example : ¬ (17 + 1007 < 1024) := by decide
end MemoryReflection
