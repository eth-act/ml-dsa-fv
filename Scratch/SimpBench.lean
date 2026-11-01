import Scratch.Reflection
import MlDsaOpt44.Fn.Blk.Bits
namespace ReflectPrototype
open EvmSemantics EvmSemantics.EVM EvmProof.Stepper
open MlDsaOptCommon MlDsaOpt44.Proofs MlDsaOpt44.Proofs.Infra
open MlDsaOpt44.Proofs.Artifact MlDsaOpt44.Proofs.Blk
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

set_option trace.profiler true in
theorem delta_run_simp (s : State) (hs : Ctx s) (v : Nat → Nat)
    (hv : v 0 < 2 ^ 256)
    (tail : List UInt256) (ht : tail.length ≤ 960) (m : ByteArray) :
    runLocatedBlock (locatedPath path)
      (callState s 9109 (denote (fun i => wd (v i)) tail input) m) =
      some (callState s 9123
        (wd (swm (2 ^ 63) (v 6) (v 0)) ::
          denote (fun i => wd (v i)) tail input.tail) m) := by
  opt44_block [path, denote, input, List.range_succ, Term.eval, swm,
    List.range_zero, List.map_cons, List.map_nil, List.map_append, List.tail_cons, ofNat_mod]
  exact (ofNat_mod _).symm

theorem delta_reach_simp (s : State) (hs : Ctx s) (v : Nat → Nat)
    (hv : v 0 < 2 ^ 256) (tail : List UInt256) (ht : tail.length ≤ 960) (m : ByteArray) :
    Reach (callState s 9109 (denote (fun i => wd (v i)) tail input) m)
      (callState s 9123 (wd (swm (2 ^ 63) (v 6) (v 0)) ::
        denote (fun i => wd (v i)) tail input.tail) m) 36 := by
  exact reach_block hs path (by decide +kernel) (delta_run_simp s hs v hv tail ht m)

#print axioms delta_run_simp
#print axioms delta_reach_simp
end ReflectPrototype
