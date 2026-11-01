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
theorem delta_run (s : State) (hs : Ctx s) (v : Nat → Nat)
    (hv : v 0 < 2 ^ 256)
    (tail : List UInt256) (ht : tail.length ≤ 960) (m : ByteArray) :
    runLocatedBlock (locatedPath path)
      (callState s 9109 (denote (fun i => wd (v i)) tail input) m) =
      some (callState s 9123
        (wd (swm (2 ^ 63) (v 6) (v 0)) ::
          denote (fun i => wd (v i)) tail input.tail) m) := by
  rw [reflected_block s hs _ tail ht m]
  simp (disch := omega) only [output, denote, List.map_cons, List.cons_append, Term.eval, delta, Bin.eval,
    ofNat_xor, ofNat_land, ofNat_shl, ofNat_shr, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, swm, ofNat_toNat, wd, Nat.mod_eq_of_lt hv, ofNat_mod]

theorem delta_reach (s : State) (hs : Ctx s) (v : Nat → Nat)
    (hv : v 0 < 2 ^ 256) (tail : List UInt256) (ht : tail.length ≤ 960) (m : ByteArray) :
    Reach (callState s 9109 (denote (fun i => wd (v i)) tail input) m)
      (callState s 9123 (wd (swm (2 ^ 63) (v 6) (v 0)) ::
        denote (fun i => wd (v i)) tail input.tail) m) 36 := by
  exact reach_block hs path (by decide +kernel) (delta_run s hs v hv tail ht m)

#print axioms delta_run
#print axioms delta_reach
end ReflectPrototype
