import EvmProof
set_option warningAsError true
/-!
# Artifact-independent vocabulary for direct-bytecode proofs

Shared by every hand-scheduled artifact (`MlDsaOpt44`, later 65/87): states at
a program counter, memory reading, frames. Artifact-specific facts (the code,
the memory map, entry points) live in the per-artifact `Layout` and the
generated `Infra` modules.
-/

namespace MlDsaOptCommon

open EvmSemantics
open EvmSemantics.EVM

/-- `s` at program counter `pc` with the given stack and memory. -/
def callState (s : State) (pc : Nat) (stack : List UInt256) (memory : ByteArray) : State :=
  { s with pc := UInt256.ofNat pc, stack, memory }

/-- The word `UInt256.ofNat n`. -/
abbrev wd (n : Nat) : UInt256 := UInt256.ofNat n

/-- A Boolean returned in a stack word. -/
def flag (b : Bool) : UInt256 := UInt256.ofNat (if b then 1 else 0)

/-- Byte `a` of memory, zero past the end (EVM memory semantics). -/
def byteAt (m : ByteArray) (a : Nat) : Nat := if h : a < m.size then m[a].toNat else 0

/-- The 32-byte big-endian word at `a`. -/
def word (m : ByteArray) (a : Nat) : Nat := (MachineState.readWord m a).toNat

/-- `m'` agrees with `m` outside the half-open byte ranges `rs`. -/
def FrameExcept (m m' : ByteArray) (rs : List (Nat × Nat)) : Prop :=
  ∀ a, (∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) → byteAt m' a = byteAt m a

/-- The bytes `b` are stored at `base`. -/
def BytesAt (m : ByteArray) (base : Nat) (b : ByteArray) : Prop :=
  ∀ i, i < b.size → byteAt m (base + i) = b[i]!.toNat

/-- `t` differs from `s` only in frame-local machine fields. -/
def FrameLocal (s t : State) : Prop :=
  t = { s with pc := t.pc, stack := t.stack, memory := t.memory,
               activeWords := t.activeWords, halt := t.halt, hReturn := t.hReturn,
               gasAvailable := t.gasAvailable }

end MlDsaOptCommon
