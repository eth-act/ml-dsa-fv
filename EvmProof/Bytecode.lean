import EvmSemantics.EVM.Decode
set_option warningAsError true
/-!
# Raw bytecode, without a compiler provenance assumption

direct-bytecode starts from bytes supplied by a participant. `disassemble` splits such
a byte array at EVM instruction boundaries while preserving opcode immediates,
including truncated immediates at the end of code. `assemble` merely joins the
chunks again. The round-trip theorem therefore applies to every `ByteArray`,
including malformed code; it does not assume that a compiler produced it.

`RawInstr` retains the original opcode byte instead of replacing it with an
`Operation`. This matters for invalid opcodes and makes the round trip honest.
Proofs can inspect `RawInstr.opcodeOperation?` to classify a valid opcode and
use `Decode.decodeAt` when they need its full immediate-bearing semantics.
-/

namespace EvmProof

open EvmSemantics
open EvmSemantics.EVM

/-- One raw instruction chunk: its opcode byte and the immediate bytes present
in the artifact. A truncated final immediate is retained at its actual length. -/
structure RawInstr where
  opcode : UInt8
  immediate : List UInt8
  deriving DecidableEq, Repr

namespace RawInstr

/-- Reassemble one raw instruction exactly as it appeared. -/
def bytes (i : RawInstr) : List UInt8 := i.opcode :: i.immediate

@[simp] theorem bytes_ne_nil (i : RawInstr) : i.bytes ≠ [] := by
  simp [bytes]

/-- Decode the opcode byte through the pinned EVM semantics. Invalid opcode
bytes remain `none`; PUSH and EIP-8024 immediates are kept separately. -/
def opcodeOperation? (i : RawInstr) : Option Operation := Decode.opcodeOf i.opcode

end RawInstr

namespace Bytecode

/-- One expected result of the pinned EVM decoder at a byte offset. -/
structure DecodeEntry where
  pc : Nat
  op : Operation
  imm : Option (UInt256 × Nat)
  deriving DecidableEq, Repr

/-- A single Boolean certificate can validate every decoder fact used by a
submission proof.  Keeping this separate from the symbolic trace prevents a
large concrete byte-array reduction from being repeated at every opcode. -/
def DecodeCertificate (code : ByteArray) (entries : List DecodeEntry) : Prop :=
  entries.all (fun e => decide (Decode.decodeAt code e.pc = some (e.op, e.imm))) = true

theorem DecodeCertificate.valid {code : ByteArray} {entries : List DecodeEntry}
    (hcert : DecodeCertificate code entries) {entry : DecodeEntry}
    (hentry : entry ∈ entries) :
    Decode.decodeAt code entry.pc = some (entry.op, entry.imm) := by
  have h := (List.all_eq_true.mp hcert) entry hentry
  exact of_decide_eq_true h

/-! ### `ByteArray.toList` bridge

Core implements `ByteArray.toList` as an opaque tail-recursive loop. Direct
decoder proofs need a structural view of immediate bytes, so establish the
bridge to the underlying array once for every direct-bytecode submission.
-/

private theorem get!_eq_data_toList (bs : Array UInt8) (i : Nat)
    (hi : i < bs.toList.length) : ByteArray.get! ⟨bs⟩ i = bs.toList[i] := by
  show bs[i]! = _
  have hib : i < bs.size := by simpa using hi
  rw [getElem!_pos bs i hib]
  exact (Array.getElem_toList hib).symm

private theorem byteArrayToList_loop_eq (bs : Array UInt8) :
    ∀ n i r, bs.size - i ≤ n →
      ByteArray.toList.loop ⟨bs⟩ i r = r.reverse ++ bs.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    unfold ByteArray.toList.loop
    rw [if_neg (by show ¬i < bs.size; omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
    rw [List.append_nil]
  | succ n ih =>
    intro i r h
    unfold ByteArray.toList.loop
    by_cases hi : (⟨bs⟩ : ByteArray).size > i
    · rw [if_pos hi]
      rw [ih (i + 1) _ (by
        show bs.size - (i + 1) ≤ n
        have : bs.size > i := hi
        omega)]
      have hi' : i < bs.toList.length := by
        rw [Array.length_toList]
        exact hi
      rw [List.drop_eq_getElem_cons hi', get!_eq_data_toList bs i hi']
      simp
    · rw [if_neg hi]
      have hle : bs.toList.length ≤ i := by
        rw [Array.length_toList]
        exact Nat.le_of_not_lt hi
      rw [List.drop_eq_nil_of_le hle, List.append_nil]

/-- Structural view of core's tail-recursive `ByteArray.toList`. This is the
normal form used when proving concrete PUSH immediate values. -/
theorem toList_eq_data (b : ByteArray) : b.toList = b.data.toList := by
  obtain ⟨bs⟩ := b
  show ByteArray.toList.loop ⟨bs⟩ 0 [] = _
  rw [byteArrayToList_loop_eq bs bs.size 0 [] (by omega)]
  simp

/-- A compact, executable certificate that every listed target satisfies the
pinned EVM semantics' jump-destination scan. -/
def JumpDestCertificate (code : ByteArray) (targets : List Nat) : Prop :=
  targets.all (Decode.isValidJumpDest code) = true

/-- Recover the exact `JUMP`/`JUMPI` side condition for any target named in a
validated certificate. -/
theorem JumpDestCertificate.valid {code : ByteArray} {targets : List Nat}
    (hcert : JumpDestCertificate code targets) {pc : Nat} (hpc : pc ∈ targets) :
    Decode.isValidJumpDest code pc = true := by
  exact (List.all_eq_true.mp hcert) pc hpc

/-- Immediate width of an opcode. PUSH1..PUSH32 carry 1..32 bytes. The Osaka
EIP-8024 opcodes DUPN/SWAPN/EXCHANGE carry one byte. The classification comes
from the pinned EVM decoder rather than a second opcode table. -/
def immediateWidth (opcode : UInt8) : Nat :=
  match Decode.opcodeOf opcode with
  | some (.Push p) => p.width.val
  | some (.DupN _) | some (.SwapN _) | some (.Exchange _) => 1
  | _ => 0

/-- Fuelled worker for `disassembleList`. One unit is enough for each input
byte because every emitted chunk consumes at least its opcode byte. -/
def disassembleList.go : Nat → List UInt8 → List RawInstr
  | 0, _ => []
  | _, [] => []
  | fuel + 1, opcode :: rest =>
      let width := immediateWidth opcode
      { opcode, immediate := rest.take width } ::
        disassembleList.go fuel (rest.drop width)

/-- Split a byte list into raw instruction chunks. Invalid opcodes occupy one
byte. A final immediate is truncated to the bytes actually present. -/
def disassembleList (bytes : List UInt8) : List RawInstr :=
  disassembleList.go bytes.length bytes

/-- Join raw instruction chunks into bytes. -/
def assembleList : List RawInstr → List UInt8
  | [] => []
  | i :: is => i.bytes ++ assembleList is

/-- Disassemble a submitted byte array. -/
def disassemble (code : ByteArray) : List RawInstr := disassembleList code.data.toList

/-- Assemble raw instruction chunks. -/
def assemble (is : List RawInstr) : ByteArray := ByteArray.mk (assembleList is).toArray

/-- Enough fuel makes the worker byte preserving. -/
private theorem assembleList_go (bytes : List UInt8) (fuel : Nat)
    (h : bytes.length ≤ fuel) :
    assembleList (disassembleList.go fuel bytes) = bytes := by
  induction fuel generalizing bytes with
  | zero =>
      have : bytes = [] := by simpa using h
      subst bytes
      rfl
  | succ fuel ih =>
      cases bytes with
      | nil => rfl
      | cons opcode rest =>
          simp only [disassembleList.go, assembleList, RawInstr.bytes]
          rw [ih]
          · simpa only [List.cons_append] using
              congrArg (List.cons opcode) (List.take_append_drop (immediateWidth opcode) rest)
          · calc
              (rest.drop (immediateWidth opcode)).length ≤ rest.length := by simp
              _ ≤ fuel := by simpa using h

/-- The raw disassembler loses no bytes, even for invalid opcodes and
truncated final immediates. -/
theorem assembleList_disassembleList (bytes : List UInt8) :
    assembleList (disassembleList bytes) = bytes := by
  exact assembleList_go bytes bytes.length (Nat.le_refl _)

/-- Verified raw-bytecode round trip: disassembling then assembling any
participant submission returns the exact submitted bytes. -/
theorem assemble_disassemble (code : ByteArray) : assemble (disassemble code) = code := by
  cases code with
  | mk data =>
      simp only [assemble, disassemble, assembleList_disassembleList,
        Array.toArray_toList]

/-- Regression case: a truncated PUSH2 remains one chunk and retains its one
available immediate byte. -/
example : disassembleList [0x61, 0xaa] =
    [{ opcode := 0x61, immediate := [0xaa] }] := by decide

/-- Regression case: invalid opcodes are preserved as one-byte chunks. -/
example : assembleList (disassembleList [0x0c, 0xfe]) = [0x0c, 0xfe] := by decide

end Bytecode
end EvmProof
