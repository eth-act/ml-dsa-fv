import EvmSemantics.EVM.Step
import YulEvmCompiler.Decode
set_option warningAsError true
/-!
# Structural raw-bytecode artifacts

A direct-bytecode submission may provide an instruction-boundary view of its bytes.
`ProgramArtifact` records only a byte array, an instruction list, and a proof
that assembling that list gives exactly those bytes. It carries no source
program and uses no compiler-correctness theorem.

The indexed theorems below turn that one byte equality into compact decoder
and jump-destination facts. Proof authors can therefore reason by
instruction index without repeatedly reducing a large byte-array literal.
-/

namespace EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

structure ProgramArtifact where
  code : ByteArray
  instructions : List Instr
  assembly_eq : assemble instructions = code

namespace ProgramArtifact

/-- Byte offset of an instruction index. -/
def instructionPC (p : ProgramArtifact) (index : Nat) : Nat :=
  (assembleBytes (p.instructions.take index)).length

theorem instructionPC_le_code_size (p : ProgramArtifact) (index : Nat) :
    p.instructionPC index ≤ p.code.size := by
  have hsplit := List.take_append_drop index p.instructions
  have hbytes : assembleBytes (p.instructions.take index) ++
      assembleBytes (p.instructions.drop index) = assembleBytes p.instructions := by
    rw [← assembleBytes_append, hsplit]
  have hlen := congrArg List.length hbytes
  have hsize := congrArg ByteArray.size p.assembly_eq
  have hlen' : (assembleBytes (p.instructions.take index)).length +
      (assembleBytes (p.instructions.drop index)).length =
        (assembleBytes p.instructions).length := by simpa using hlen
  have hsize' : (assembleBytes p.instructions).length = p.code.size := by
    change (assembleBytes p.instructions).toArray.size = p.code.size at hsize
    simpa only [List.size_toArray] using hsize
  unfold instructionPC
  omega

private theorem split_at_get {α : Type} {xs : List α} {index : Nat} {x : α}
    (hget : xs[index]? = some x) :
    xs = xs.take index ++ x :: xs.drop (index + 1) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hget
  calc
    xs = xs.take index ++ xs.drop index := (List.take_append_drop index xs).symm
    _ = xs.take index ++ x :: xs.drop (index + 1) := by
      rw [List.drop_eq_getElem_cons hi, hx]

theorem decodeAt_op_index (p : ProgramArtifact) (index : Nat) (o : Operation)
    (hget : p.instructions[index]? = some (.op o))
    (hopcode : Decode.opcodeOf (Instr.opByte o) = some o)
    (hplain : YulEvmCompiler.plainOp o) :
    Decode.decodeAt p.code (p.instructionPC index) = some (o, none) := by
  have hsplit := split_at_get hget
  rw [← p.assembly_eq]
  unfold assemble instructionPC
  change Decode.decodeAt (mkCode (assembleBytes p.instructions))
    (assembleBytes (List.take index p.instructions)).length = _
  have hbytes : assembleBytes p.instructions =
      assembleBytes (p.instructions.take index) ++ (Instr.op o).bytes ++
        assembleBytes (p.instructions.drop (index + 1)) := by
    calc
      assembleBytes p.instructions = assembleBytes
          (p.instructions.take index ++
            Instr.op o :: p.instructions.drop (index + 1)) :=
        congrArg assembleBytes hsplit
      _ = _ := by
        rw [assembleBytes_append, assembleBytes_cons]
        simp [List.append_assoc]
  rw [hbytes]
  exact YulEvmCompiler.decodeAt_op
    (assembleBytes (p.instructions.take index))
    (assembleBytes (p.instructions.drop (index + 1))) o hopcode hplain

theorem decodeAt_push_index (p : ProgramArtifact) (index : Nat)
    (width : Fin 33) (value : UInt256)
    (hget : p.instructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val) :
    Decode.decodeAt p.code (p.instructionPC index) =
      some (.Push ⟨width⟩, some (value, width.val)) := by
  have hsplit := split_at_get hget
  rw [← p.assembly_eq]
  unfold assemble instructionPC
  change Decode.decodeAt (mkCode (assembleBytes p.instructions))
    (assembleBytes (List.take index p.instructions)).length = _
  have hbytes : assembleBytes p.instructions =
      assembleBytes (p.instructions.take index) ++
        (Instr.push width value).bytes ++
          assembleBytes (p.instructions.drop (index + 1)) := by
    calc
      assembleBytes p.instructions = assembleBytes
          (p.instructions.take index ++
            Instr.push width value :: p.instructions.drop (index + 1)) :=
        congrArg assembleBytes hsplit
      _ = _ := by
        rw [assembleBytes_append, assembleBytes_cons]
        simp [List.append_assoc]
  rw [hbytes]
  exact YulEvmCompiler.decodeAt_push
    (assembleBytes (p.instructions.take index))
    (assembleBytes (p.instructions.drop (index + 1))) width value hfit

theorem isValidJumpDest_index (p : ProgramArtifact) (index : Nat)
    (hget : p.instructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest p.code (p.instructionPC index) = true := by
  have hsplit := split_at_get hget
  rw [← p.assembly_eq]
  unfold assemble instructionPC
  change Decode.isValidJumpDest (mkCode (assembleBytes p.instructions))
    (assembleBytes (List.take index p.instructions)).length = true
  have hbytes : assembleBytes p.instructions =
      assembleBytes (p.instructions.take index) ++
        (Instr.op .JUMPDEST).bytes ++
          assembleBytes (p.instructions.drop (index + 1)) := by
    calc
      assembleBytes p.instructions = assembleBytes
          (p.instructions.take index ++
            Instr.op .JUMPDEST :: p.instructions.drop (index + 1)) :=
        congrArg assembleBytes hsplit
      _ = _ := by
        rw [assembleBytes_append, assembleBytes_cons]
        simp [List.append_assoc]
  rw [hbytes]
  exact YulEvmCompiler.isValidJumpDest_boundary
    (p.instructions.take index)
    (assembleBytes (p.instructions.drop (index + 1)))

/-- Install a certified decoder fact into an arbitrary machine state. Gas,
memory, stack, and world fields are irrelevant to decoding. -/
theorem state_decoded_of (p : ProgramArtifact) (s : EvmSemantics.EVM.State)
    (index : Nat)
    (hcode : s.executionEnv.code = p.code)
    (hpc : s.pc.toNat = p.instructionPC index)
    (op : Operation) (imm : Option (UInt256 × Nat))
    (hdecode : Decode.decodeAt p.code (p.instructionPC index) = some (op, imm))
    (havailable : op.availableInFork s.fork = true) :
    s.decoded = some (op, imm) := by
  unfold State.decoded
  rw [hcode, hpc, hdecode]
  simp [havailable]

theorem state_decodedOp_of (p : ProgramArtifact) (s : EvmSemantics.EVM.State)
    (index : Nat)
    (hcode : s.executionEnv.code = p.code)
    (hpc : s.pc.toNat = p.instructionPC index)
    (op : Operation) (imm : Option (UInt256 × Nat))
    (hdecode : Decode.decodeAt p.code (p.instructionPC index) = some (op, imm))
    (havailable : op.availableInFork s.fork = true) :
    s.decodedOp = some op := by
  unfold State.decodedOp
  rw [state_decoded_of p s index hcode hpc op imm hdecode havailable]
  rfl

end ProgramArtifact
end EvmProof
