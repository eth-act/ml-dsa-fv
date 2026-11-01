"""Generate scratch-only input data from frozen bytecode; Lean checks alignment."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
code = bytes.fromhex((ROOT / "MlDsaOpt/44/opt.hex").read_text().strip().removeprefix("0x"))
ops = []
pc = 0
while pc < len(code):
    opcode = code[pc]
    width = opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0
    value = int.from_bytes(code[pc + 1:pc + 1 + width], "big")
    ops.append((pc, opcode, width, value))
    pc += 1 + width

def lean_op(op):
    _, o, w, v = op
    if 0x5F <= o <= 0x7F:
        return f".push {w} {v}"
    if 0x80 <= o <= 0x8F:
        return f".dup {o - 0x80}"
    return {0x01: ".bin .add", 0x16: ".bin .land", 0x17: ".bin .lor",
            0x18: ".bin .xor", 0x1B: ".bin .shl", 0x1C: ".bin .shr",
            0x51: ".load", 0x52: ".store", 0x5B: ".dest"}[o]

text = """import Scratch.MemoryReflection
namespace MemoryReflection.BodyA
open MlDsaOpt44.Proofs.Infra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
def program : List Op := [
"""
text += ",\n".join("  " + lean_op(op) for op in ops[3675:4015])
text += "]\ndef path : List (Fin 11792) := [" + ", ".join(map(str, range(3675,4015))) + "]\n"
text += """
theorem alignment : Aligned path program 9106 := by
  simp only [path, program, Aligned, finVal_lit, instrAt_lit, pcAt_lit,
    Op.instr, Bin.instr, MlDsaOptCommon.wd, EvmProof.Word.literal_eq_ofNat,
    Op.width, Nat.reduceAdd, Nat.reducePow, Nat.reduceLT,
    eq_self_iff_true, true_and, and_true]
end MemoryReflection.BodyA
"""
(ROOT / "Scratch/BodyAData.lean").write_text(text)

# Fair single-file timing: include all block-specific alignment and bridges,
# importing only the reusable soundness library and the original BodyA imports.
proof = (ROOT / "Scratch/BodyAReflect.lean").read_text()
proof = proof.removeprefix("import Scratch.BodyAData\n")
imports, proof = proof.split("namespace MemoryReflection.BodyA", 1)
(ROOT / "Scratch/BodyAAll.lean").write_text(
    "import Scratch.MemoryReflection\n" + imports
    + text.removeprefix("import Scratch.MemoryReflection\n")
    + "namespace MemoryReflection.BodyA" + proof)
