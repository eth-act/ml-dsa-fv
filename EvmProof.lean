import EvmProof.Amsterdam
import EvmProof.Bytecode
import EvmProof.Bytes
import EvmProof.ByteWindow
import EvmProof.Execution
import EvmProof.Gas
import EvmProof.GasFormula
import EvmProof.Memory
import EvmProof.Meter
import EvmProof.Ops
import EvmProof.Program
import EvmProof.Stepper
import EvmProof.Word
set_option warningAsError true
/-!
# Direct-bytecode proof support

Vendored from powdr-labs/eip8200-challenges (Apache-2.0), namespace renamed
from `Challenge.EvmProof` to `EvmProof`. Byte-preserving disassembly,
a symbolic stepper for pure opcodes, gas-parametric traces and memory lemmas.
No source-language or compiler-correctness premise.
-/
