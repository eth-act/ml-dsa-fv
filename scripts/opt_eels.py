#!/usr/bin/env python3
"""Cross-check verifier bytecode on the execution specs (EELS), fork Amsterdam.

The second EVM implementation for the Glamsterdam variant: EELS's Amsterdam
fork implements EIP-8024 (DUPN / SWAPN / EXCHANGE) and EIP-7954. This runs
the frame with EELS's own opcode implementations, gas and memory accounting
(the interpreter loop of vm/interpreter.py process_call, without the
transaction-level wrapper) and prints frame gas and the returned word per
calldata line, comparable to opt_evm.run(..., fork="glamsterdam").

Setup (outside this repository):
  git clone https://github.com/ethereum/execution-specs /tmp/eels
  python3 -m venv /tmp/eelsenv && /tmp/eelsenv/bin/pip install -e /tmp/eels
Usage:
  /tmp/eelsenv/bin/python scripts/opt_eels.py HEX CALLDATA_FILE [N_LINES]
"""
import sys
import time

from ethereum_types.numeric import U256, Uint
from ethereum.forks.amsterdam.vm import Evm
from ethereum.forks.amsterdam.vm.exceptions import ExceptionalHalt, Revert
from ethereum.forks.amsterdam.vm.gas import ExecutionGas, GasMeter, StateGas
from ethereum.forks.amsterdam.vm.instructions import Ops, op_implementation
from ethereum.forks.amsterdam.vm.runtime import get_valid_jump_destinations


def main(argv):
    code = bytes.fromhex(open(argv[0]).read().strip())
    nmax = int(argv[2]) if len(argv) > 2 else 1 << 30
    jd = get_valid_jump_destinations(code)
    G = 1 << 40
    for line in open(argv[1]).read().splitlines()[:nmax]:
        f = line.split()
        cd = b"" if f[0] == "-" else bytes.fromhex(f[0])
        gm = GasMeter(gas_left=ExecutionGas(Uint(G)), state_gas_left=StateGas(Uint(0)),
                      state_gas_baseline=StateGas(Uint(0)))
        evm = Evm(pc=Uint(0), stack=[], memory=bytearray(), code=code, gas_meter=gm,
                  valid_jump_destinations=jd, logs=(), running=True, block_env=None, tx_env=None,
                  caller=None, current_target=None, value=U256(0), call_data=cd, code_address=None,
                  depth=Uint(0), should_transfer_value=False, is_static=False,
                  disable_precompiles=False, parent_evm=None, output=b"", accounts_to_delete=set(),
                  return_data=b"", error=None, accessed_addresses=set(), accessed_storage_keys=set())
        t = time.time()
        status = "ok"
        try:
            while evm.running and int(evm.pc) < len(code):
                op_implementation[Ops(code[evm.pc])](evm)
        except (ExceptionalHalt, Revert) as e:
            status = type(e).__name__
        got = int.from_bytes(evm.output, "big") if len(evm.output) == 32 else None
        print(f"eels len={len(cd)} exp={f[1]} got={got} status={status} gas={G - int(gm.gas_left)} "
              f"({time.time() - t:.0f}s)", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
