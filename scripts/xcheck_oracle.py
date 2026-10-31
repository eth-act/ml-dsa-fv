#!/usr/bin/env python3
"""FFI oracle for foundry/test/DifferentialFuzz.t.sol.

    python3 scripts/xcheck_oracle.py 0x<calldata> [--lean-evm]

Prints `0x` ‖ abi.encode(uint256[7]):
  [0] Lean spec verdict (MlDsa44.accepts via mldsa44tool spec-file)
  [1] RustCrypto ml-dsa verdict
  [2] Go crypto/internal/fips140/mldsa verdict
  [3] dilithium-py verdict
  [4] 1 iff the hint has a repeated index (dilithium-py's known divergence)
  [5] Lean-semantics frame gas of the frozen bytecode (0 without --lean-evm)
  [6] Lean-semantics returned verdict (0/1; 2 = not run; 3 = no proper word)
"""
import sys

import xcheck_common as xc


def main():
    arg = sys.argv[1]
    cd = bytes.fromhex(arg[2:] if arg.startswith("0x") else arg)
    words = [xc.lean_spec([cd])[0], xc.rust([cd])[0], xc.go([cd])[0], xc.dpy_one(cd),
             int(xc.repeated_hint_index(cd)), 0, 2]
    if "--lean-evm" in sys.argv[2:]:
        gas, halt, ret = xc.lean_evm([cd], jobs=1, log=lambda _: None)[0]
        words[5] = gas
        words[6] = {xc.WORD[0]: 0, xc.WORD[1]: 1}.get(ret, 3) if halt == "returned" else 3
    sys.stdout.write("0x" + "".join(f"{w:064x}" for w in words))


if __name__ == "__main__":
    main()
