// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {XCheckBase} from "./XCheckBase.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {Schedule} from "../src/Schedule.sol";

/// @notice Forge-native mutation fuzzing with live oracles.
///
/// @dev Each run takes a valid EIP-8355 calldata (the 14 accepted rows of
///      fixtures/vectors.txt and the first 64 of fixtures/fuzz/valid.txt:
///      fresh keys, message lengths 0 … 4096), applies one fuzzer-chosen
///      mutation (bit flips anywhere / in the hint / in pk or M, hint byte or
///      count overwrite, hint byte swap, z coefficient set to a norm-boundary
///      encoding, truncation, extension, or none), executes it
///      in revm and asks scripts/xcheck_oracle.py (via `vm.ffi`) for the
///      verdicts of the Lean specification, RustCrypto ml-dsa, Go's FIPS 140-3
///      mldsa and dilithium-py. revm must agree with the Lean specification,
///      as must Rust and Go; dilithium-py must too except on a repeated hint
///      index. Gas must be within `Gas.schedule`. With `XCHECK_LEAN_GAS=1` the
///      oracle also executes the case in the Lean EVM semantics (~3 s per run)
///      and revm gas must equal it exactly.
///
///      A disagreement is appended to vectors/fuzz/forge_fuzz_failures.txt
///      before the assertion fails.
contract DifferentialFuzzTest is XCheckBase {
    string internal constant FUZZ_FAILURES = "../vectors/fuzz/forge_fuzz_failures.txt";
    uint256 internal constant PK_LEN = 1312;
    uint256 internal constant Z_OFF = PK_LEN + 32;
    uint256 internal constant H_OFF = PK_LEN + 32 + 4 * 576;

    bytes[] internal bases;
    bool internal leanGas;
    /// @dev Optional per-run log (`XCHECK_FUZZ_LOG=cache/<name>.txt`):
    ///      `kind size revm lean dpy revmGas leanEvmGas schedule ok|FAIL`.
    string internal statsLog;

    function setUp() public override {
        super.setUp();
        leanGas = vm.envOr("XCHECK_LEAN_GAS", false);
        statsLog = vm.envOr("XCHECK_FUZZ_LOG", string(""));
        _loadValid("fixtures/vectors.txt", type(uint256).max);
        require(bases.length >= 10, "too few valid bases");
        // Plus fresh keys and message lengths from the corpus (0 .. 4096 bytes).
        _loadValid("fixtures/fuzz/valid.txt", 64);
    }

    function _loadValid(string memory path, uint256 limit) internal {
        vm.closeFile(path);
        for (uint256 n = 0; n < limit;) {
            string memory line = vm.readLine(path);
            if (bytes(line).length == 0) break;
            string[] memory f = vm.split(line, " ");
            if (vm.parseUint(f[1]) == 1) {
                bases.push(vm.parseBytes(string.concat("0x", f[0])));
                n++;
            }
        }
        vm.closeFile(path);
    }

    function _flip(bytes memory cd, uint256 lo, uint256 hi, uint256 sel) private pure returns (string memory) {
        uint256 bit = sel % ((hi - lo) * 8);
        cd[lo + bit / 8] ^= bytes1(uint8(1 << (bit % 8)));
        return string.concat("flip byte ", vm.toString(lo + bit / 8));
    }

    function _setZRaw(bytes memory cd, uint256 coeff, uint256 raw) private pure {
        for (uint256 k = 0; k < 18; k++) {
            uint256 bit = coeff * 18 + k;
            uint256 idx = Z_OFF + bit / 8;
            bytes1 mask = bytes1(uint8(1 << (bit % 8)));
            if ((raw >> k) & 1 == 1) cd[idx] |= mask;
            else cd[idx] &= ~mask;
        }
    }

    /// @dev Applies mutation `kind` to a copy of `base`.
    function _mutate(bytes memory base, uint256 kind, uint256 a, uint256 b)
        internal
        pure
        returns (bytes memory cd, string memory what)
    {
        cd = bytes.concat(base);
        uint256 len = cd.length;
        if (kind == 0) {
            what = "unmodified";
        } else if (kind == 1) {
            what = _flip(cd, 0, len, a);
        } else if (kind == 2) {
            what = _flip(cd, H_OFF, H_OFF + 84, a);
        } else if (kind == 3) {
            cd[H_OFF + a % 84] = bytes1(uint8(b));
            what = string.concat("hint byte ", vm.toString(a % 84), " := ", vm.toString(uint8(b)));
        } else if (kind == 4) {
            uint256[14] memory raws = [
                uint256(0), 1, 77, 78, 79, 80, 131071, 131072, 131073, 262064, 262065, 262066, 262067, 262143
            ];
            uint256 raw = (b >> 8) % 2 == 0 ? raws[b % 14] : b % 262144;
            _setZRaw(cd, a % 1024, raw);
            what = string.concat("z coeff ", vm.toString(a % 1024), " raw := ", vm.toString(raw));
        } else if (kind == 5) {
            uint256 n = a % len;
            assembly {
                mstore(cd, n)
            }
            what = string.concat("truncate to ", vm.toString(n));
        } else if (kind == 6) {
            uint256 extra = 1 + a % 300;
            bytes memory tail = new bytes(extra);
            for (uint256 i = 0; i < extra; i++) {
                tail[i] = bytes1(uint8(uint256(keccak256(abi.encode(b, i)))));
            }
            cd = bytes.concat(cd, tail);
            what = string.concat("extend by ", vm.toString(extra));
        } else if (kind == 7) {
            uint256 i = H_OFF + a % 80;
            uint256 j = H_OFF + b % 80;
            (cd[i], cd[j]) = (cd[j], cd[i]);
            what = string.concat("swap hint bytes ", vm.toString(a % 80), " ", vm.toString(b % 80));
        } else if (kind == 8) {
            what = (len > 3732 && b % 2 == 0) ? _flip(cd, 3732, len, a) : _flip(cd, 0, PK_LEN, a);
        } else {
            cd[H_OFF + 80 + a % 4] = bytes1(uint8(b));
            what = string.concat("hint count ", vm.toString(a % 4), " := ", vm.toString(uint8(b)));
        }
    }

    struct Verdicts {
        uint256 lean;
        uint256 rust;
        uint256 go;
        uint256 dpy;
        uint256 dpyKnown;
        uint256 leanEvmGas;
        uint256 leanEvmVerdict;
    }

    function _oracles(bytes memory cd) internal returns (Verdicts memory v) {
        string[] memory cmd = new string[](leanGas ? 4 : 3);
        cmd[0] = "python3";
        cmd[1] = "../scripts/xcheck_oracle.py";
        cmd[2] = vm.toString(cd);
        if (leanGas) cmd[3] = "--lean-evm";
        uint256[7] memory w = abi.decode(vm.ffi(cmd), (uint256[7]));
        v = Verdicts(w[0], w[1], w[2], w[3], w[4], w[5], w[6]);
    }

    function testFuzz_mutated_calldata_matches_oracles(uint256 baseSel, uint8 kind, uint256 a, uint256 b)
        public
    {
        // The fuzzer's dictionary favours 0; keep unmodified bases to ~1/80.
        uint256 k = kind % 10;
        if (k == 0 && a % 8 != 0) k = 1 + a % 9;
        (bytes memory cd, string memory what) = _mutate(bases[baseSel % bases.length], k, a, b);

        GasProbe.Result memory r = GasProbe.probe(REFERENCE, cd);
        uint256 revm = r.ok && r.ret.length == 32 ? abi.decode(r.ret, (uint256)) : 2;
        Verdicts memory v = _oracles(cd);
        uint256 sched = Schedule.gas(cd.length);

        bool ok = revm == v.lean && v.rust == v.lean && v.go == v.lean && (v.dpy == v.lean || v.dpyKnown == 1)
            && r.gasUsed <= sched;
        if (leanGas) ok = ok && v.leanEvmVerdict == v.lean && v.leanEvmGas == r.gasUsed;
        if (bytes(statsLog).length != 0) {
            vm.writeLine(
                statsLog,
                string.concat(
                    vm.toString(k),
                    " ",
                    vm.toString(cd.length),
                    " ",
                    vm.toString(revm),
                    " ",
                    vm.toString(v.lean),
                    " ",
                    vm.toString(v.dpy),
                    " ",
                    vm.toString(r.gasUsed),
                    " ",
                    vm.toString(leanGas ? v.leanEvmGas : 0),
                    " ",
                    vm.toString(sched),
                    ok ? " ok" : " FAIL"
                )
            );
        }
        if (!ok) {
            vm.writeLine(
                FUZZ_FAILURES,
                string.concat(
                    vm.toString(cd),
                    " mutation=",
                    what,
                    " revm=",
                    vm.toString(revm),
                    " revm_gas=",
                    vm.toString(r.gasUsed),
                    " lean=",
                    vm.toString(v.lean),
                    " rust=",
                    vm.toString(v.rust),
                    " go=",
                    vm.toString(v.go),
                    " dpy=",
                    vm.toString(v.dpy),
                    " lean_evm_gas=",
                    vm.toString(v.leanEvmGas),
                    " schedule=",
                    vm.toString(sched)
                )
            );
        }
        assertEq(revm, v.lean, "revm != Lean spec");
        assertEq(v.rust, v.lean, "RustCrypto != Lean spec");
        assertEq(v.go, v.lean, "Go != Lean spec");
        if (v.dpyKnown == 0) assertEq(v.dpy, v.lean, "dilithium-py != Lean spec");
        assertLe(r.gasUsed, sched, "revm gas > Gas.schedule");
        if (cd.length < Schedule.HEADER) assertEq(r.gasUsed, 267, "short calldata gas");
        if (leanGas) {
            assertEq(v.leanEvmVerdict, v.lean, "Lean-semantics execution != Lean spec");
            assertEq(r.gasUsed, v.leanEvmGas, "revm gas != Lean-semantics gas");
        }
    }
}
