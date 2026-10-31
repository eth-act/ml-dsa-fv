// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {LeanArtifact} from "../src/LeanArtifact.sol";
import {Schedule} from "../src/Schedule.sol";

/// @title XCheckBase
/// @notice Etches the frozen verifier at the address `MlDsa44.deployAddress`
///         fixes and replays fixture files against it.
///
/// @dev A fixture line (scripts/xcheck_common.py `write_fixture`) is
///      `calldata expected leanGas schedule category note`, with `-` for empty
///      calldata. `expected` is the Lean specification's verdict (on which the
///      fixture script has already required RustCrypto, Go and dilithium-py
///      to agree), `leanGas` is `start.gasAvailable - final.gasAvailable` of
///      the Lean-semantics execution of the same bytes from
///      `MlDsa44.initialState`, and `schedule` is the Lean `Gas.schedule` of
///      the calldata size.
abstract contract XCheckBase is Test {
    /// @dev `MlDsa44.deployAddress := AccountAddress.ofNat 0x8212`.
    address internal constant REFERENCE = address(uint160(0x8212));
    string internal constant FAILURES = "../vectors/fuzz/revm_failures.txt";

    LeanArtifact.Pin internal pin;

    struct Line {
        bool eof;
        bool outputOk;
        bool gasOk;
        bool scheduleOk;
        uint256 size;
        uint256 expected;
        uint256 leanGas;
        uint256 revmGas;
        uint256 schedule;
        string category;
    }

    struct Tally {
        uint256 cases;
        uint256 accepted;
        uint256 outputMismatches;
        uint256 gasMismatches;
        uint256 scheduleViolations;
        uint256 leanGasTotal;
        uint256 revmGasTotal;
        uint256 maxGas;
        uint256 maxGasSchedule;
        uint256 minSlack;
        uint256 minSlackSize;
    }

    function setUp() public virtual {
        vm.etch(GasProbe.STOP_TARGET, hex"00");
        pin = LeanArtifact.load(vm);
        vm.etch(REFERENCE, pin.code);
    }

    /// @notice The 32-byte word the verifier must return for `verdict`.
    function _word(uint256 verdict) internal pure returns (bytes memory) {
        return abi.encode(verdict);
    }

    /// @notice Runs one fixture line in a fresh call frame (so the caller's
    ///         memory does not grow with the corpus) and records a reproducer
    ///         in vectors/fuzz/revm_failures.txt on any disagreement.
    function checkLine(string calldata path, bool record) external returns (Line memory line) {
        string memory text = vm.readLine(path);
        if (bytes(text).length == 0) {
            line.eof = true;
            return line;
        }
        string[] memory f = vm.split(text, " ");
        require(f.length == 6, "fixture: malformed line");
        bytes memory cd = keccak256(bytes(f[0])) == keccak256("-") ? bytes("") : vm.parseBytes(string.concat("0x", f[0]));
        line.size = cd.length;
        line.expected = vm.parseUint(f[1]);
        line.leanGas = vm.parseUint(f[2]);
        line.schedule = vm.parseUint(f[3]);
        line.category = f[4];
        require(line.schedule == Schedule.gas(cd.length), "fixture: Lean schedule != Schedule.gas");

        GasProbe.Result memory r = GasProbe.probe(REFERENCE, cd);
        line.revmGas = r.gasUsed;
        line.outputOk = r.ok && keccak256(r.ret) == keccak256(_word(line.expected));
        line.gasOk = r.gasUsed == line.leanGas;
        line.scheduleOk = r.gasUsed <= line.schedule;
        if (record && !(line.outputOk && line.gasOk && line.scheduleOk)) {
            vm.writeLine(
                FAILURES,
                string.concat(
                    f[0],
                    " expected=",
                    f[1],
                    " revm_ok=",
                    r.ok ? "1" : "0",
                    " revm_ret=",
                    vm.toString(r.ret),
                    " lean_gas=",
                    f[2],
                    " revm_gas=",
                    vm.toString(r.gasUsed),
                    " schedule=",
                    f[3],
                    " cat=",
                    f[4],
                    " note=",
                    f[5]
                )
            );
        }
    }

    /// @notice Replays every line of `path`; asserts output, exact Lean gas and
    ///         the proved schedule on each, and logs a summary.
    function _replay(string memory path, uint256 minCases) internal returns (Tally memory t) {
        vm.closeFile(path);
        t.minSlack = type(uint256).max;
        while (true) {
            Line memory l = this.checkLine(path, true);
            if (l.eof) break;
            t.cases++;
            if (l.expected == 1) t.accepted++;
            if (!l.outputOk) t.outputMismatches++;
            if (!l.gasOk) t.gasMismatches++;
            if (!l.scheduleOk) t.scheduleViolations++;
            t.leanGasTotal += l.leanGas;
            t.revmGasTotal += l.revmGas;
            if (l.revmGas > t.maxGas) {
                t.maxGas = l.revmGas;
                t.maxGasSchedule = l.schedule;
            }
            uint256 slack = l.schedule >= l.revmGas ? l.schedule - l.revmGas : 0;
            // Below 3732 bytes the schedule is the exact cost (267); report the
            // slack of the verification path.
            if (l.size >= Schedule.HEADER && slack < t.minSlack) {
                t.minSlack = slack;
                t.minSlackSize = l.size;
            }
        }
        vm.closeFile(path);
        _log(path, t);
        assertGe(t.cases, minCases, "fixture has too few cases");
        assertEq(t.outputMismatches, 0, "revm output != Lean spec verdict");
        assertEq(t.gasMismatches, 0, "revm gas != Lean-semantics gas");
        assertEq(t.scheduleViolations, 0, "revm gas > Gas.schedule");
        assertEq(t.revmGasTotal, t.leanGasTotal, "suite gas total");
    }

    function _log(string memory path, Tally memory t) internal pure {
        console2.log(
            string.concat(
                path,
                ": cases=",
                vm.toString(t.cases),
                " accepted=",
                vm.toString(t.accepted),
                " output_mismatch=",
                vm.toString(t.outputMismatches),
                " gas_mismatch=",
                vm.toString(t.gasMismatches),
                " over_schedule=",
                vm.toString(t.scheduleViolations)
            )
        );
        console2.log(
            string.concat(
                "  lean_gas_total=",
                vm.toString(t.leanGasTotal),
                " revm_gas_total=",
                vm.toString(t.revmGasTotal),
                " max_gas=",
                vm.toString(t.maxGas),
                " (schedule ",
                vm.toString(t.maxGasSchedule),
                ") min_slack=",
                vm.toString(t.minSlack),
                " at size ",
                vm.toString(t.minSlackSize)
            )
        );
    }
}
