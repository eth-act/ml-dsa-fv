// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {XCheckBase} from "./XCheckBase.sol";
import {Schedule} from "../src/Schedule.sol";

/// @notice vectors/calldata.txt and the usable ACVP sigVer rows: revm output
///         equals the expected verdict, revm frame gas equals the Lean
///         semantics' gas exactly, and stays within `Gas.schedule`.
contract VectorsTest is XCheckBase {
    function test_vectors_and_acvp() public {
        Tally memory t = _replay("fixtures/vectors.txt", 48);
        assertEq(t.cases, 48, "47 calldata.txt rows + 1 ACVP row");
    }

    /// @dev Negative control: fixtures/control.txt holds a valid vector with
    ///      its Lean gas off by one and a valid vector with its verdict
    ///      flipped; the replay must flag exactly those.
    function test_harness_detects_mismatches() public {
        string memory path = "fixtures/control.txt";
        vm.closeFile(path);
        Line memory gasOff = this.checkLine(path, false);
        Line memory verdictOff = this.checkLine(path, false);
        Line memory end = this.checkLine(path, false);
        vm.closeFile(path);
        assertTrue(gasOff.outputOk && !gasOff.gasOk && gasOff.scheduleOk, "gas mismatch not detected");
        assertEq(gasOff.revmGas + 1, gasOff.leanGas, "control gas");
        assertTrue(!verdictOff.outputOk && verdictOff.gasOk, "verdict mismatch not detected");
        assertTrue(end.eof, "control has two lines");
    }

    /// @dev `Schedule.gas` against values evaluated from the Lean definition.
    function test_schedule_closed_form_matches_lean() public {
        string memory path = "fixtures/schedule.txt";
        vm.closeFile(path);
        uint256 n;
        while (true) {
            string memory line = vm.readLine(path);
            if (bytes(line).length == 0) break;
            string[] memory f = vm.split(line, " ");
            assertEq(Schedule.gas(vm.parseUint(f[0])), vm.parseUint(f[1]), "Schedule.gas != Lean Gas.schedule");
            n++;
        }
        vm.closeFile(path);
        assertGt(n, 200, "schedule fixture too small");
        assertEq(Schedule.gas(3731), 267);
        assertEq(Schedule.gas(3732), 13_161_063);
    }
}
