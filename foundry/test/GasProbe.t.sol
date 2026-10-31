// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {XCheckBase} from "./XCheckBase.sol";
import {GasProbe} from "../src/GasProbe.sol";

/// @notice Validates the measurement method (same controls as the
///         eip8200-challenges/powdr cross-checks): the probe must reproduce
///         the closed-form schedules of the 0x02/0x03 precompiles exactly and
///         report zero for a STOP frame.
contract GasProbeTest is XCheckBase {
    function _patterned(uint256 n) private pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; i++) {
            b[i] = bytes1(uint8(i * 7 + 3));
        }
    }

    function _gas(address target, bytes memory input) private view returns (uint256) {
        GasProbe.Result memory r = GasProbe.probe(target, input);
        require(r.ok, "probe call failed");
        return r.gasUsed;
    }

    function test_probe_matches_precompile_schedules() public view {
        uint256[8] memory sizes = [uint256(0), 1, 31, 32, 33, 376, 1000, 7464];
        for (uint256 i = 0; i < sizes.length; i++) {
            bytes memory input = _patterned(sizes[i]);
            uint256 words = (sizes[i] + 31) / 32;
            assertEq(_gas(address(0x02), input), 60 + 12 * words, "sha256 precompile gas");
            assertEq(_gas(address(0x03), input), 600 + 120 * words, "ripemd160 precompile gas");
        }
    }

    function test_probe_reports_zero_for_stop_frame() public {
        address stopper = address(uint160(0x9001));
        vm.etch(stopper, hex"00");
        assertEq(_gas(stopper, _patterned(7464)), 0, "STOP frame gas");
    }

    /// @dev Short calldata: the proof's `Gas.short` is 267 and the frame
    ///      returns the zero word. 264 gas of instructions plus one memory word.
    function test_short_calldata_costs_267() public view {
        uint256[5] memory sizes = [uint256(0), 1, 1312, 3700, 3731];
        for (uint256 i = 0; i < sizes.length; i++) {
            GasProbe.Result memory r = GasProbe.probe(REFERENCE, _patterned(sizes[i]));
            assertTrue(r.ok, "short call failed");
            assertEq(r.ret, _word(0), "short calldata accepted");
            assertEq(r.gasUsed, 267, "short calldata gas");
        }
    }

    function test_probe_is_independent_of_caller_state() public view {
        bytes memory input = _patterned(1000);
        uint256 before = _gas(address(0x03), input);
        (bool ok,) = address(0x03).staticcall(input);
        require(ok, "precompile call failed");
        bytes memory ballast = new bytes(200_000);
        ballast[199_999] = 0x01;
        assertEq(_gas(address(0x03), input), before, "measurement depends on caller state");
    }
}
