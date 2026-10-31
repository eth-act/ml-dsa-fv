// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

/// @title Schedule
/// @notice `MlDsa44.Proofs.Gas.schedule`, the gas budget the Lean theorem
///         `reference_correctWithSchedule` proves sufficient, as a function of
///         the calldata size. Closed form from README.md; `ScheduleTest`
///         checks it against values evaluated from the Lean definition
///         (fixtures/schedule.txt, written by scripts/xcheck_fixtures.py, which
///         compares all sizes 0 .. 3732 + 4500 and a sparse tail).
library Schedule {
    uint256 internal constant HEADER = 3732;

    function gas(uint256 size) internal pure returns (uint256) {
        if (size < HEADER) return 267;
        uint256 n = size - HEADER;
        uint256 ell = n + 66;
        uint256 w = (81120 + n + 31) / 32;
        return 13_140_898 + 59_324 * (ell / 136) + 3 * (((ell % 136) + 31) / 32) + 3 * ((n + 31) / 32) + 3 * w
            + w * w / 512;
    }
}
