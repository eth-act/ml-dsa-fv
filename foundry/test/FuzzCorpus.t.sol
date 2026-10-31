// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {XCheckBase} from "./XCheckBase.sol";

/// @notice Replays the differential fuzz corpus (scripts/fuzz_corpus.py)
///         against revm. Every case's verdict was produced by the Lean
///         specification and confirmed by RustCrypto ml-dsa, Go's FIPS 140-3
///         mldsa and dilithium-py (modulo its known repeated-hint-index
///         divergence); its gas by executing the same bytes in the Lean EVM
///         semantics. Here revm must return the same word, charge exactly the
///         same frame gas, and stay within `Gas.schedule`.
///
/// @dev One test per category so forge runs them in parallel.
contract FuzzCorpusTest is XCheckBase {
    function _category(string memory name) internal returns (Tally memory) {
        return _replay(string.concat("fixtures/fuzz/", name, ".txt"), 1);
    }

    function test_corpus_valid() public {
        Tally memory t = _category("valid");
        assertEq(t.accepted, t.cases, "every valid signature accepted");
    }

    function test_corpus_z_forced() public {
        Tally memory t = _category("z-forced");
        assertEq(2 * t.accepted, t.cases, "half the forced-z signatures sit inside the bound");
    }

    function test_corpus_flip_pk() public {
        _category("flip-pk");
    }

    function test_corpus_flip_ctilde() public {
        _category("flip-ctilde");
    }

    function test_corpus_flip_z() public {
        _category("flip-z");
    }

    function test_corpus_flip_hint() public {
        _category("flip-hint");
    }

    function test_corpus_flip_msg() public {
        _category("flip-msg");
    }

    function test_corpus_hint_struct() public {
        _category("hint-struct");
    }

    function test_corpus_z_raw() public {
        _category("z-raw");
    }

    function test_corpus_length() public {
        _category("length");
    }

    function test_corpus_other() public {
        _category("other");
    }
}
