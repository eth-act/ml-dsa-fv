// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {LeanArtifact} from "../src/LeanArtifact.sol";

/// @title OptVerdictsTest
/// @notice Replays the vectors and the fuzz corpus against an alternate
///         (optimised, unproved) verifier bytecode and checks only the verdict:
///         the call must succeed and return exactly `abi.encode(expected)`.
///         Gas is recorded, not compared.
///
/// @dev Enabled by environment variables; without `OPT_HEX` every test returns
///      immediately, so plain `forge test` is unaffected.
///
///      * `OPT_HEX`: hex artifact path relative to foundry/ (e.g.
///        `../MlDsaOpt/44/opt.hex`).
///      * `OPT_SET`: parameter set, 44 (default), 65 or 87.
///
///      Set 44 replays fixtures/vectors.txt and every fixtures/fuzz/<category>.txt
///      (lines `calldata expected leanGas schedule category note`); sets 65 and
///      87 replay ../vectors/mldsa<set>/calldata.txt (lines
///      `calldata expected note...`). Only fields 0 and 1 are used; calldata `-`
///      is empty. Every line is appended to cache/opt/<set>_<name>.tsv
///      (`set file line size expected returned gas`), mismatching lines with
///      full calldata to cache/opt/failures_<set>_<name>.txt; both files are
///      recreated by the test that owns them, one pair per test function so
///      parallel tests never share a file. scripts/opt_forge.sh runs the suite
///      and summarises the TSVs.
contract OptVerdictsTest is Test {
    string internal constant OUT_DIR = "cache/opt";
    /// @dev Upper bound for one verifier frame (the ML-DSA-87 reference peaks
    ///      at 39.2M), so a non-halting candidate fails in well under a second
    ///      per case instead of burning the whole test gas limit.
    uint256 internal constant GAS_CAP = 100_000_000;

    bool internal enabled;
    string internal artifact;
    uint256 internal set;
    address internal target;

    struct Line {
        bool eof;
        bool ok;
        uint256 size;
        uint256 expected;
        uint256 gas;
    }

    struct Tally {
        uint256 cases;
        uint256 accepted;
        uint256 mismatches;
        uint256 gasTotal;
        uint256 minGas;
        uint256 maxGas;
        uint256 emptyMsgLine;
        uint256 emptyMsgGas;
    }

    function setUp() public {
        string memory hexPath = vm.envOr("OPT_HEX", string(""));
        if (bytes(hexPath).length == 0) return;
        set = vm.envOr("OPT_SET", uint256(44));
        if (set == 44) target = address(uint160(0x8212));
        else if (set == 65) target = address(uint160(0x8213));
        else if (set == 87) target = address(uint160(0x8214));
        else revert("OPT_SET must be 44, 65 or 87");
        bytes memory code = LeanArtifact.parseHex(vm.readFile(hexPath));
        require(code.length != 0, "OPT_HEX is empty");
        vm.etch(GasProbe.STOP_TARGET, hex"00");
        vm.etch(target, code);
        vm.createDir(OUT_DIR, true);
        enabled = true;
        artifact = string.concat("opt artifact ", hexPath, " set ", vm.toString(set), " size ", vm.toString(code.length));
    }

    /// @dev pk ‖ σ: the calldata length of an empty-message signature.
    function _minLength() internal view returns (uint256) {
        if (set == 44) return 1312 + 2420;
        if (set == 65) return 1952 + 3309;
        return 2592 + 4627;
    }

    function _out(string memory name, string memory kind, string memory ext) internal view returns (string memory) {
        return string.concat(OUT_DIR, "/", kind, vm.toString(set), "_", name, ext);
    }

    function _returned(GasProbe.Result memory r) internal pure returns (string memory) {
        if (!r.ok) return string.concat("revert:", vm.toString(r.ret));
        if (r.ret.length == 32) return vm.toString(abi.decode(r.ret, (uint256)));
        return vm.toString(r.ret);
    }

    /// @notice Runs one line in a fresh call frame (so the caller's memory does
    ///         not grow with the corpus) and records it.
    function checkLine(string calldata path, uint256 lineNo, string calldata tsv, string calldata failures)
        external
        returns (Line memory line)
    {
        string memory text = vm.readLine(path);
        if (bytes(text).length == 0) {
            line.eof = true;
            return line;
        }
        string[] memory f = vm.split(text, " ");
        require(f.length >= 2, "fixture: malformed line");
        bytes memory cd = keccak256(bytes(f[0])) == keccak256("-") ? bytes("") : vm.parseBytes(string.concat("0x", f[0]));
        line.size = cd.length;
        line.expected = vm.parseUint(f[1]);

        GasProbe.Result memory r = GasProbe.probeCapped(target, cd, GAS_CAP);
        line.gas = r.gasUsed;
        line.ok = r.ok && keccak256(r.ret) == keccak256(abi.encode(line.expected));
        string memory returned = _returned(r);
        vm.writeLine(
            tsv,
            string.concat(
                vm.toString(set),
                "\t",
                path,
                "\t",
                vm.toString(lineNo),
                "\t",
                vm.toString(line.size),
                "\t",
                f[1],
                "\t",
                returned,
                "\t",
                vm.toString(r.gasUsed)
            )
        );
        if (!line.ok) {
            vm.writeLine(
                failures,
                string.concat(
                    f[0], " expected=", f[1], " returned=", returned, " gas=", vm.toString(r.gasUsed), " file=", path, ":", vm.toString(lineNo)
                )
            );
        }
    }

    function _replay(string memory path, string memory name, uint256 minCases) internal returns (Tally memory t) {
        string memory tsv = _out(name, "", ".tsv");
        string memory failures = _out(name, "failures_", ".txt");
        if (vm.exists(tsv)) vm.removeFile(tsv);
        if (vm.exists(failures)) vm.removeFile(failures);
        uint256 minLength = _minLength();
        t.minGas = type(uint256).max;
        vm.closeFile(path);
        while (true) {
            Line memory l = this.checkLine(path, t.cases + 1, tsv, failures);
            if (l.eof) break;
            t.cases++;
            if (l.expected == 1) t.accepted++;
            if (!l.ok) t.mismatches++;
            t.gasTotal += l.gas;
            if (l.gas < t.minGas) t.minGas = l.gas;
            if (l.gas > t.maxGas) t.maxGas = l.gas;
            if (t.emptyMsgLine == 0 && l.expected == 1 && l.size == minLength) {
                t.emptyMsgLine = t.cases;
                t.emptyMsgGas = l.gas;
            }
        }
        vm.closeFile(path);
        console2.log(artifact);
        _log(path, t);
        assertGe(t.cases, minCases, "fixture has too few cases");
        assertEq(t.mismatches, 0, "opt output != expected verdict");
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
                vm.toString(t.mismatches)
            )
        );
        console2.log(
            string.concat(
                "  gas_total=",
                vm.toString(t.gasTotal),
                " min_gas=",
                vm.toString(t.cases == 0 ? 0 : t.minGas),
                " max_gas=",
                vm.toString(t.maxGas),
                t.emptyMsgLine == 0
                    ? ""
                    : string.concat(
                        " empty_msg_valid_gas=", vm.toString(t.emptyMsgGas), " (line ", vm.toString(t.emptyMsgLine), ")"
                    )
            )
        );
    }

    function test_vectors() public {
        if (!enabled) return;
        if (set == 44) {
            Tally memory t = _replay("fixtures/vectors.txt", "vectors", 48);
            assertEq(t.cases, 48, "47 calldata.txt rows + 1 ACVP row");
        } else {
            string memory path = string.concat("../vectors/mldsa", vm.toString(set), "/calldata.txt");
            _replay(path, "vectors", 57);
        }
    }

    /// @dev The corpus exists for ML-DSA-44 only; one test per category so
    ///      forge runs them in parallel.
    function _category(string memory name) internal returns (Tally memory t) {
        if (!enabled || set != 44) return t;
        t = _replay(string.concat("fixtures/fuzz/", name, ".txt"), name, 1);
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
