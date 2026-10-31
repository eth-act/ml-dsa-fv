// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {XCheckBase} from "./XCheckBase.sol";
import {GasProbe} from "../src/GasProbe.sol";
import {LeanArtifact} from "../src/LeanArtifact.sol";

/// @notice The bytes executed by every other test are the proved artifact.
contract ArtifactTest is XCheckBase {
    /// @dev keccak256 of MlDsa44/Reference/reference.hex (5289 bytes) at the
    ///      time of the cross-check; a changed artifact must be a deliberate
    ///      update of this constant and of every fixture.
    bytes32 internal constant PINNED_KECCAK = 0x44c18b2d33b4d7eeab3e7e0204c20896be8c06985e5dadc8852c06e5df476d44;
    uint256 internal constant PINNED_SIZE = 5289;

    function test_deployed_runtime_is_reference_hex() public view {
        bytes memory fromHex = LeanArtifact.parseHex(vm.readFile(string.concat(LeanArtifact.DIR, "/reference.hex")));
        assertEq(REFERENCE.code.length, fromHex.length, "runtime size");
        assertEq(keccak256(REFERENCE.code), keccak256(fromHex), "runtime keccak != keccak(reference.hex)");
        assertEq(REFERENCE.codehash, keccak256(fromHex), "EXTCODEHASH != keccak(reference.hex)");
        assertEq(keccak256(fromHex), PINNED_KECCAK, "reference.hex changed");
        assertEq(fromHex.length, PINNED_SIZE, "reference.hex size");
    }

    /// @dev `load` already requires this; asserted again for the report.
    function test_reference_hex_is_lean_literal() public view {
        (bytes memory literal, uint256 chunks) =
            LeanArtifact.parseLeanLiteral(vm.readFile(string.concat(LeanArtifact.DIR, "/Bytes.lean")));
        assertEq(keccak256(literal), PINNED_KECCAK, "Bytes.lean literal != reference.hex");
        assertEq(chunks, 6, "chunk count");
        assertEq(pin.provedSize, PINNED_SIZE, "referenceBytes_size");
    }

    /// @dev A real CREATE of `initcode ‖ runtime` (not a cheatcode etch) yields
    ///      the same runtime bytes, so the artifact is deployable as-is
    ///      (EIP-170 size limit, EIP-3541 no 0xEF prefix), and behaves and costs
    ///      exactly the same at the CREATE address.
    function test_create_deployment_is_identical() public {
        bytes memory code = pin.code;
        bytes memory initcode = abi.encodePacked(
            hex"61", uint16(code.length), hex"80600a5f395ff3", code
        );
        address deployed;
        assembly {
            deployed := create(0, add(initcode, 0x20), mload(initcode))
        }
        assertTrue(deployed != address(0), "CREATE failed");
        assertEq(deployed.codehash, PINNED_KECCAK, "CREATE runtime != reference.hex");

        string memory path = "fixtures/vectors.txt";
        vm.closeFile(path);
        for (uint256 i = 0; i < 6; i++) {
            string[] memory f = vm.split(vm.readLine(path), " ");
            bytes memory cd = vm.parseBytes(string.concat("0x", f[0]));
            GasProbe.Result memory a = GasProbe.probe(REFERENCE, cd);
            GasProbe.Result memory b = GasProbe.probe(deployed, cd);
            assertTrue(a.ok && b.ok, "call failed");
            assertEq(b.ret, a.ret, "output differs at CREATE address");
            assertEq(b.gasUsed, a.gasUsed, "gas differs at CREATE address");
            assertEq(b.gasUsed, vm.parseUint(f[2]), "gas != Lean");
        }
        vm.closeFile(path);
    }

    /// @dev The code reads no state; its gas must not depend on the account's
    ///      storage or balance (the Lean frame starts with an empty account).
    function test_gas_is_state_independent() public {
        string memory path = "fixtures/vectors.txt";
        vm.closeFile(path);
        string[] memory f = vm.split(vm.readLine(path), " ");
        vm.closeFile(path);
        bytes memory cd = vm.parseBytes(string.concat("0x", f[0]));
        GasProbe.Result memory clean = GasProbe.probe(REFERENCE, cd);
        vm.store(REFERENCE, bytes32(0), bytes32(uint256(0xdeadbeef)));
        vm.deal(REFERENCE, 1 ether);
        GasProbe.Result memory dirty = GasProbe.probe(REFERENCE, cd);
        assertEq(dirty.gasUsed, clean.gasUsed, "gas depends on state");
        assertEq(dirty.ret, clean.ret, "output depends on state");
        assertEq(clean.gasUsed, vm.parseUint(f[2]), "gas != Lean");
    }

    /// @dev A plain CALL (with value) and a STATICCALL see the same frame: the
    ///      verifier is pure, so the proved behaviour carries over to both.
    function test_call_and_staticcall_agree() public {
        string memory path = "fixtures/vectors.txt";
        vm.closeFile(path);
        string[] memory f = vm.split(vm.readLine(path), " ");
        vm.closeFile(path);
        bytes memory cd = vm.parseBytes(string.concat("0x", f[0]));
        vm.deal(address(this), 1 ether);
        (bool ok1, bytes memory r1) = REFERENCE.call{value: 1}(cd);
        (bool ok2, bytes memory r2) = REFERENCE.staticcall(cd);
        assertTrue(ok1 && ok2, "call failed");
        assertEq(r1, r2, "CALL and STATICCALL differ");
        assertEq(r1, _word(1), "valid vector rejected");
    }
}
