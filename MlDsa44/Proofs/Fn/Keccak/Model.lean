import MlDsa44.Proofs.Infra
/-!
# Yul-level model of `keccakF`

Memory and word operations that mirror the EVM semantics of the opcodes the
compiled `keccakF` uses (`MLOAD`, `MSTORE`, `XOR`, `AND`, `OR`, `NOT`, `SHL`,
`SHR`).  The block lemmas state their post-states with these functions, so
`evm_block` normalises both sides of the residual identically.
-/

namespace MlDsa44.Proofs.KeccakModel

open EvmSemantics
open EvmSemantics.EVM

/-- `mload(a)`. -/
def mloadY (M : ByteArray) (a : Nat) : UInt256 := MachineState.readWord M a

/-- `mstore(a, v)`. -/
def mstoreY (M : ByteArray) (a : Nat) (v : UInt256) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded v.toNat 32) a

/-- `or(and(shl(n, x), 0xffffffffffffffff), shr(64 - n, x))`. -/
def rotY (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.lor (UInt256.land (UInt256.shiftLeft x (UInt256.ofNat n))
      (UInt256.ofNat 0xffffffffffffffff))
    (UInt256.shiftRight x (UInt256.ofNat (64 - n)))

/-- `xor(b0, and(not(b1), b2))`. -/
def chiY (b0 b1 b2 : UInt256) : UInt256 :=
  UInt256.xor b0 (UInt256.land (UInt256.lnot b1) b2)

/-- `xor(xor(xor(xor(mload(a0), mload(a1)), mload(a2)), mload(a3)), mload(a4))`. -/
def xor5Y (M : ByteArray) (a0 a1 a2 a3 a4 : Nat) : UInt256 :=
  UInt256.xor (UInt256.xor (UInt256.xor (UInt256.xor (mloadY M a0) (mloadY M a1))
    (mloadY M a2)) (mloadY M a3)) (mloadY M a4)

/-- Theta column parities of the lanes at `src`, stored at `CT`. -/
def thetaY (M : ByteArray) (src : Nat) : ByteArray :=
  let M1 := mstoreY M 0x640 (xor5Y M src (src + 0xa0) (src + 0x140) (src + 0x1e0) (src + 0x280))
  let M2 := mstoreY M1 0x660
    (xor5Y M1 (src + 0x20) (src + 0xc0) (src + 0x160) (src + 0x200) (src + 0x2a0))
  let M3 := mstoreY M2 0x680
    (xor5Y M2 (src + 0x40) (src + 0xe0) (src + 0x180) (src + 0x220) (src + 0x2c0))
  let M4 := mstoreY M3 0x6a0
    (xor5Y M3 (src + 0x60) (src + 0x100) (src + 0x1a0) (src + 0x240) (src + 0x2e0))
  mstoreY M4 0x6c0 (xor5Y M4 (src + 0x80) (src + 0x120) (src + 0x1c0) (src + 0x260) (src + 0x300))

/-- The five chi stores of one output row at `dst`. -/
def chi5Y (M : ByteArray) (dst : Nat) (b0 b1 b2 b3 b4 : UInt256) : ByteArray :=
  let M1 := mstoreY M dst (chiY b0 b1 b2)
  let M2 := mstoreY M1 (dst + 32) (chiY b1 b2 b3)
  let M3 := mstoreY M2 (dst + 64) (chiY b2 b3 b4)
  let M4 := mstoreY M3 (dst + 96) (chiY b3 b4 b0)
  mstoreY M4 (dst + 128) (chiY b4 b0 b1)

/-- Iota: `mstore(dst, xor(mload(dst), mload(rcAddr)))`. -/
def iotaY (M : ByteArray) (dst : Nat) (rcAddr : UInt256) : ByteArray :=
  mstoreY M dst (UInt256.xor (mloadY M dst) (mloadY M rcAddr.toNat))

/-- `add(0x6e0, shl(5, r))`. -/
def rcAddr1 (r : Nat) : UInt256 :=
  UInt256.ofNat 0x6e0 + UInt256.shiftLeft (UInt256.ofNat r) (UInt256.ofNat 5)

/-- `add(0x6e0, shl(5, add(r, 1)))`. -/
def rcAddr2 (r : Nat) : UInt256 :=
  UInt256.ofNat 0x6e0 + UInt256.shiftLeft (UInt256.ofNat r + UInt256.ofNat 1) (UInt256.ofNat 5)

/-- `d := xor(mload(a), rotl1(mload(b)))`. -/
def dY (M : ByteArray) (a b : Nat) : UInt256 := UInt256.xor (mloadY M a) (rotY (mloadY M b) 1)

end MlDsa44.Proofs.KeccakModel
