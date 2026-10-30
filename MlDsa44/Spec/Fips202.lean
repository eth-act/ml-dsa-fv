import EvmSemantics.Crypto.Keccak256
set_option warningAsError true
/-!
# FIPS 202 SHAKE128 / SHAKE256

Byte-oriented SHAKE built on the Keccak-f[1600] permutation of the pinned EVM
semantics (`EvmSemantics.Crypto.Keccak.permute`, lanes little-endian via
`readLE64`). Only the sponge driver below is new trusted code:

* padding: the SHAKE domain bits `1111` followed by `pad10*1`, which at byte
  granularity is `0x1F` at the first free byte and `0x80` or-ed into the last
  byte of the final block (FIPS 202 §6.2, Appendix B.2);
* absorb: xor each `rate`-byte block into the first `rate / 8` lanes, permute;
* squeeze: emit the first `rate` bytes of the state, permute, repeat.
-/

namespace MlDsa44.Fips202

open EvmSemantics.Crypto

/-- Sponge state: 25 little-endian 64-bit lanes. -/
abbrev SpongeState := Array UInt64

def emptyState : SpongeState := Array.replicate 25 0

/-- `msg ‖ suffix ‖ 0* ‖ 0x80`, padded to a positive multiple of `rate`. When
only one byte is free the suffix and the final bit share it. -/
def pad (rate : Nat) (suffix : UInt8) (msg : ByteArray) : ByteArray :=
  let padLen := rate - msg.size % rate
  let p := (ByteArray.mk (Array.replicate padLen 0)).set! 0 suffix
  msg ++ p.set! (padLen - 1) (p[padLen - 1]! ||| 0x80)

/-- Xor the block `bytes[off, off + rate)` into the first `rate / 8` lanes. -/
def xorBlock (rate : Nat) (bytes : ByteArray) (off : Nat) (st : SpongeState) :
    SpongeState :=
  (List.range (rate / 8)).foldl
    (fun st j => st.set! j (st[j]! ^^^ Keccak.readLE64 bytes (off + 8 * j))) st

/-- Xor the block `bytes[off, off + rate)` into the state and permute. -/
def absorbBlock (rate : Nat) (bytes : ByteArray) (st : SpongeState) (off : Nat) :
    SpongeState :=
  Keccak.permute (xorBlock rate bytes off st)

/-- Absorb an already padded byte string. -/
def absorb (rate : Nat) (padded : ByteArray) : SpongeState :=
  (List.range (padded.size / rate)).foldl
    (fun st i => absorbBlock rate padded st (i * rate)) emptyState

/-- The first `rate` bytes of the state. -/
def stateBytes (rate : Nat) (st : SpongeState) : ByteArray :=
  (List.range (rate / 8)).foldl (fun out j => Keccak.writeLE64 out st[j]!) .empty

/-- Squeeze `blocks` full output blocks. -/
def squeeze (rate : Nat) : SpongeState → Nat → ByteArray
  | _, 0 => .empty
  | st, blocks + 1 => stateBytes rate st ++ squeeze rate (Keccak.permute st) blocks

/-- SHAKE with the given rate in bytes: the first `outLen` output bytes. -/
def shake (rate : Nat) (msg : ByteArray) (outLen : Nat) : ByteArray :=
  (squeeze rate (absorb rate (pad rate 0x1F msg)) ((outLen + rate - 1) / rate)).extract
    0 outLen

/-- SHAKE128, rate 168 bytes. -/
def shake128 (msg : ByteArray) (outLen : Nat) : ByteArray := shake 168 msg outLen

/-- SHAKE256, rate 136 bytes. -/
def shake256 (msg : ByteArray) (outLen : Nat) : ByteArray := shake 136 msg outLen

end MlDsa44.Fips202
