import MlDsa44.Proofs.Infra
/-!
# Lane codecs: `bswap64`, `loadLE64`, `storeLE64`, `xorBlock`

Yul:
* `bswap64(x) -> y`: byte reversal of a 64-bit value (three mask/shift steps);
* `loadLE64(p) -> w := bswap64(shr(192, mload(p)))`;
* `storeLE64(p, w)`: `mstore(p, shl(192, bswap64(w)))`, i.e. eight
  little-endian bytes followed by 24 zero bytes;
* `xorBlock(rate, p)`: lanes `j < rate / 8` of `ST` xor `loadLE64(p + 8 j)`.
-/

namespace MlDsa44.Proofs

open EvmSemantics
open EvmSemantics.EVM

-- Gas budget: upper bound proved by the contracts below; set it to the exact
-- worst case once proved.
namespace Gas

def bswap64 : Nat := 122

def loadLE64 : Nat := 180

def storeLE64 : Nat := 180

def xorBlock (rate : Nat) : Nat := 200 + rate / 8 * 300

end Gas

/-- Byte reversal of the low 8 bytes of `x`. -/
def bswap64 (x : Nat) : Nat :=
  ((List.range 8).map fun i => x / 256 ^ i % 256 * 256 ^ (7 - i)).sum

theorem bswap64_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.bswap64 ret tail) (m : ByteArray) {x : Nat} (hx : x < 2 ^ 64) :
    Call s Entry.bswap64 [wd x] ret tail m [wd (bswap64 x)] m Gas.bswap64 := by
  have : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.bswap64, Stack.leaf] at this; omega
  have := hr.small
  rw [Infra.call_iff, Entry.bswap64, Gas.bswap64]
  evm_reach [1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596]
    with [hr.jumpdest, bswap64, Infra.bswap_masks]

theorem loadLE64_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.loadLE64 ret tail) (m : ByteArray) {p : Nat}
    (hp : p + 32 ≤ 32 * s.activeWords.toNat) :
    Call s Entry.loadLE64 [wd p] ret tail m
      [wd (Crypto.Keccak.readLE64 m p).toNat] m Gas.loadLE64 := by
  sorry

theorem storeLE64_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.storeLE64 ret tail) (m : ByteArray) {p x : Nat} (hx : x < 2 ^ 64)
    (hp : p + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', BytesAt m' p (Crypto.Keccak.writeLE64 .empty (UInt64.ofNat x) ++
        ByteArray.mk (Array.replicate 24 0)) ∧
      FrameExcept m m' [(p, p + 32)] ∧
      Call s Entry.storeLE64 [wd p, wd x] ret tail m [] m' Gas.storeLE64 := by
  sorry

theorem xorBlock_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.xorBlock ret tail) {m : ByteArray} {rate p : Nat} {A : Array UInt64}
    (hrate : rate = 136 ∨ rate = 168) (hA : LanesAt m ST A)
    (hp : RC ≤ p) (hmem : p + rate + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', LanesAt m' ST (Fips202.xorBlock rate m p A) ∧
      FrameExcept m m' [(ST, ST + 32 * (rate / 8))] ∧
      Call s Entry.xorBlock [wd rate, wd p] ret tail m [] m' (Gas.xorBlock rate) := by
  sorry

end MlDsa44.Proofs
