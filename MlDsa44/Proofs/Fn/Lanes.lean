import MlDsa44.Proofs.Infra
import MlDsa44.Proofs.Fn.Lanes.Bytes
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

-- Gas budgets: exact worst cases, proved by the contracts below.
namespace Gas

def bswap64 : Nat := 122

def loadLE64 : Nat := 170

def storeLE64 : Nat := 167

def xorBlock (rate : Nat) : Nat := 50 + rate / 8 * 285

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
  have : tail.length ≤ 896 := by
    have := hr.depth; simp only [Stack.loadLE64, Stack.bswap64, Stack.leaf] at this; omega
  have := hr.small
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hx : word m p / 2 ^ 192 < 2 ^ 64 := by
    have := Infra.word_lt m p
    omega
  have h1 : Infra.Reach (callState s 2572 (wd p :: wd 0 :: wd ret :: tail) m)
      (callState s 2490 (wd (word m p / 2 ^ 192) :: wd 0 :: wd 2586 :: wd p :: wd 0 :: wd ret :: tail) m) 29 := by
    evm_reach [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608]
  have hcall := Infra.call_iff.mp (bswap64_call hs
    (hr.callee (B' := Stack.bswap64) (ret' := 2586) (extra := [wd p, wd 0, wd ret])
      (by simp [Stack.loadLE64]) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) m hx)
  have h2 : ∀ y, Infra.Reach (callState s 2586 (wd y :: wd p :: wd 0 :: wd ret :: tail) m)
      (callState s ret (wd y :: tail) m) 19 := by
    intro y
    evm_reach [1609, 1610, 1611, 1612, 1613, 1614] with [hr.jumpdest]
  have hval : bswap64 (word m p / 2 ^ 192) = (Crypto.Keccak.readLE64 m p).toNat := by
    rw [Lanes.word_div_eq_beNat8, bswap64, Lanes.readLE64_toNat]
    exact Lanes.bswap_sum_be _ _ _ _ _ _ _ _ _ (Infra.byteAt_lt m p) (Infra.byteAt_lt m (p + 1))
      (Infra.byteAt_lt m (p + 2)) (Infra.byteAt_lt m (p + 3)) (Infra.byteAt_lt m (p + 4))
      (Infra.byteAt_lt m (p + 5)) (Infra.byteAt_lt m (p + 6)) (Infra.byteAt_lt m (p + 7))
      (by simp only [Infra.beNat, Nat.add_zero, Nat.zero_mul, Nat.zero_add]; omega)
  rw [Infra.call_iff, Entry.loadLE64, Gas.loadLE64]
  have h := (h1.trans (hcall.of_eq (by simp [Entry.bswap64]) rfl)).trans (h2 _)
  rw [hval] at h
  exact (h.mono (by norm_num [Gas.bswap64])).of_eq (by simp) (by simp)

theorem storeLE64_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.storeLE64 ret tail) (m : ByteArray) {p x : Nat} (hx : x < 2 ^ 64)
    (hp : p + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', BytesAt m' p (Crypto.Keccak.writeLE64 .empty (UInt64.ofNat x) ++
        ByteArray.mk (Array.replicate 24 0)) ∧
      FrameExcept m m' [(p, p + 32)] ∧
      Call s Entry.storeLE64 [wd p, wd x] ret tail m [] m' Gas.storeLE64 := by
  have : tail.length ≤ 896 := by
    have := hr.depth; simp only [Stack.storeLE64, Stack.bswap64, Stack.leaf] at this; omega
  have := hr.small
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hy : bswap64 x < 2 ^ 64 := by
    rw [bswap64, Lanes.bswap_sum_eq]; omega
  let m' := MachineState.writeBytes m (Data.Bytes.natToBytesPadded (bswap64 x * 2 ^ 192) 32) p
  have h1 : Infra.Reach (callState s 2597 (wd p :: wd x :: wd ret :: tail) m)
      (callState s 2490 (wd x :: wd 0 :: wd 2607 :: wd p :: wd x :: wd ret :: tail) m) 20 := by
    evm_reach [1618, 1619, 1620, 1621, 1622, 1623]
  have hcall := Infra.call_iff.mp (bswap64_call hs
    (hr.callee (B' := Stack.bswap64) (ret' := 2607) (extra := [wd p, wd x, wd ret])
      (by simp [Stack.storeLE64]) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) m hx)
  have h2 : ∀ y, y < 2 ^ 64 →
      Infra.Reach (callState s 2607 (wd y :: wd p :: wd x :: wd ret :: tail) m)
        (callState s ret tail
          (MachineState.writeBytes m (Data.Bytes.natToBytesPadded (y * 2 ^ 192) 32) p)) 25 := by
    intro y hy
    evm_reach [1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631] with [hr.jumpdest]
  refine ⟨m', fun i hi => ?_, Infra.FrameExcept.mstore m p _, ?_⟩
  · rw [Lanes.writeLE64_pad_size x hx] at hi
    rw [Infra.byteAt_writeBytes, if_pos (by rw [Infra.natToBytesPadded_size]; omega),
      Nat.add_sub_cancel_left, Lanes.byteAt_natToBytesPadded _ _ hi,
      Lanes.writeLE64_pad_getElem x hx i hi, bswap64]
    simp only [Nat.reducePow]
    exact Lanes.bswap_store_byte x i hi
  · rw [Infra.call_iff, Entry.storeLE64, Gas.storeLE64]
    have h := (h1.trans (hcall.of_eq (by simp [Entry.bswap64]) rfl)).trans (h2 _ hy)
    exact (h.mono (by norm_num [Gas.bswap64])).of_eq (by simp) rfl

theorem xorBlock_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.xorBlock ret tail) {m : ByteArray} {rate p : Nat} {A : Array UInt64}
    (hrate : rate = 136 ∨ rate = 168) (hA : LanesAt m ST A)
    (hp : RC ≤ p) (hmem : p + rate + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ m', LanesAt m' ST (Fips202.xorBlock rate m p A) ∧
      FrameExcept m m' [(ST, ST + 32 * (rate / 8))] ∧
      Call s Entry.xorBlock [wd rate, wd p] ret tail m [] m' (Gas.xorBlock rate) := by
  have : tail.length ≤ 832 := by
    have := hr.depth
    simp only [Stack.xorBlock, Stack.loadLE64, Stack.bswap64, Stack.leaf] at this; omega
  have := hr.small
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  simp only [RC] at hp
  have hn : rate / 8 ≤ 21 := by omega
  have hrate' : rate < 256 := by omega
  let v : Nat → Nat := fun k =>
    word m (k * 32) ^^^ (Crypto.Keccak.readLE64 m (p + k * 8)).toNat
  let mem : Nat → ByteArray := Infra.storeWords m 0 v
  let I : Nat → State := fun j =>
    callState s 2623 (wd j :: wd rate :: wd p :: wd ret :: tail) (mem j)
  have hentry : Infra.Reach (callState s 2621 (wd rate :: wd p :: wd ret :: tail) m) (I 0) 3 := by
    simp only [I, mem, Infra.storeWords_zero]
    evm_reach [1635, 1636]
  have hb1 : ∀ j M, j < rate / 8 →
      Infra.Reach (callState s 2623 (wd j :: wd rate :: wd p :: wd ret :: tail) M)
        (callState s 2572 (wd (p + j * 8) :: wd 0 :: wd 2653 :: wd (j * 32) :: wd j :: wd rate ::
          wd p :: wd ret :: tail) M) 72 := by
    intro j M hj
    evm_reach [1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657]
  have hb2 : ∀ j M w, j < rate / 8 → w < 2 ^ 64 →
      Infra.Reach (callState s 2653 (wd w :: wd (j * 32) :: wd j :: wd rate :: wd p :: wd ret ::
          tail) M)
        (callState s 2623 (wd (j + 1) :: wd rate :: wd p :: wd ret :: tail)
          (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (word M (j * 32) ^^^ w) 32)
            (j * 32))) 43 := by
    intro j M w hj hw
    have hxor : (word M (j * 32) ^^^ w) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        word M (j * 32) ^^^ w :=
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Infra.word_lt M _) (by omega))
    evm_reach [1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671] with [hxor]
  have hexit : ∀ M, Infra.Reach
      (callState s 2623 (wd (rate / 8) :: wd rate :: wd p :: wd ret :: tail) M)
      (callState s ret tail M) 47 := by
    intro M
    evm_reach [1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1672, 1673, 1674, 1675, 1676] with [hr.jumpdest]
  have hframe : ∀ j, FrameExcept m (mem j) [(0, 0 + 32 * j)] := Infra.FrameExcept.storeWords m 0 v
  have hbody : ∀ j, j < rate / 8 → Infra.Reach (I j) (I (j + 1)) 285 := by
    intro j hj
    have hread : Crypto.Keccak.readLE64 (mem j) (p + j * 8) =
        Crypto.Keccak.readLE64 m (p + j * 8) :=
      Lanes.readLE64_congr fun k hk =>
        Infra.FrameExcept.byteAt (hframe j)
          (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega)
    have hword : word (mem j) (j * 32) = word m (j * 32) :=
      Infra.FrameExcept.word (hframe j)
        (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega)
    have hcall := Infra.call_iff.mp (loadLE64_call hs
      (hr.callee (B' := Stack.loadLE64) (ret' := 2653)
        (extra := [wd (j * 32), wd j, wd rate, wd p, wd ret])
        (by simp [Stack.xorBlock]) (by simp) (by simp only [Infra.isValidJumpDest_lit])
        (by norm_num))
      (mem j) (p := p + j * 8) (by omega))
    rw [hread] at hcall
    have h := ((hb1 j (mem j) hj).trans (hcall.of_eq (by simp [Entry.loadLE64]) rfl)).trans
      (hb2 j (mem j) _ hj (UInt64.toNat_lt _))
    rw [hword] at h
    refine (h.mono (by norm_num [Gas.loadLE64])).of_eq rfl ?_
    simp only [I, mem]
    rw [Infra.storeWords_succ, Nat.zero_add]
  have hall := (hentry.trans (Infra.Reach.loop (rate / 8) hbody)).trans (hexit (mem (rate / 8)))
  refine ⟨mem (rate / 8), ⟨?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [Fips202.xorBlock, Lanes.xorBlock_fold_size]; exact hA.1
  · have hAi := hA.2 i hi
    simp only [ST, Nat.zero_add] at hAi ⊢
    rw [Fips202.xorBlock, Lanes.xorBlock_fold_getElem _ _ _ (by rw [hA.1]; omega)]
    split
    · rename_i hin
      have hv : v i < 2 ^ 256 :=
        Nat.xor_lt_two_pow (Infra.word_lt _ _)
          (by have := UInt64.toNat_lt (Crypto.Keccak.readLE64 m (p + i * 8)); omega)
      have := Infra.word_storeWords (m := m) (base := 0) (v := v) hv (rate / 8) hin
      rw [Nat.zero_add] at this
      rw [this, UInt64.toNat_xor, ← hAi]
      simp only [v]
      rw [show i * 32 = 32 * i by omega, show p + i * 8 = p + 8 * i by omega]
    · rw [Infra.FrameExcept.word (hframe (rate / 8))
        (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega), hAi]
  · simpa [ST] using hframe (rate / 8)
  · rw [Infra.call_iff, Entry.xorBlock, Gas.xorBlock]
    exact (hall.mono (by omega)).of_eq (by simp) (by simp)

end MlDsa44.Proofs
