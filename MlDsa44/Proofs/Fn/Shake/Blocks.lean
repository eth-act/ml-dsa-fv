import MlDsa44.Proofs.Fn.Shake.Evm
set_option warningAsError true
/-!
# Straight-line blocks of `shake` (instructions 1680‥1874)

Stack names: `A = rate :: ptr :: len :: out :: blocks :: ret :: tail` (the
arguments), absorb loop `b :: full :: A`, padding `rem :: full :: A`, squeeze
`b :: last :: rem :: full :: A`, lane loop `j :: o :: b :: last :: rem :: full :: A`.
-/

namespace MlDsa44.Proofs.Shake

open EvmSemantics
open EvmSemantics.EVM

/-- Memory after `mstore8(PADB + rem, 0x1f)`. -/
def padMem3 (M : ByteArray) (rem : Nat) : ByteArray :=
  MachineState.writeBytes M (ByteArray.mk #[UInt8.ofNat 31]) (78464 + rem)

/-- Memory after `mstore8(last, or(byte(0, mload(last)), 0x80))`. -/
def padMem4 (M : ByteArray) (rem rate : Nat) : ByteArray :=
  MachineState.writeBytes (padMem3 M rem)
    (ByteArray.mk #[UInt8.ofNat ((byteAt (padMem3 M rem) (78464 + (rate - 1)) ||| 128) % 256)])
    (78464 + (rate - 1))

theorem byte_or_mod (m : ByteArray) (a : Nat) :
    (byteAt m a ||| 128) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      byteAt m a ||| 128 := by
  apply Nat.mod_eq_of_lt
  have := Infra.byteAt_lt m a
  have : byteAt m a ||| 128 < 2 ^ 8 := Nat.or_lt_two_pow (by omega) (by norm_num)
  omega

section
variable {s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 768)
  (hfw : 2535 ≤ s.activeWords.toNat) (haw : s.activeWords.toNat ≤ 18446744073709551616)
  {rate ptr len out blocks ret : Nat} (hrate : 0 < rate ∧ rate < 256) (hlen : len < 2 ^ 128)
  (hblk : blocks ≤ 6)
include hs htail

theorem b_entry (m : ByteArray) :
    Infra.Reach
      (callState s 2680 (wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) m)
      (callState s 2682
        (wd 0 :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) m) 3 := by
  evm_reach [1680, 1681]

include hfw haw in
theorem b_zero (m : ByteArray) (i : Nat) (hi : i < 25) :
    Infra.Reach
      (callState s 2682
        (wd i :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
        (Infra.storeWords m 0 (fun _ => 0) i))
      (callState s 2682
        (wd (i + 1) :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
        (Infra.storeWords m 0 (fun _ => 0) (i + 1))) 65 := by
  evm_reach [1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700]
    with [Infra.storeWords_succ, Nat.zero_add]

include hrate hlen in
theorem b_zeroExit (M : ByteArray) :
    Infra.Reach
      (callState s 2682
        (wd 25 :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2714 (wd 0 :: wd (len / rate) ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 42 := by
  evm_reach [1682, 1683, 1684, 1685, 1686, 1687, 1688, 1701, 1702, 1703, 1704, 1705, 1706]
    with [Infra.ofNat_div_ofNat]

include hlen in
theorem b_absorb1 (M : ByteArray) {b full : Nat} (hb : b < full) (hfull : full ≤ len) :
    Infra.Reach
      (callState s 2714 (wd b :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2621 (wd rate :: wd (ptr + b * rate) :: wd 2736 :: wd b :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 60 := by
  evm_reach [1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722]

theorem b_absorb2 (M : ByteArray) (b full : Nat) :
    Infra.Reach
      (callState s 2736 (wd b :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 4 (wd 2744 :: wd b :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 15 := by
  evm_reach [1723, 1724, 1725, 1726]

theorem b_absorb3 (M : ByteArray) (b full : Nat) :
    Infra.Reach
      (callState s 2744 (wd b :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2714 (wd (b + 1) :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 26 := by
  evm_reach [1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734]

include hlen in
theorem b_absorbExit (M : ByteArray) {full : Nat} (hfr : full * rate ≤ len) (hfull : full ≤ len) :
    Infra.Reach
      (callState s 2714 (wd full :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2763 (wd 0 :: wd (len - full * rate) :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 48 := by
  evm_reach [1707, 1708, 1709, 1710, 1711, 1712, 1713, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742]

include hfw haw in
theorem b_padZero (m : ByteArray) (rem full : Nat) (i : Nat) (hi : i < 6) :
    Infra.Reach
      (callState s 2763 (wd i :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
        (Infra.storeWords m 78464 (fun _ => 0) i))
      (callState s 2763 (wd (i + 1) :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
        (Infra.storeWords m 78464 (fun _ => 0) (i + 1))) 71 := by
  evm_reach [1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763]
    with [Infra.storeWords_succ]

theorem b_padExit (M : ByteArray) (rem full : Nat) :
    Infra.Reach
      (callState s 2763 (wd 6 :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2806 (wd 78464 :: wd (ptr + full * rate) :: wd rem :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 52 := by
  evm_reach [1743, 1744, 1745, 1746, 1747, 1748, 1749, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772]

include hfw haw hrate in
theorem b_padBytes (M : ByteArray) (rem full : Nat) (hrem : rem < rate) :
    Infra.Reach
      (callState s 2807 (wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2621 (wd rate :: wd 78464 :: wd 2846 :: wd (78464 + (rate - 1)) :: wd rem ::
        wd full :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
        (padMem4 M rem rate)) 73 := by
  evm_reach [1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796]
    with [padMem4, padMem3, byte0_word, byte_or_mod]

theorem b_pad2 (M : ByteArray) (last rem full : Nat) :
    Infra.Reach
      (callState s 2846 (wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 4 (wd 2854 :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 15 := by
  evm_reach [1797, 1798, 1799, 1800]

theorem b_pad3 (M : ByteArray) (last rem full : Nat) :
    Infra.Reach
      (callState s 2854 (wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2856 (wd 0 :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 3 := by
  evm_reach [1801, 1802]

include hblk in
theorem b_sq0 (M : ByteArray) (last rem full : Nat) (hb : 0 < blocks) :
    Infra.Reach
      (callState s 2856 (wd 0 :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2886 (wd 0 :: wd out :: wd 0 :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 65 := by
  evm_reach [1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1818, 1819, 1820, 1821, 1822, 1823, 1824]
    with [Nat.zero_mul, Nat.add_zero]

include hblk in
theorem b_sq1 (M : ByteArray) (last rem full b : Nat) (hb0 : 0 < b) (hb : b < blocks) :
    Infra.Reach
      (callState s 2856 (wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 4 (wd 2878 :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 59 := by
  evm_reach [1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816]

theorem b_sq2 (M : ByteArray) (last rem full b : Nat) :
    Infra.Reach
      (callState s 2878 (wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2886 (wd 0 :: wd (out + b * rate) :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 21 := by
  evm_reach [1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824]

include hfw haw hrate in
theorem b_lane1 (M : ByteArray) (last rem full b o j : Nat) (hj : j < rate / 8) :
    Infra.Reach
      (callState s 2886 (wd j :: wd o :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2597 (wd (o + j * 8) :: wd (word M (j * 32)) :: wd 2916 ::
        wd j :: wd o :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 73 := by
  evm_reach [1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845]

theorem b_lane2 (M : ByteArray) (last rem full b o j : Nat) :
    Infra.Reach
      (callState s 2916 (wd j :: wd o :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2886 (wd (j + 1) :: wd o :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 26 := by
  evm_reach [1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853]

include hrate in
theorem b_laneExit (M : ByteArray) (last rem full b o : Nat) :
    Infra.Reach
      (callState s 2886 (wd (rate / 8) :: wd o :: wd b :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s 2856 (wd (b + 1) :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M) 62 := by
  evm_reach [1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863]

include hblk in
theorem b_exit (M : ByteArray) (last rem full : Nat) (hr : RetOK Stack.shake ret tail) :
    Infra.Reach
      (callState s 2856 (wd blocks :: wd last :: wd rem :: wd full ::
        wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
      (callState s ret tail M) 53 := by
  have := hr.small
  have := hblk
  evm_reach [1803, 1804, 1805, 1806, 1807, 1808, 1809, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874]
    with [hr.jumpdest]

end

end MlDsa44.Proofs.Shake
