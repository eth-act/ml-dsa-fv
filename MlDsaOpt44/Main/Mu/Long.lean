import MlDsaOpt44.Main.Mu.Blocks
import MlDsaOpt44.Main.Mu.Spec
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
/-!
# `seg_mu` (v4) straight-line blocks

Dispatch on `|M| ≤ 69`, the short path (`MU` replicated into `FIN`), the
long path's setup (copy of `SC` to `KS`, the call of `cext`, the replication
of the extracted lanes for `kf1`, block 1's `absorb17`), the `kf1` / `absorb17`
loop, the padding of the last block and the copy of μ's lanes to `FIN`.
-/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- Lanes `[a, b)` of `KS` replicated for `kf1` (`MUL` by `REP`, `NOT` on the
complemented lanes), nothing else changed. -/
def RepStep (M M' : ByteArray) (a b : Nat) : Prop :=
  (∀ x, a ≤ x → x < b → word M' (KS + 32 * x) = rep (cpl x (word M (KS + 32 * x)))) ∧
    FrameExcept M M' [(KS + 32 * a, KS + 32 * b)]

theorem RepStep.trans {M M1 M2 : ByteArray} {a b c : Nat} (h1 : RepStep M M1 a b)
    (h2 : RepStep M1 M2 b c) (hab : a ≤ b) (hbc : b ≤ c) : RepStep M M2 a c := by
  refine ⟨fun x hx1 hx2 => ?_, (h1.2.trans h2.2).mono ?_⟩
  · by_cases hx : x < b
    · rw [FrameExcept.word h2.2 (by simp only [avoids_cons, avoids_nil, and_true]; omega),
        h1.1 x hx1 hx]
    · rw [h2.1 x (by omega) hx2,
        FrameExcept.word h1.2 (by simp only [avoids_cons, avoids_nil, and_true]; omega)]
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨(KS + 32 * a, KS + 32 * c), by simp, ?_⟩
    rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem mu_chk_long {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 3802 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 5075 [flag b] M) (callState s 5369 [flag b] M) 24 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1601, 1602, 1603, 1604, 1605, 1606]

theorem mu_short {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hsh : s.executionEnv.calldata.size < 3802)
    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5075 [flag b] M) (callState s 5876 [flag b] M') 195 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h0 : word M 65024 < 2 ^ 64 := by simpa [MU] using hU 0 (by omega)
  have h1 : word M 65056 < 2 ^ 64 := by simpa [MU] using hU 1 (by omega)
  have h2 : word M 65088 < 2 ^ 64 := by simpa [MU] using hU 2 (by omega)
  have h3 : word M 65120 < 2 ^ 64 := by simpa [MU] using hU 3 (by omega)
  have h4 : word M 65152 < 2 ^ 64 := by simpa [MU] using hU 4 (by omega)
  have h5 : word M 65184 < 2 ^ 64 := by simpa [MU] using hU 5 (by omega)
  have h6 : word M 65216 < 2 ^ 64 := by simpa [MU] using hU 6 (by omega)
  have h7 : word M 65248 < 2 ^ 64 := by simpa [MU] using hU 7 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt44_reach [1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [FIN, MU, Nat.reduceMul, Nat.reduceAdd] <;> chain_facts <;>
      simp only [rep_lit']
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_cpy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5369 [flag b] M) (callState s 5377 [wd KS, wd SC, wd 800, flag b] M) 9 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1657, 1658, 1659, 1660] with [KS, SC]

theorem mu_cext_pre {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5378 [flag b] M)
      (callState s 12151 [wd 25, wd 1, wd KS, wd 5391, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1662, 1663, 1664, 1665, 1666, 1667, 1668] with [KS]

set_option maxRecDepth 10000 in
theorem mu_repA {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, 0 ≤ x → x < 7 → word M (KS + 32 * x) < 2 ^ 64) :
    ∃ M', RepStep M M' 0 7 ∧
      Reach (callState s 5391 [flag b] M) (callState s 5474 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 148 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h0 : word M 0 < 2 ^ 64 := by simpa [KS] using hT 0 (by omega) (by omega)
  have h1 : word M 32 < 2 ^ 64 := by simpa [KS] using hT 1 (by omega) (by omega)
  have h2 : word M 64 < 2 ^ 64 := by simpa [KS] using hT 2 (by omega) (by omega)
  have h3 : word M 96 < 2 ^ 64 := by simpa [KS] using hT 3 (by omega) (by omega)
  have h4 : word M 128 < 2 ^ 64 := by simpa [KS] using hT 4 (by omega) (by omega)
  have h5 : word M 160 < 2 ^ 64 := by simpa [KS] using hT 5 (by omega) (by omega)
  have h6 : word M 192 < 2 ^ 64 := by simpa [KS] using hT 6 (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  rotate_left 3
  · opt44_reach [1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714] with [word_mstore_disjoint]
  · intro x h1 h2
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] <;> chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals simp [cpl, complemented]
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

set_option maxRecDepth 10000 in
theorem mu_repB {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, 7 ≤ x → x < 14 → word M (KS + 32 * x) < 2 ^ 64) :
    ∃ M', RepStep M M' 7 14 ∧
      Reach (callState s 5474 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5544 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 146 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h7 : word M 224 < 2 ^ 64 := by simpa [KS] using hT 7 (by omega) (by omega)
  have h8 : word M 256 < 2 ^ 64 := by simpa [KS] using hT 8 (by omega) (by omega)
  have h9 : word M 288 < 2 ^ 64 := by simpa [KS] using hT 9 (by omega) (by omega)
  have h10 : word M 320 < 2 ^ 64 := by simpa [KS] using hT 10 (by omega) (by omega)
  have h11 : word M 352 < 2 ^ 64 := by simpa [KS] using hT 11 (by omega) (by omega)
  have h12 : word M 384 < 2 ^ 64 := by simpa [KS] using hT 12 (by omega) (by omega)
  have h13 : word M 416 < 2 ^ 64 := by simpa [KS] using hT 13 (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  rotate_left 3
  · opt44_reach [1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758] with [word_mstore_disjoint]
  · intro x h1 h2
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] <;> chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals simp [cpl, complemented]
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

set_option maxRecDepth 10000 in
theorem mu_repC {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, 14 ≤ x → x < 20 → word M (KS + 32 * x) < 2 ^ 64) :
    ∃ M', RepStep M M' 14 20 ∧
      Reach (callState s 5544 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5605 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 123 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h14 : word M 448 < 2 ^ 64 := by simpa [KS] using hT 14 (by omega) (by omega)
  have h15 : word M 480 < 2 ^ 64 := by simpa [KS] using hT 15 (by omega) (by omega)
  have h16 : word M 512 < 2 ^ 64 := by simpa [KS] using hT 16 (by omega) (by omega)
  have h17 : word M 544 < 2 ^ 64 := by simpa [KS] using hT 17 (by omega) (by omega)
  have h18 : word M 576 < 2 ^ 64 := by simpa [KS] using hT 18 (by omega) (by omega)
  have h19 : word M 608 < 2 ^ 64 := by simpa [KS] using hT 19 (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  rotate_left 3
  · opt44_reach [1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795] with [word_mstore_disjoint]
  · intro x h1 h2
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] <;> chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals simp [cpl, complemented]
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

set_option maxRecDepth 10000 in
theorem mu_repD {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, 20 ≤ x → x < 25 → word M (KS + 32 * x) < 2 ^ 64) :
    ∃ M', RepStep M M' 20 25 ∧
      Reach (callState s 5605 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5657 [flag b] M') 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h20 : word M 640 < 2 ^ 64 := by simpa [KS] using hT 20 (by omega) (by omega)
  have h21 : word M 672 < 2 ^ 64 := by simpa [KS] using hT 21 (by omega) (by omega)
  have h22 : word M 704 < 2 ^ 64 := by simpa [KS] using hT 22 (by omega) (by omega)
  have h23 : word M 736 < 2 ^ 64 := by simpa [KS] using hT 23 (by omega) (by omega)
  have h24 : word M 768 < 2 ^ 64 := by simpa [KS] using hT 24 (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  rotate_left 3
  · opt44_reach [1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827] with [word_mstore_disjoint]
  · intro x h1 h2
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] <;> chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals simp [cpl, complemented]
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem mu_abs1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5657 [flag b] M)
      (callState s 6644 [wd 3802, wd 5668, wd 3802, flag b] M) 20 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1828, 1829, 1830, 1831, 1832]

theorem mu_head0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 3802 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 5668 [wd 3802, flag b] M)
      (callState s 5677 [wd (s.executionEnv.calldata.size - 3802), wd 3938, flag b] M) 15 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1833, 1834, 1835, 1836, 1837, 1838]

theorem mu_loop1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5677 [wd len, wd off, flag b] M)
      (callState s 20535 [wd 5693, wd len, wd off, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847]

theorem mu_loop2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} :
    Reach (callState s 5693 [wd len, wd off, flag b] M)
      (callState s 6644 [wd off, wd 5703, wd off, wd len, flag b] M) 21 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1848, 1849, 1850, 1851, 1852, 1853]

theorem mu_loop3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5703 [wd off, wd len, flag b] M)
      (callState s 5677 [wd (len - 136), wd (136 + off), flag b] M) 30 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862]

theorem mu_exit {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : len < 136) :
    Reach (callState s 5677 [wd len, wd off, flag b] M)
      (callState s 5716 [wd len, wd off, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1839, 1840, 1841, 1842, 1843, 1844]

theorem mu_copy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) =
        if x = 1 ∨ x = 2 then 2 ^ 256 - 1 - word M (KS + 32 * x) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5818 [flag b] M) (callState s 5876 [flag b] M') 102 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt44_reach [1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [FIN, KS, Nat.reduceMul, Nat.reduceAdd] <;> chain_facts
    all_goals norm_num
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_pad {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} (hlen : len < 136) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ rep (padLane len x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 5716 [wd len, wd off, flag b] M) (callState s 20535 [wd 5818, flag b] M') 100 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h7 : 7 &&& len ≤ 7 := Nat.and_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt44_reach [1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895] with [word_mstore_disjoint]
  · intro x hx
    have hm8 : len % 8 < 8 := Nat.mod_lt _ (by omega)
    have hk : 7 &&& len = len % 8 := by
      rw [Nat.and_comm, show (7 : Nat) = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    have hA : 194590153796987103689458225493986751267109480675054880555039 * 2 ^ (len % 8 * 8) =
        rep (31 * 2 ^ (8 * (len % 8))) := by
      unfold rep REP pack4; rw [show 8 * (len % 8) = len % 8 * 8 by ring]; norm_num; ring
    have hB : (57896044618658097714924043372037294308723028227884584459520880401941320957952 : Nat) =
        rep (2 ^ 63) := by unfold rep REP pack4; norm_num
    have hAl : 31 * 2 ^ (8 * (len % 8)) < 2 ^ 64 := by interval_cases (len % 8) <;> norm_num
    have hBl : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
    rw [hk, hA, hB]
    simp only [KS, Nat.zero_add]
    rw [xor_mod_lit (rep_lt_lit hAl) (word_lt_lit _ _)]
    have hAw : rep (31 * 2 ^ (8 * (len % 8))) ^^^ word M (len / 8 * 32) < 2 ^ 256 :=
      Nat.xor_lt_two_pow (rep_lt hAl) (word_lt _ _)
    rw [word_wrL _ (Nat.mod_lt _ (by norm_num)) (by omega), word_wr _ hAw (by omega), word_wr _ hAw (by omega)]
    unfold padLane
    split_ifs <;> simp (disch := first | omega | exact hAl | exact hBl | exact rep_lt_lit hAl | exact rep_lt_lit hBl | exact word_lt_lit _ _ | norm_num) only [← rep_xor, rep_zero, Nat.xor_zero, Nat.zero_xor, xor_mod_lit, rep_lt_lit, word_lt_lit]
    all_goals first
      | (exfalso; omega)
      | (rw [show len / 8 * 32 = 32 * x by omega]; try simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm])
      | simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm]
      | (rw [show 32 * x = 512 by omega]; try simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm])
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

end MlDsaOpt44.Proofs
