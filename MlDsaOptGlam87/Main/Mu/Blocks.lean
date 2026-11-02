import MlDsaOpt44.Main.Mu.Lemmas
import MlDsaOptGlam87.Main.Base
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
/- Ported from `MlDsaOpt87/Main/Mu/Blocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
/-! # `seg_mu` blocks (ML-DSA-87)

The ML-DSA-44 blocks (`MlDsaOpt44/Main/Mu/Blocks.lean`) relocated to this artifact: the code
is the 44 code instruction for instruction, with `PUSH3` for the addresses above `0xffff`
and this artifact's calldata offsets (`HDR = 7219`) and no `|M| ≤ 69` branch. -/

namespace MlDsaOptGlam87.Proofs.S6Mu

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CRep CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK Rho1At SP SibFresh TOP TRL TTable Z0 aD aOf azRow baseOf cD cOf cStream codeOf ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf nNeg negCount okA okC okH okZ optAccepts pkOf rawZ rhoOf sPrime sigOf spOff t1Of t1v tEntry trOf w1Of wRow zHat zHi zLane zLo zPolys
open MlDsaOptGlam87.Proofs.Infra

/-- The byte-swap masks and `REP` below the swapped word. -/
def muK (b : Bool) : List UInt256 :=
  [wd 6277101735386680764176071790128604879584176795969512275969, wd 18446744073709551615, wd 26959946660873538060741835960174461801791452538186943042387869433855, wd 1766820105243087041267848467410591083712559083657179364930612997358944255, wd 450552876409790643671482431940419874915447411150352389258589821042463539455, flag b]

/-- Close the facts of a block whose memory is a chain of `MSTORE`s. -/
macro "s6mu_chain_facts" : tactic => `(tactic| (
  simp (disch := first | omega | exact word_lt _ _) only [word_mstore_disjoint, word_mstore]))

theorem mu_L1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, x < 8 → word M (TRL + 32 * x) < 2 ^ 64) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        rep (cpl x (if x < 8 then word M (TRL + 32 * x) else 0))) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 4624 [flag b] M) (callState s 4994 [flag b] M') 313 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  have h0 : word M 90368 < 2 ^ 64 := by simpa [TRL] using hT 0 (by omega)
  have h1 : word M 90400 < 2 ^ 64 := by simpa [TRL] using hT 1 (by omega)
  have h2 : word M 90432 < 2 ^ 64 := by simpa [TRL] using hT 2 (by omega)
  have h3 : word M 90464 < 2 ^ 64 := by simpa [TRL] using hT 3 (by omega)
  have h4 : word M 90496 < 2 ^ 64 := by simpa [TRL] using hT 4 (by omega)
  have h5 : word M 90528 < 2 ^ 64 := by simpa [TRL] using hT 5 (by omega)
  have h6 : word M 90560 < 2 ^ 64 := by simpa [TRL] using hT 6 (by omega)
  have h7 : word M 90592 < 2 ^ 64 := by simpa [TRL] using hT 7 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [KS, TRL, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals (try simp [cpl, complemented])
    all_goals (try norm_num [rep, REP, pack4])
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_L2a {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 4994 [flag b] M)
      (callState s 5164 (wd (bswapNet (word s.executionEnv.calldata 7217)) :: muK b) M) 120 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L3a {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5236 (muK b) M)
      (callState s 5279 (wd (bswapNet (word s.executionEnv.calldata 7249)) :: muK b) M) 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L4a {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5341 (muK b) M)
      (callState s 5384 (wd (bswapNet (word s.executionEnv.calldata 7281)) :: muK b) M) 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L2b {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray) :
    ∃ M', (word M' (KS + 256) = word M (KS + 256) ^^^ rep (18446744073709486080 &&& lane Y 3) ∧
      word M' (KS + 288) = word M (KS + 288) ^^^ rep (lane Y 2) ∧
      word M' (KS + 320) = word M (KS + 320) ^^^ rep (lane Y 1) ∧
      word M' (KS + 352) = word M (KS + 352) ^^^ rep (lane Y 0)) ∧
      FrameExcept M M' [(KS + 256, KS + 384)] ∧
      Reach (callState s 5164 (wd Y :: muK b) M) (callState s 5236 (muK b) M') 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761] with [muK, word_mstore_disjoint]
    rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit'] <;> xor_mod
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_L3b {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray) :
    ∃ M', (word M' (KS + 384) = word M (KS + 384) ^^^ rep (lane Y 3) ∧
      word M' (KS + 416) = word M (KS + 416) ^^^ rep (lane Y 2) ∧
      word M' (KS + 448) = word M (KS + 448) ^^^ rep (lane Y 1) ∧
      word M' (KS + 480) = word M (KS + 480) ^^^ rep (lane Y 0)) ∧
      FrameExcept M M' [(KS + 384, KS + 512)] ∧
      Reach (callState s 5279 (wd Y :: muK b) M) (callState s 5341 (muK b) M') 137 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839] with [muK, word_mstore_disjoint]
    rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit'] <;> xor_mod
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_L4b {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 7219 ≤ s.executionEnv.calldata.size) :
    ∃ M', (word M' (KS + 512) = word M (KS + 512) ^^^ rep (lane Y 3)) ∧
      FrameExcept M M' [(KS + 512, KS + 544)] ∧
      Reach (callState s 5384 (wd Y :: muK b) M) (callState s 5415 [wd (66 + (s.executionEnv.calldata.size - 7219)), wd 7289, flag b] M') 59 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895] with [muK, word_mstore_disjoint]
    rfl
  · simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit'] <;> xor_mod
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_loop1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5415 [wd len, wd off, flag b] M)
      (callState s 29816 [wd 5431, wd len, wd off, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904]

theorem mu_loop2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} :
    Reach (callState s 5431 [wd len, wd off, flag b] M)
      (callState s 6506 [wd off, wd 5441, wd off, wd len, flag b] M) 21 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1905, 1906, 1907, 1908, 1909, 1910]

theorem mu_loop3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5441 [wd off, wd len, flag b] M)
      (callState s 5415 [wd (len - 136), wd (136 + off), flag b] M) 30 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]

theorem mu_exit {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : len < 136) :
    Reach (callState s 5415 [wd len, wd off, flag b] M)
      (callState s 5454 [wd len, wd off, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  glam87_rreach [1896, 1897, 1898, 1899, 1900, 1901]

theorem mu_copy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) =
        if x = 1 ∨ x = 2 then 2 ^ 256 - 1 - word M (KS + 32 * x) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5556 [flag b] M) (callState s 5622 [flag b] M') 102 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [FIN, KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts
    all_goals norm_num
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_pad {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} (hlen : len < 136) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ rep (padLane len x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 5454 [wd len, wd off, flag b] M) (callState s 29816 [wd 5556, flag b] M') 100 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  have h7 : 7 &&& len ≤ 7 := Nat.and_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam87_rreach [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952] with [word_mstore_disjoint]
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

end MlDsaOptGlam87.Proofs.S6Mu
