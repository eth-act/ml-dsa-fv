import MlDsaOpt44.Main.Mu.Lemmas
import MlDsaOpt65.Main.Base
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
/-! # `seg_mu` blocks (ML-DSA-65)

The ML-DSA-44 blocks (`MlDsaOpt44/Main/Mu/Blocks.lean`) relocated to this artifact: the code
is the 44 code instruction for instruction, with `PUSH3` for the addresses above `0xffff`
and this artifact's calldata offsets (`HDR = 5261`). -/

namespace MlDsaOpt65.Proofs.S6Mu

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt65.Proofs.Infra

/-- The byte-swap masks and `REP` below the swapped word. -/
def muK (b : Bool) : List UInt256 :=
  [wd 6277101735386680764176071790128604879584176795969512275969, wd 18446744073709551615, wd 26959946660873538060741835960174461801791452538186943042387869433855, wd 1766820105243087041267848467410591083712559083657179364930612997358944255, wd 450552876409790643671482431940419874915447411150352389258589821042463539455, flag b]

/-- Close the facts of a block whose memory is a chain of `MSTORE`s. -/
macro "s6mu_chain_facts" : tactic => `(tactic| (
  simp (disch := first | omega | exact word_lt _ _) only [word_mstore_disjoint, word_mstore]))

theorem mu_chk_long {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 5331 ≤ s.executionEnv.calldata.size) :
    Reach (callState s 5190 [flag b] M) (callState s 5500 [flag b] M) 24 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [1715, 1716, 1717, 1718, 1719, 1720]

theorem mu_short {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hsh : s.executionEnv.calldata.size < 5331)
    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5190 [flag b] M) (callState s 6499 [flag b] M') 195 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  have h0 : word M 89600 < 2 ^ 64 := by simpa [MU] using hU 0 (by omega)
  have h1 : word M 89632 < 2 ^ 64 := by simpa [MU] using hU 1 (by omega)
  have h2 : word M 89664 < 2 ^ 64 := by simpa [MU] using hU 2 (by omega)
  have h3 : word M 89696 < 2 ^ 64 := by simpa [MU] using hU 3 (by omega)
  have h4 : word M 89728 < 2 ^ 64 := by simpa [MU] using hU 4 (by omega)
  have h5 : word M 89760 < 2 ^ 64 := by simpa [MU] using hU 5 (by omega)
  have h6 : word M 89792 < 2 ^ 64 := by simpa [MU] using hU 6 (by omega)
  have h7 : word M 89824 < 2 ^ 64 := by simpa [MU] using hU 7 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770] with [word_mstore_disjoint]
    rfl
  · intro x hx
    interval_cases x <;> simp only [FIN, MU, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit']
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_L1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, x < 8 → word M (TRL + 32 * x) < 2 ^ 64) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) =
        rep (cpl x (if x < 8 then word M (TRL + 32 * x) else 0))) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 5500 [flag b] M) (callState s 5871 [flag b] M') 314 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  have h0 : word M 89344 < 2 ^ 64 := by simpa [TRL] using hT 0 (by omega)
  have h1 : word M 89376 < 2 ^ 64 := by simpa [TRL] using hT 1 (by omega)
  have h2 : word M 89408 < 2 ^ 64 := by simpa [TRL] using hT 2 (by omega)
  have h3 : word M 89440 < 2 ^ 64 := by simpa [TRL] using hT 3 (by omega)
  have h4 : word M 89472 < 2 ^ 64 := by simpa [TRL] using hT 4 (by omega)
  have h5 : word M 89504 < 2 ^ 64 := by simpa [TRL] using hT 5 (by omega)
  have h6 : word M 89536 < 2 ^ 64 := by simpa [TRL] using hT 6 (by omega)
  have h7 : word M 89568 < 2 ^ 64 := by simpa [TRL] using hT 7 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876] with [word_mstore_disjoint]
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
    Reach (callState s 5871 [flag b] M)
      (callState s 6041 (wd (bswapNet (word s.executionEnv.calldata 5259)) :: muK b) M) 120 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L3a {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 6113 (muK b) M)
      (callState s 6156 (wd (bswapNet (word s.executionEnv.calldata 5291)) :: muK b) M) 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L4a {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 6218 (muK b) M)
      (callState s 6261 (wd (bswapNet (word s.executionEnv.calldata 5323)) :: muK b) M) 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074] with [muK, bswapNet, bsw8, bsw16, bsw32]

theorem mu_L2b {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray) :
    ∃ M', (word M' (KS + 256) = word M (KS + 256) ^^^ rep (18446744073709486080 &&& lane Y 3) ∧
      word M' (KS + 288) = word M (KS + 288) ^^^ rep (lane Y 2) ∧
      word M' (KS + 320) = word M (KS + 320) ^^^ rep (lane Y 1) ∧
      word M' (KS + 352) = word M (KS + 352) ^^^ rep (lane Y 0)) ∧
      FrameExcept M M' [(KS + 256, KS + 384)] ∧
      Reach (callState s 6041 (wd Y :: muK b) M) (callState s 6113 (muK b) M') 143 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961] with [muK, word_mstore_disjoint]
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
      Reach (callState s 6156 (wd Y :: muK b) M) (callState s 6218 (muK b) M') 137 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039] with [muK, word_mstore_disjoint]
    rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit'] <;> xor_mod
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_L4b {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 5261 ≤ s.executionEnv.calldata.size) :
    ∃ M', (word M' (KS + 512) = word M (KS + 512) ^^^ rep (lane Y 3)) ∧
      FrameExcept M M' [(KS + 512, KS + 544)] ∧
      Reach (callState s 6261 (wd Y :: muK b) M) (callState s 6292 [wd (66 + (s.executionEnv.calldata.size - 5261)), wd 5331, flag b] M') 59 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095] with [muK, word_mstore_disjoint]
    rfl
  · simp only [KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts <;>
      simp only [rep_lit'] <;> xor_mod
  · simp only [KS]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_loop1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 6292 [wd len, wd off, flag b] M)
      (callState s 19907 [wd 6308, wd len, wd off, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104]

theorem mu_loop2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} :
    Reach (callState s 6308 [wd len, wd off, flag b] M)
      (callState s 7415 [wd off, wd 6318, wd off, wd len, flag b] M) 21 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [2105, 2106, 2107, 2108, 2109, 2110]

theorem mu_loop3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 6318 [wd off, wd len, flag b] M)
      (callState s 6292 [wd (len - 136), wd (136 + off), flag b] M) 30 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119]

theorem mu_exit {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : len < 136) :
    Reach (callState s 6292 [wd len, wd off, flag b] M)
      (callState s 6331 [wd len, wd off, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  opt65_reach [2096, 2097, 2098, 2099, 2100, 2101]

theorem mu_copy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) =
        if x = 1 ∨ x = 2 then 2 ^ 256 - 1 - word M (KS + 32 * x) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 6433 [flag b] M) (callState s 6499 [flag b] M') 102 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [2153, 2154, 2155, 2156, 2157, 2158, 2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [FIN, KS, Nat.reduceMul, Nat.reduceAdd] <;> s6mu_chain_facts
    all_goals norm_num
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_pad {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} (hlen : len < 136) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ rep (padLane len x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 6331 [wd len, wd off, flag b] M) (callState s 19907 [wd 6433, flag b] M') 100 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2865 ≤ s.activeWords.toNat := hs.sized
  have h7 : 7 &&& len ≤ 7 := Nat.and_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt65_reach [2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127, 2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152] with [word_mstore_disjoint]
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

end MlDsaOpt65.Proofs.S6Mu
