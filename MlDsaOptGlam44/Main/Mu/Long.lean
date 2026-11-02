import MlDsaOpt44.Main.Mu.Blocks
import MlDsaOpt44.Main.Mu.Spec
import MlDsaOptGlam44.Layout
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Main.Base
/- Ported from `MlDsaOpt44/Main/Mu/Long.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
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

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

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
    (hl : 3802 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 1) :
    Reach (callState s 5183 [flag b] M) (callState s 5486 [flag b] M) 41 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 1 := hfl  -- glam: `FLAG`
  glam44_rreach [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756] with [hfl']

theorem mu_short {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hsh : s.executionEnv.calldata.size < 3802)
    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) (hfl : word M FLAG = 1) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5183 [flag b] M) (callState s 6020 [flag b] M') 212 := by
  have hfl' : word M 3936 = 1 := hfl  -- glam: `FLAG`
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
  · glam44_rreach [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806] with [word_mstore_disjoint, hfl']
    rfl
  · intro x hx
    interval_cases x <;> simp only [FIN, MU, Nat.reduceMul, Nat.reduceAdd] <;> chain_facts <;>
      simp only [rep_lit']
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_cpy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 1) :
    Reach (callState s 5486 [flag b] M) (callState s 5503 [wd KS, wd SC, wd 800, flag b] M) 31 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 1 := hfl  -- glam: `FLAG`
  glam44_rreach [1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815] with [KS, SC, hfl']

theorem mu_cext_pre {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 5504 [flag b] M)
      (callState s 19241 [wd 25, wd 1, wd KS, wd 5517, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [1817, 1818, 1819, 1820, 1821, 1822, 1823] with [KS]

set_option maxRecDepth 10000 in
theorem mu_repA {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hT : ∀ x, 0 ≤ x → x < 7 → word M (KS + 32 * x) < 2 ^ 64) :
    ∃ M', RepStep M M' 0 7 ∧
      Reach (callState s 5517 [flag b] M) (callState s 5600 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 148 := by
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
  · glam44_rreach [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869] with [word_mstore_disjoint]
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
      Reach (callState s 5600 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5670 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 146 := by
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
  · glam44_rreach [1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913] with [word_mstore_disjoint]
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
      Reach (callState s 5670 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5731 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M') 123 := by
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
  · glam44_rreach [1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950] with [word_mstore_disjoint]
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
      Reach (callState s 5731 [wd 6277101735386680764176071790128604879584176795969512275969, flag b] M) (callState s 5783 [flag b] M') 105 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h20 : word M 640 < 2 ^ 64 := by simpa [KS] using hT 20 (by omega) (by omega)
  have h21 : word M 672 < 2 ^ 64 := by simpa [KS] using hT 21 (by omega) (by omega)
  have h22 : word M 704 < 2 ^ 64 := by simpa [KS] using hT 22 (by omega) (by omega)
  have h23 : word M 736 < 2 ^ 64 := by simpa [KS] using hT 23 (by omega) (by omega)
  have h24 : word M 768 < 2 ^ 64 := by simpa [KS] using hT 24 (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  rotate_left 3
  · glam44_rreach [1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982] with [word_mstore_disjoint]
  · intro x h1 h2
    interval_cases x <;> simp only [KS, Nat.reduceMul, Nat.reduceAdd, Nat.zero_add] <;> chain_facts
    all_goals (try simp (disch := assumption) only [not_rep_lit'])
    all_goals (try simp only [rep_lit'])
    all_goals simp [cpl, complemented]
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _

theorem mu_abs1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 1) :
    Reach (callState s 5783 [flag b] M)
      (callState s 7000 [wd 3802, wd 5803, wd 3802, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 1 := hfl  -- glam: `FLAG`
  glam44_rreach [1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992] with [hfl']

theorem mu_head0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 3802 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 1) :
    Reach (callState s 5803 [wd 3802, flag b] M)
      (callState s 5821 [wd (s.executionEnv.calldata.size - 3802), wd 3938, flag b] M) 32 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 1 := hfl  -- glam: `FLAG`
  glam44_rreach [1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003] with [hfl']

theorem mu_loop1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5821 [wd len, wd off, flag b] M)
      (callState s 30933 [wd 5837, wd len, wd off, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012]

theorem mu_loop2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} :
    Reach (callState s 5837 [wd len, wd off, flag b] M)
      (callState s 7000 [wd off, wd 5847, wd off, wd len, flag b] M) 21 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [2013, 2014, 2015, 2016, 2017, 2018]

theorem mu_loop3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : 136 ≤ len) (hl : len < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 5847 [wd off, wd len, flag b] M)
      (callState s 5821 [wd (len - 136), wd (136 + off), flag b] M) 30 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027]

theorem mu_exit {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat}
    (hlen : len < 136) :
    Reach (callState s 5821 [wd len, wd off, flag b] M)
      (callState s 5860 [wd len, wd off, flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  glam44_rreach [2004, 2005, 2006, 2007, 2008, 2009]

theorem mu_copy {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) =
        if x = 1 ∨ x = 2 then 2 ^ 256 - 1 - word M (KS + 32 * x) else word M (KS + 32 * x)) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5962 [flag b] M) (callState s 6020 [flag b] M') 102 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam44_rreach [2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095] with [word_mstore_disjoint]
  · intro x hx
    interval_cases x <;> simp only [FIN, KS, Nat.reduceMul, Nat.reduceAdd] <;> chain_facts
    all_goals norm_num
  · simp only [FIN]
    repeat (refine frame_wr (by norm_num) (by norm_num) ?_)
    exact FrameExcept.refl _ _

theorem mu_pad {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} (hlen : len < 136) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ rep (padLane len x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 5860 [wd len, wd off, flag b] M) (callState s 30933 [wd 5962, flag b] M') 100 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have h7 : 7 &&& len ≤ 7 := Nat.and_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · glam44_rreach [2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060] with [word_mstore_disjoint]
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

end MlDsaOptGlam44.Proofs
