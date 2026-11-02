import MlDsaOptGlam44.Main.Mu.Long
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
/-!
# μ on the long-message schedule (`FLAG = 0`): the blocks that read `FLAG`

The dispatch bound is `0x10fa − 0x220 · FLAG = 4346`; `hash_mu`'s test
`FLAG == 0` jumps to `muimg` (5504, no `MCOPY` of `SC`), and block 5 of
`tr ‖ 0 ‖ 0 ‖ M` (calldata 4346) is the first one absorbed. The other blocks
are those of `Main/Mu/Long.lean`.
-/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOptGlam44.Proofs.Infra

theorem mu0_chk_long {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 4346 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 0) :
    Reach (callState s 5183 [flag b] M) (callState s 5486 [flag b] M) 41 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 0 := hfl
  glam44_rreach [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756] with [hfl']

theorem mu0_short {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hsh : s.executionEnv.calldata.size < 4346)
    (hU : ∀ x, x < 8 → word M (MU + 32 * x) < 2 ^ 64) (hfl : word M FLAG = 0) :
    ∃ M', (∀ x, x < 8 → word M' (FIN + 32 * x) = rep (word M (MU + 32 * x))) ∧
      FrameExcept M M' [(FIN, FIN + 256)] ∧
      Reach (callState s 5183 [flag b] M) (callState s 6020 [flag b] M') 212 := by
  have hfl' : word M 3936 = 0 := hfl
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

/-- `hash_mu` with `FLAG = 0`: the jump to `muimg`, past the `MCOPY`. -/
theorem mu0_img {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 0) :
    Reach (callState s 5486 [flag b] M) (callState s 5504 [flag b] M) 23 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 0 := hfl
  glam44_rreach [1807, 1808, 1809, 1810, 1811, 1812] with [hfl']

theorem mu0_abs1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) (hfl : word M FLAG = 0) :
    Reach (callState s 5783 [flag b] M)
      (callState s 7000 [wd 4346, wd 5803, wd 4346, flag b] M) 37 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 0 := hfl
  glam44_rreach [1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992] with [hfl']

theorem mu0_head0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray)
    (hfit : s.executionEnv.calldata.size < 18446744073709551616)
    (hl : 4346 ≤ s.executionEnv.calldata.size) (hfl : word M FLAG = 0) :
    Reach (callState s 5803 [wd 4346, flag b] M)
      (callState s 5821 [wd (s.executionEnv.calldata.size - 4346), wd 4482, flag b] M) 32 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2616 ≤ s.activeWords.toNat := hs.sized
  have hfl' : word M 3936 = 0 := hfl
  glam44_rreach [1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003] with [hfl']

end MlDsaOptGlam44.Proofs
