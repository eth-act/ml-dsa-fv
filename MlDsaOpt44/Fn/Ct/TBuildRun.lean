import MlDsaOpt44.Fn.Ct.TBuildMath
import MlDsaOpt44.Fn.Ball
/-!
# `tbuild` (WP10): loops and the contract body

Word loop: 6 visits per chunk (`tb_inner`, `tb_chunk`); chunk loop: chunks `0 … 8`
continue (`tb_outer`), chunk 9 clamps `pa = end`, `off = 322`, chunk 10 rewrites
words 58, 59 and fills 60 … 63, then returns. Gas
`25 + 9 · 2591 + (2501 + 107) + (2501 + 58) = 28511 = Gas.tbuild`.
-/

namespace MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ
open MlDsa44

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem V_lt (cd : ByteArray) (a : Nat) : leNat cd a 32 < 2 ^ 256 := leNat_lt cd a 32

/-- The first `j` word-loop visits of a chunk. -/
theorem tb_inner (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m M : ByteArray} {n v0 off : Nat} (hI : Inv s.executionEnv.calldata m M n) (hoff : off = 32 + 5 * v0)
    (hn : v0 ≤ n) (hn64 : n ≤ 64) (hv : v0 + 6 ≤ 64) :
    ∀ j, j ≤ 5 → ∃ M', Inv s.executionEnv.calldata m M' (max n (v0 + j)) ∧
      Reach (callState s 14358 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata (320 + off) 32) ::
          wd (leNat s.executionEnv.calldata off 32) :: wd (24544 - 32 * v0) :: wd 20480 :: wd off :: wd 22688 ::
          wd ret :: tail) M)
        (callState s 14358 (wd (40 * j) :: wd (leNat s.executionEnv.calldata (960 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata (320 + off) 32) ::
          wd (leNat s.executionEnv.calldata off 32) :: wd (24544 - 32 * (v0 + j)) :: wd 20480 :: wd off ::
          wd 22688 :: wd ret :: tail) M') (302 * j)
  | 0, _ => ⟨M, by rw [show max n (v0 + 0) = n by omega]; exact hI,
      ((Reach.refl _).mono (by omega)).of_eq rfl (by simp)⟩
  | j + 1, hj => by
    obtain ⟨M', hI', hR⟩ := tb_inner hs htl hcd hI hoff hn hn64 hv j (by omega)
    have hA := tb_A hs htl M' (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (320 + off) 32)
      (V2 := leNat s.executionEnv.calldata (640 + off) 32) (V3 := leNat s.executionEnv.calldata (960 + off) 32)
      (ret := ret) (sh := 40 * j) (pa := 24544 - 32 * (v0 + j)) (off := off) (by omega)
      (V_lt _ _) (V_lt _ _) (V_lt _ _) (V_lt _ _)
    have hB := tb_B hs htl M' (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (320 + off) 32)
      (V2 := leNat s.executionEnv.calldata (640 + off) 32) (V3 := leNat s.executionEnv.calldata (960 + off) 32)
      (ret := ret) (X := tbW (40 * j) (leNat s.executionEnv.calldata off 32)
        (leNat s.executionEnv.calldata (320 + off) 32) (leNat s.executionEnv.calldata (640 + off) 32)
        (leNat s.executionEnv.calldata (960 + off) 32)) (sh := 40 * j) (pa := 24544 - 32 * (v0 + j)) (off := off)
      (lt_of_lt_of_eq (tbW_lt _ _ _ _ _) (by norm_num)) (by omega) (by omega) (by omega)
    have hI2 := inv_visit hcd hI' hoff (j := j) (by omega) (by omega) (by omega) (by omega)
    rw [show max (max n (v0 + j)) (v0 + j + 1) = max n (v0 + (j + 1)) by omega] at hI2
    refine ⟨_, hI2, ((hR.trans (hA.trans hB)).mono (by omega)).of_eq rfl ?_⟩
    rw [show 40 + 40 * j = 40 * (j + 1) by omega,
      show 24544 - 32 * (v0 + j) - 32 = 24544 - 32 * (v0 + (j + 1)) by omega]

/-- One chunk: four window loads and six word-loop visits. -/
theorem tb_chunk (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m M : ByteArray} {n v0 off : Nat} (hI : Inv s.executionEnv.calldata m M n) (hoff : off = 32 + 5 * v0)
    (hn : v0 ≤ n) (hn64 : n ≤ 64) (hv : v0 + 6 ≤ 64) :
    ∃ M', Inv s.executionEnv.calldata m M' (max n (v0 + 6)) ∧
      Reach (callState s 13967 (wd (24544 - 32 * v0) :: wd 20480 :: wd off :: wd 22688 :: wd ret :: tail) M)
        (callState s 14684 (wd 240 :: wd (leNat s.executionEnv.calldata (960 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata (320 + off) 32) ::
          wd (leNat s.executionEnv.calldata off 32) :: wd (24544 - 32 * v0 - 192) :: wd 20480 :: wd off ::
          wd 22688 :: wd ret :: tail) M') 2501 := by
  have hoff64 : off < 2 ^ 64 := by omega
  have l0 := tb_l0 hs htl M (ret := ret) (pa := 24544 - 32 * v0) hoff64
  have l1 := tb_l1 hs htl M (ret := ret) (pa := 24544 - 32 * v0) (V0 := leNat s.executionEnv.calldata off 32) hoff64
  have l2 := tb_l2 hs htl M (ret := ret) (pa := 24544 - 32 * v0) (V0 := leNat s.executionEnv.calldata off 32)
    (V1 := leNat s.executionEnv.calldata (320 + off) 32) hoff64
  have l3 := tb_l3 hs htl M (ret := ret) (pa := 24544 - 32 * v0) (V0 := leNat s.executionEnv.calldata off 32)
    (V1 := leNat s.executionEnv.calldata (320 + off) 32) (V2 := leNat s.executionEnv.calldata (640 + off) 32)
    hoff64
  obtain ⟨M5, hI5, hR5⟩ := tb_inner hs htl hcd hI hoff hn hn64 hv 5 (by omega)
  have hA := tb_A hs htl M5 (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (320 + off) 32)
      (V2 := leNat s.executionEnv.calldata (640 + off) 32) (V3 := leNat s.executionEnv.calldata (960 + off) 32)
      (ret := ret) (sh := 200) (pa := 24544 - 32 * (v0 + 5)) (off := off) (by omega)
    (V_lt _ _) (V_lt _ _) (V_lt _ _) (V_lt _ _)
  have hB := tb_Bx hs htl M5 (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (320 + off) 32)
      (V2 := leNat s.executionEnv.calldata (640 + off) 32) (V3 := leNat s.executionEnv.calldata (960 + off) 32)
      (ret := ret) (X := tbW 200 (leNat s.executionEnv.calldata off 32)
      (leNat s.executionEnv.calldata (320 + off) 32) (leNat s.executionEnv.calldata (640 + off) 32)
      (leNat s.executionEnv.calldata (960 + off) 32)) (pa := 24544 - 32 * (v0 + 5)) (off := off)
    (lt_of_lt_of_eq (tbW_lt _ _ _ _ _) (by norm_num)) (by omega) (by omega)
  have hI6 := inv_visit hcd hI5 hoff (j := 5) (by omega) (by omega) (by omega) (by omega)
  rw [show max (max n (v0 + 5)) (v0 + 5 + 1) = max n (v0 + 6) by omega,
    show (40 * 5 : Nat) = 200 from rfl] at hI6
  refine ⟨_, hI6, ((l0.trans (l1.trans (l2.trans (l3.trans (hR5.trans (hA.trans hB)))))).mono
    (by omega)).of_eq rfl ?_⟩
  rw [show 24544 - 32 * (v0 + 5) - 32 = 24544 - 32 * v0 - 192 by omega]

/-- Chunks `0 … c − 1` (all continuing). -/
theorem tb_outer (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (m : ByteArray) :
    ∀ c, c ≤ 9 → ∃ M, Inv s.executionEnv.calldata m M (6 * c) ∧
      Reach (callState s 13967 (wd 24544 :: wd 20480 :: wd 32 :: wd 22688 :: wd ret :: tail) m)
        (callState s 13967 (wd (24544 - 192 * c) :: wd 20480 :: wd (32 + 30 * c) :: wd 22688 :: wd ret :: tail) M)
        (2591 * c)
  | 0, _ => ⟨m, inv_zero _ _, ((Reach.refl _).mono (by omega)).of_eq rfl (by simp)⟩
  | c + 1, hc => by
    obtain ⟨M, hI, hR⟩ := tb_outer hs htl hcd m c (by omega)
    obtain ⟨M', hI', hC⟩ := tb_chunk hs htl hcd hI (v0 := 6 * c) (off := 32 + 30 * c) (by omega) (by omega)
      (by omega) (by omega)
    have hN := tb_nc hs htl M' (ret := ret) (V0 := leNat s.executionEnv.calldata (32 + 30 * c) 32)
      (V1 := leNat s.executionEnv.calldata (320 + (32 + 30 * c)) 32)
      (V2 := leNat s.executionEnv.calldata (640 + (32 + 30 * c)) 32)
      (V3 := leNat s.executionEnv.calldata (960 + (32 + 30 * c)) 32)
      (pa := 24544 - 192 * c - 192) (off := 32 + 30 * c) (by omega) (by omega) (by omega) (by omega)
    rw [show max (6 * c) (6 * c + 6) = 6 * (c + 1) by omega] at hI'
    rw [show 24544 - 32 * (6 * c) = 24544 - 192 * c by omega] at hC
    refine ⟨M', hI', ((hR.trans (hC.trans hN)).mono (by omega)).of_eq rfl ?_⟩
    rw [show 24544 - 192 * c - 192 = 24544 - 192 * (c + 1) by omega,
      show 30 + (32 + 30 * c) = 32 + 30 * (c + 1) by omega]

theorem tbuild_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.tbuild ret tail) (m : ByteArray) (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', (∀ e, e < 768 → ∀ r, r < 4 → be16 m' (TT + 6142 - 8 * e - 2 * r) =
        (if 256 ≤ e ∧ e < 512 then t1v s.executionEnv.calldata r (e - 256)
          else 1023 - t1v s.executionEnv.calldata r (e % 256))) ∧
      FrameExcept m m' [(TT, TT + 6144)] ∧
      Call s Entry.tbuild [wd TT, wd 32] ret tail m [] m' Gas.tbuild := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.tbuild, Stack.leaf] at this; omega
  have hp := tb_pro hs htl m (ret := ret)
  obtain ⟨M9, hI9, hR9⟩ := tb_outer hs htl hcd m (ret := ret) 9 le_rfl
  obtain ⟨M10, hI10, hC9⟩ := tb_chunk hs htl hcd hI9 (ret := ret) (v0 := 54) (off := 302) (by omega)
    (by omega) (by omega) (by omega)
  have hL := tb_cl hs htl M10 (ret := ret) (V0 := leNat s.executionEnv.calldata 302 32)
    (V1 := leNat s.executionEnv.calldata (320 + 302) 32) (V2 := leNat s.executionEnv.calldata (640 + 302) 32)
    (V3 := leNat s.executionEnv.calldata (960 + 302) 32)
  rw [show max (6 * 9) (54 + 6) = 60 by omega] at hI10
  obtain ⟨M11, hI11, hC10⟩ := tb_chunk hs htl hcd hI10 (ret := ret) (v0 := 58) (off := 322) (by omega)
    (by omega) (by omega) (by omega)
  have hE := tb_exit hs htl hr.jumpdest hr.small M11 (ret := ret)
    (V0 := leNat s.executionEnv.calldata 322 32)
    (V1 := leNat s.executionEnv.calldata (320 + 322) 32) (V2 := leNat s.executionEnv.calldata (640 + 322) 32)
    (V3 := leNat s.executionEnv.calldata (960 + 322) 32)
  rw [show max 60 (58 + 6) = 64 by omega] at hI11
  refine ⟨M11, inv_table hI11, hI11.1, ?_⟩
  rw [call_iff, Entry.tbuild, Gas.tbuild]
  simp only [TT, List.cons_append, List.nil_append]
  exact (hp.trans (hR9.trans (hC9.trans (hL.trans (hC10.trans hE))))).mono (by norm_num)

end

end MlDsaOpt44.Proofs.TB
