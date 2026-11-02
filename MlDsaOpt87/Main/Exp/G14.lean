import MlDsaOpt87.Main.Exp.Round
import MlDsaOpt87.Main.Exp.Bound
import MlDsaOpt87.Fn.Ginit.Call
set_option warningAsError true
set_option maxHeartbeats 0
/-!
# The Kronecker group 14 and `pass3f14` (`5394 … 5551`, ML-DSA-87, v4)

`HAVE6 := 0`; `ginit [l4, 0, 15, 0]` seeds slot `k` with `A[7][6 − k]`; five
squeezes (`kf4` with `blk`, `blkh` for block 4); `gfix 15` (flag `okRow7`); `AND`;
`pass3f14` adds columns 4–6 of rows 4–6 (`CW`, `HP`, `HP + 0x2000`, masked) and
the Kronecker term of row 7 (columns 3–6) to `ACC + 0x2000`. Both accumulator
tables then hold the sums over all seven columns: `AccAt` (`fin_p3f14`, `accAt_of`).
-/

namespace MlDsaOpt87.Proofs.Exp

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt87.Proofs
open MlDsaOpt87.Proofs.Infra

/-- Slot `k` of group 14: the seed of `A[7][6 − k]`. -/
def I14 (cd : ByteArray) (k : Nat) : Fips202.SpongeState := seedState 168 (aSeed cd 7 (6 - k))

/-- Group 14 at the start of squeeze `b`. -/
def X14 (cd : ByteArray) (b k : Nat) : Fips202.SpongeState := permN b (I14 cd k)

theorem X14_sized (cd : ByteArray) (b : Nat) : Sized4 (X14 cd b) := fun _ _ =>
  permN_size (seedState_size _ _) b

theorem g14_flag {cd : ByteArray} (hcd : 32 ≤ cd.size) :
    ((List.range 4).all fun sl => !(15 : Nat).testBit sl || (aI (I14 cd sl)).isSome) = okRow7 cd := by
  have e : ∀ c, aI (seedState 168 (aSeed cd 7 c)) = aOf cd 7 c := fun c => GroupP.aI_aSeed hcd 7 c
  unfold I14 okRow7
  simp only [e, show List.range 4 = [0, 1, 2, 3] from rfl, List.all_cons, List.all_nil,
    show (15 : Nat).testBit 0 = true by decide, show (15 : Nat).testBit 1 = true by decide,
    show (15 : Nat).testBit 2 = true by decide, show (15 : Nat).testBit 3 = true by decide,
    Bool.not_true, Bool.false_or, Bool.and_true, Nat.reduceSub, Nat.reduceAdd]
  cases (aOf cd 7 3).isSome <;> cases (aOf cd 7 4).isSome <;> cases (aOf cd 7 5).isSome <;>
    cases (aOf cd 7 6).isSome <;> rfl

/-- `HAVE6 := 0; ginit` of group 14. -/
theorem g14_ginit {s : State} (hs : Ctx s) (hcd32 : 32 ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (b : Bool) :
    ∃ m1, KS4 m1 (X14 s.executionEnv.calldata 0) ∧ word m1 HAVE6 = 0 ∧
      FrameExcept m m1 [(HAVE6, HAVE6 + 32), (KS, KS + 800)] ∧
      Reach (callState s 5394 [flag b] m) (callState s 5422 [flag b] m1) (32 + Gas.ginit) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have g0 : Reach (callState s 5394 [flag b] m)
      (callState s 13376 [wd 0x0fffff00000fff0000079a, wd 0, wd 15, wd 0, wd 5422, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 32 := by
    opt87_reach [1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680] with [HAVE6]
  generalize hcdv : s.executionEnv.calldata = cd at hcd32 hrho
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 5422) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 15) (cmult := 0) (l4 := 0x0fffff00000fff0000079a)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by avoids_tac)
  have hks : KS4 m1 (X14 cd 0) :=
    ks4_ginit (keep := 0) (amult := 15) (cmult := 0) (l4 := 0x0fffff00000fff0000079a) (kmask := 0)
      (L := fun k => (6 - k) + 256 * 7 + 0x1F0000)
      (S := X14 cd 0) hrho0 (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun k _ => by omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        have e : X14 cd 0 k = seedState 168 (aSeed cd 7 (6 - k)) := rfl
        rw [e]
        exact freshLane_aSeed' hcd32 (amult := 15) (k := k) (r := 7) (col := 6 - k)
          (L := fun k => (6 - k) + 256 * 7 + 0x1F0000) (by norm_num) (by omega)
          (by interval_cases k <;> decide) rfl hx)
      hg
  refine ⟨m1, hks, by
      rw [word_frame hf1 (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h60,
    FrameExcept.trans hf0 hf1, g0.trans hc1⟩

/-- The glue of `5394 … 5551` outside the calls (exact static cost). -/
def g14Glue : Nat := 248

/-- The exact cost of `5394 … 5551`. -/
def gG14 : Nat :=
  g14Glue + Gas.ginit + 5 * Gas.kf4 + 4 * Gas.blk + Gas.blkh + Gas.gfix 4 + Gas.pass3f14

theorem exp_g14 {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hI : InvG14 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', InvW s.executionEnv.calldata m' ∧
      Reach (callState s 5394 [flag b] m)
        (callState s 5551 [flag (b && okRow7 s.executionEnv.calldata)] m') gG14 := by
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by
    have h := hcd; unfold HDR at h; omega
  clear hcd
  have hI0 := hI.inv
  obtain ⟨m1, hks1, h61, hf1, hR1⟩ := g14_ginit hs hcd32 hI0.rho b
  have hrc1 := RC4Table.frame hI0.rc4 hf1 (by avoids_tac)
  have St_eq : ∀ b' k, k < 4 → (fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) b' k =
      Keccak.permute (X14 s.executionEnv.calldata b' k) := fun b' k _ => permN_succ _ _
  have Xs : ∀ b', ∀ k, k < 4 → Keccak.permute (X14 s.executionEnv.calldata b' k) =
      X14 s.executionEnv.calldata (b' + 1) k := fun b' k _ => (permN_succ _ _).symm
  -- squeeze 0
  obtain ⟨m2, hks2', hB2, hrc2, hf2, hR2⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m1) (St := fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) (pc0 := 5422) (r1 := 5430) (r2 := 5444) (c1 := 15) (c2 := 21) (b := 0) (by norm_num)
    (by opt87_reach [1681, 1682, 1683, 1684])
    (fun _ => by opt87_reach [1685, 1686, 1687, 1688, 1689, 1690] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc1 (X14_sized _ 0) hks1 (HBlocks.zero _ _) (St_eq 0)
  have hks2 := KS4.congr hks2' (Xs 0)
  -- squeeze 1
  obtain ⟨m3, hks3', hB3, hrc3, hf3, hR3⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m2) (St := fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) (pc0 := 5444) (r1 := 5452) (r2 := 5466) (c1 := 15) (c2 := 21) (b := 1) (by norm_num)
    (by opt87_reach [1691, 1692, 1693, 1694])
    (fun _ => by opt87_reach [1695, 1696, 1697, 1698, 1699, 1700] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc2 (X14_sized _ 1) hks2 hB2 (St_eq 1)
  have hks3 := KS4.congr hks3' (Xs 1)
  -- squeeze 2
  obtain ⟨m4, hks4', hB4, hrc4, hf4, hR4⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m3) (St := fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) (pc0 := 5466) (r1 := 5474) (r2 := 5488) (c1 := 15) (c2 := 21) (b := 2) (by norm_num)
    (by opt87_reach [1701, 1702, 1703, 1704])
    (fun _ => by opt87_reach [1705, 1706, 1707, 1708, 1709, 1710] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc3 (X14_sized _ 2) hks3 hB3 (St_eq 2)
  have hks4 := KS4.congr hks4' (Xs 2)
  -- squeeze 3
  obtain ⟨m5, hks5', hB5, hrc5, hf5, hR5⟩ := kb_round hs (fb := flag b) (stk := [flag b])
    (m := m4) (St := fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) (pc0 := 5488) (r1 := 5496) (r2 := 5510) (c1 := 15) (c2 := 21) (b := 3) (by norm_num)
    (by opt87_reach [1711, 1712, 1713, 1714])
    (fun _ => by opt87_reach [1715, 1716, 1717, 1718, 1719, 1720] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc4 (X14_sized _ 3) hks4 hB4 (St_eq 3)
  have hks5 := KS4.congr hks5' (Xs 3)
  -- squeeze 4 (blkh)
  obtain ⟨m6, hks6', hB6, hrc6, hf6, hR6⟩ := kbh_round hs (fb := flag b) (stk := [flag b])
    (m := m5) (St := fun b k => permN (b + 1) (I14 s.executionEnv.calldata k)) (pc0 := 5510) (r1 := 5518) (r2 := 5532) (c1 := 15) (c2 := 21)
    (by opt87_reach [1721, 1722, 1723, 1724])
    (fun _ => by opt87_reach [1725, 1726, 1727, 1728, 1729, 1730] with [FL, ABUF])
    (by simp only [isValidJumpDest_lit]) (by norm_num) (by simp only [isValidJumpDest_lit]) (by norm_num)
    hrc5 (X14_sized _ 4) hks5 hB5 (St_eq 4)
  have hks6 := KS4.congr hks6' (Xs 4)
  -- gfix 15
  have hfS := FrameExcept.trans (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hf2 hf3) hf4) hf5) hf6
  have h66 : word m6 HAVE6 = 0 := by
    rw [word_frame hfS (lo := HAVE6) (hi := HAVE6 + 32) (by avoids_tac) le_rfl le_rfl]; exact h61
  have gG : Reach (callState s 5532 [flag b] m6) (callState s 12966 [wd 15, wd 5542, flag b] m6) 18 := by
    opt87_reach [1731, 1732, 1733, 1734, 1735]
  obtain ⟨m7, hl7, hks7, -, hf7, hc7⟩ := gfix_call hs (ret := 5542) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m6 hrc6
    (amask := 15) (by norm_num) 4 (by decide) (X14 s.executionEnv.calldata 5) (X14_sized _ 5) hks6
    (I14 s.executionEnv.calldata) h66
    (fun sl hsl _ => ⟨hB6.slotHead hsl (fun _ _ => rfl), rfl⟩)
  rw [g14_flag hcd32] at hc7
  have hrow : Row7At m7 s.executionEnv.calldata := by
    intro hok t ht k hk
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (okA_get hok (r := 7) (s := 6 - k) (by omega)
      (by omega))
    rw [aD_of_some ha]
    exact hl7 k hk (by interval_cases k <;> decide) a
      (by unfold I14; rw [GroupP.aI_aSeed hcd32]; exact ha) t ht
  -- AND, pass3f14
  have gA : Reach (callState s 5542 [flag (okRow7 s.executionEnv.calldata), flag b] m7)
      (callState s 12698 [wd 5551, flag (b && okRow7 s.executionEnv.calldata)] m7) 18 := by
    opt87_rreach [1736, 1737, 1738, 1739, 1740] with [flag, MlDsaOpt44.Proofs.ite01_land]
  obtain ⟨m8, hw8, hf8, hc8⟩ := pass3f14_call hs (ret := 5551)
    (tail := [flag (b && okRow7 s.executionEnv.calldata)])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m7
  -- frames
  have hfA := FrameExcept.trans (FrameExcept.trans hf1 hfS) hf7
  have hI7 := inve_frame hI0 hfA
  have hI8 := inve_frame hI7 hf8
  have hacc := accAt_of hI8.zhat
    (fin_p3f14 hI7.zhat (hI.acc0.frame (by norm_num) hfA (by exp_av) (by exp_av))
      (hI.acc1.frame hfA (by exp_av) (by exp_av))
      (hI.b11.frame hfA (by exp_av)) (hI.b12.frame hfA (by exp_av)) (hI.b13.frame hfA (by exp_av))
      hrow hw8
      (fun t ht => word_frame hf8 (lo := ACC) (hi := ACC + 8192) (by exp_av) (by omega) (by omega))
      (fun k hk t ht => zhLane_frame hf8 (by exp_av) (by omega) ht))
  refine ⟨m8, ⟨hI8.rc1, hI8.tbl, hacc,
    TrlAt.frame (TrlAt.frame hI.trl hfA (by exp_av)) hf8 (by exp_av),
    hI8.zBases, hI8.zIdx, hI8.zNeg⟩, ?_⟩
  have hR := ((((((((hR1.trans hR2).trans hR3).trans hR4).trans hR5).trans hR6).trans gG).trans hc7).trans
    gA).trans hc8
  refine hR.mono ?_
  unfold gG14 g14Glue
  omega

end MlDsaOpt87.Proofs.Exp
