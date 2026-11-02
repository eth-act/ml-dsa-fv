import MlDsaOpt65.Main.Exp.G8Mu
import MlDsaOpt65.Main.Exp.G57.Defs
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# Group 8 up to `gfix` (ML-DSA-65, v4)

`g8_head` (pc 5022): `HAVE6 := 0`, `ginit [0, 1, 2, L4]` (slot 0 `A[5][4]`,
slot 1 c̃), `mub0 [2]` (μ's block 0 into slot 2); `mub0` returns to 5064
for `|M| ≤ 69` and to the out-of-line region at 7066 otherwise.

* `g8_short` (5064): five rounds `kf4` + `blk` / `blkh`, `cext` of c̃'s
  stream after rounds 0 and 1, `cext [MU, 2, 8]` after round 0.
* `g8_long` (7066): the same rounds and c̃ `cext`s, `mub (136 k)` after round
  `k − 1` (`mub_step`: absorb block `k`, or squeeze μ when `k = N`).

Both end at `gfix`'s entry with `G8Mid`: the slots after round 4 (`St 4`),
the five block heads, `HAVE6 = 0`, `H(c̃)` in `CB`, μ in `MU`.
-/

namespace MlDsaOpt65.Proofs.Exp

open MlDsaOpt44.Proofs
open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt65.Proofs
open MlDsaOpt65.Proofs.Ex
open MlDsaOpt65.Proofs.Infra

/-- μ is in `MU` once its last block was squeezed (after `mub n`). -/
def MuW (m cd : ByteArray) (n : Nat) : Prop :=
  muN cd ≤ n → ∀ x, x < 8 → word m (MU + 32 * x) = le64 (muOf cd) (8 * x)

theorem MuW.frame {m m' cd : ByteArray} {n : Nat} {rs : List (Nat × Nat)} (h : MuW m cd n)
    (hf : FrameExcept m m' rs) (ha : Avoids rs MU (MU + 256)) : MuW m' cd n := fun hn x hx => by
  rw [word_frame hf ha (a := MU + 32 * x) (by omega) (by omega)]; exact h hn x hx

/-- At `gfix`'s entry. -/
structure G8Mid (cd m0 m : ByteArray) : Prop where
  ks : KS4 m (St cd 4)
  hb : HBlocks m ABUF FL (St cd) 5
  rc : RC4Table m
  h6 : word m HAVE6 = 0
  cb : CbAt m cd
  mu : MuAt m cd
  fr : FrameExcept m0 m [(KS, KS + 800), (KB, KB + 800), (ABUF, FL + 1344), (CB, CB + 1088), (MU, MU + 256)]

theorem I8_one (cd : ByteArray) : I8 cd 1 = seedState 136 (ctOf cd) := rfl

/-- `cext [dst, 1, 17]` after round `j < 2`: block `j` of `H(c̃)`. -/
theorem cb_lane {cd : ByteArray} (hcdN : 5261 ≤ cd.size) {m m' : ByteArray} {j dst : Nat} (hj : j < 2)
    (hks : KS4 m (St cd j))
    (hw : ∀ x, x < 17 → word m' (dst + 32 * x) = cpl x (compress (word m (KS + 32 * x) / 2 ^ 1 &&& spread M64))) :
    ∀ x, x < 17 → word m' (dst + 32 * x) = le64 (cStream cd) (8 * (17 * j + x)) := fun x hx => by
  rw [hw x hx, cext_lane hks (by norm_num) (by omega), St_ne2 cd j (by decide), I8_one,
    S4.le64_cStream (le_trans (by decide) hcdN) hj hx]

theorem cb_of {cd m4 m7 m : ByteArray} {rs1 rs2 : List (Nat × Nat)}
    (hA : ∀ x, x < 17 → word m4 (CB + 32 * x) = le64 (cStream cd) (8 * (17 * 0 + x)))
    (hB : ∀ x, x < 17 → word m7 (CB + 544 + 32 * x) = le64 (cStream cd) (8 * (17 * 1 + x)))
    (hf1 : FrameExcept m4 m rs1) (ha1 : Avoids rs1 CB (CB + 544))
    (hf2 : FrameExcept m7 m rs2) (ha2 : Avoids rs2 (CB + 544) (CB + 1088)) : CbAt m cd := by
  intro x hx
  by_cases h17 : x < 17
  · rw [word_frame hf1 ha1 (a := CB + 32 * x) (by omega) (by omega), hA x h17]
    congr 2; omega
  · rw [show CB + 32 * x = CB + 544 + 32 * (x - 17) by omega,
      word_frame hf2 ha2 (a := CB + 544 + 32 * (x - 17)) (by omega) (by omega), hB _ (by omega)]
    congr 2; omega

/-- `mub (136 (b + 1))` on slot 2 after round `b`. -/
theorem mub_step {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {ret : Nat}
    {tail : List UInt256} (hr : RetOK Stack.mub ret tail) {m : ByteArray} {b : Nat} (hb : b < 5)
    (hks : KS4 m (St s.executionEnv.calldata b)) (hmu : MuW m s.executionEnv.calldata b) :
    ∃ m', KS4 m' (Sb s.executionEnv.calldata (b + 1)) ∧ MuW m' s.executionEnv.calldata (b + 1) ∧
      FrameExcept m m' [(KS, KS + 800), (MU, MU + 256)] ∧
      Call s Entry.mub [wd (136 * (b + 1)), wd 2] ret tail m [] m' Gas.mub := by
  obtain ⟨m', habs, hext, hkeep, heq, hf, hc⟩ := mub_call hs hr m (sh := 2) (k := b + 1) (by norm_num)
    (by omega) (by omega) hcd
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  generalize hcdv : s.executionEnv.calldata = cd at *
  have hN : muN cd = (66 + mlenOf cd) / 136 + 1 := rfl
  refine ⟨m', ?_, ?_, hf, hc⟩
  · by_cases hA : b + 1 < muN cd ∧ b + 1 < 5
    · have hw := habs (trOf cd) (S4.trOf_size _) hA.2 (by omega)
      have h := ks4_xor_slot (sh := 2) (by norm_num) hks
        (fun x => if x < 17 then le64 (muPadded (trOf cd) cd) (136 * (b + 1) + 8 * x) else 0)
        (fun x _ => by split; exact le64_lt _ _; norm_num)
        (fun x hx => by
          rw [hw x hx]
          split
          · rfl
          · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
        (Fips202.xorBlock 136 (muP cd) (136 * (b + 1)) (St cd b 2))
        (fun x _ => laneOf_absorb cd _ (St_sized cd b 2 (by norm_num)) b x)
      exact KS4.congr h fun k _ => (Sb_succ_abs cd hA k).symm
    · have hk : KS4 m' (St cd b) := by
        by_cases hP : 66 + mlenOf cd < 136 * (b + 1)
        · intro x hx; rw [hkeep hP x hx]; exact hks x hx
        · rw [heq (Or.inl ⟨by omega, by omega⟩)]; exact hks
      exact KS4.congr hk fun k _ => (Sb_succ_keep cd hA k).symm
  · intro hn x hx
    by_cases hb' : muN cd ≤ b
    · rw [heq (Or.inr (by omega))]; exact hmu hb' x hx
    · rw [hext (by omega) (by omega) x hx, cext_lane hks (by norm_num) (by omega),
        le64_muOf_St cd hcdN (by omega) (by omega) hx]

/-- `HAVE6 := 0`, `ginit`, `mub0 [2]`. -/
theorem g8_head {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size) {m : ByteArray}
    (hrho : Rho1At m s.executionEnv.calldata) (htrl : TrlAt m s.executionEnv.calldata) (b : Bool) :
    ∃ m2, KS4 m2 (Sb s.executionEnv.calldata 0) ∧ word m2 HAVE6 = 0 ∧
      FrameExcept m m2 [(HAVE6, HAVE6 + 32), (KS, KS + 800), (KS, KS + 800)] ∧
      Reach (callState s 5022 [flag b] m)
        (if mlenOf s.executionEnv.calldata ≤ 69 then callState s 5064 [wd 7066, flag b] m2
          else callState s 7066 [flag b] m2) (33 + Gas.ginit + 21 + Gas.mub0) := by
  have hsz := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  unfold memWords at hsz
  have hcdN : 5261 ≤ s.executionEnv.calldata.size := hcd
  clear hcd
  have hcd32 : 32 ≤ s.executionEnv.calldata.size := by omega
  have g0 : Reach (callState s 5022 [flag b] m)
      (callState s 11987 [wd 0x0111110000010100000100, wd 2, wd 1, wd 0, wd 5051, flag b]
        (MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6)) 33 := by
    opt65_reach [1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642] with [HAVE6]
  generalize hm0 : MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) HAVE6 = m0 at g0
  have hf0 : FrameExcept m m0 [(HAVE6, HAVE6 + 32)] := hm0 ▸ FrameExcept.mstore m HAVE6 0
  have h60 : word m0 HAVE6 = 0 := hm0 ▸ word_mstore m HAVE6 0 (by norm_num)
  obtain ⟨m1, hg, hf1, hc1⟩ := ginit_call hs (ret := 5051) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m0
    (keep := 0) (amult := 1) (cmult := 2) (l4 := 0x0111110000010100000100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hrho0 := Rho1At.frame hrho hf0 (by g57_frame)
  have hks1 : KS4 m1 (I8 s.executionEnv.calldata) :=
    S4.ks4_ginit (kmask := 0)
      (L := fun k => if k = 0 then 4 + 256 * 5 + 0x1F0000 else 0)
      (ρ := fun x => le64 s.executionEnv.calldata (8 * x)) (c := fun x => le64 s.executionEnv.calldata (CTOFF + 8 * x)) (S := I8 s.executionEnv.calldata)
      (by norm_num) (by norm_num) (il_eq_zero fun k _ => by simp).symm (by decide +kernel)
      (fun x hx => hrho0.1 x hx) (fun x hx => hrho0.2 x hx)
      (fun x _ => by rw [Nat.and_zero]; exact (il_eq_zero fun k _ => by simp).symm)
      (fun _ => le64_lt _ _) (fun _ => le64_lt _ _) (fun k _ => by split <;> omega)
      (fun k _ h => by simp at h) (fun k _ h => by simp at h)
      (fun k hk _ x hx => by
        interval_cases k
        · show _ = laneOf (seedState 168 (aSeed s.executionEnv.calldata 5 4)) x
          exact S4.freshLane_aSeed hcd32 (fun _ _ => rfl) (by norm_num) (by norm_num) (by decide)
            (by decide) (by norm_num) hx
        · show _ = laneOf (seedState 136 (ctOf s.executionEnv.calldata)) x
          exact S4.freshLane_ctSeed (le_trans (by decide) hcdN) (fun _ _ => rfl) (by decide) (by decide) (by norm_num) hx
        · show _ = laneOf Fips202.emptyState x
          exact S4.freshLane_zero (by decide) (by decide) (by norm_num) x
        · show _ = laneOf Fips202.emptyState x
          exact S4.freshLane_zero (by decide) (by decide) (by norm_num) x)
      hg
  have g1 : Reach (callState s 5051 [flag b] m1)
      (callState s 13365 [wd 2, wd 5064, wd 7066, flag b] m1) 21 := by
    opt65_reach [1643, 1644, 1645, 1646, 1647, 1648]
  obtain ⟨m2, hpost, hf2, hc2⟩ := mub0_call hs (rl := 7066) (rs := 5064) (tail := [flag b])
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num))
    (retOK_main (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) m1
    (sh := 2) (by norm_num) hcdN
  have htrl1 : ∀ x, x < 8 → word m1 (TRL + 32 * x) = le64 (trOf s.executionEnv.calldata) (8 * x) := fun x hx => by
    rw [word_frame (hf0.trans hf1) (lo := TRL) (hi := TRL + 256) (by g57_frame) (by omega) (by omega)]
    exact htrl x hx
  have hw := hpost (trOf s.executionEnv.calldata) (S4.trOf_size _) htrl1
  have hks2 : KS4 m2 (Sb s.executionEnv.calldata 0) := by
    have h := ks4_xor_slot (sh := 2) (by norm_num) hks1
      (fun x => if x < 17 then le64 (mu0Bytes (trOf s.executionEnv.calldata) s.executionEnv.calldata) (8 * x) else 0)
      (fun x _ => by split; exact le64_lt _ _; norm_num)
      (fun x hx => by
        rw [hw x hx]
        split
        · rfl
        · rw [spread_zero, Nat.zero_mul, Nat.xor_zero])
      (muT s.executionEnv.calldata 0) (fun x _ => by
        rw [laneOf_muT0, show I8 s.executionEnv.calldata 2 = Fips202.emptyState from rfl]
        by_cases h : x < 17
        · simp only [h, if_true]; rw [le64_mu0Bytes _ hcdN h]
        · simp only [h, if_false])
    exact KS4.congr h fun k _ => by unfold Sb; rfl
  refine ⟨m2, hks2, ?_, (hf0.trans hf1).trans hf2, ((g0.trans hc1).trans g1).trans hc2⟩
  rw [word_frame (hf1.trans hf2) (lo := HAVE6) (hi := HAVE6 + 32) (by g57_frame) le_rfl le_rfl]
  exact h60

end MlDsaOpt65.Proofs.Exp
