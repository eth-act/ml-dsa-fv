import MlDsaOptGlam65.Fn.Ball.V4Scan
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Fn/Ball/V4Run.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, ML-DSA-65): the accept step

`acc_chain`: an accepted byte (blocks `A`, `B`, `C`/`D`) on the invariant. -/

namespace MlDsaOptGlam65.Proofs

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Ball4

open MlDsaOpt65.Proofs

open MlDsaOptCommon.BallScan (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv sampleInBallOf_eq)

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem code_eq (sg : Nat) (hsg : sg ≤ 1) :
    UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) -
        UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 =
      UInt256.ofNat (if sg = 1 then REP else 2 ^ 256 - REP) := by
  rw [REP_val]
  rcases (by omega : sg = 0 ∨ sg = 1) with h | h <;> subst h <;> decide

/-- One accepted byte `j` at index `i`: the shared accept step on the invariant. -/
theorem acc_chain (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 3384 ≤ s.activeWords.toNat)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode ret = true) (hret : ret < 2 ^ 16)
    {m M : ByteArray} {c : Fips204.Poly} {i j rl w o : Nat} (bs : ByteArray)
    (h : SInv m M c i) (hsz : c.size = 256) (hi1 : 207 ≤ i) (hi : i < 256) (hji : j ≤ i)
    (hhigh : ∀ t, i ≤ t → c[t]! = 0)
    (hrl : Decode.isValidJumpDest MlDsaOptGlam65.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    ∃ M', FrameExcept M M' sibRegions ∧
      SInv m M' (ballSet P bs c i j) (i + 1) ∧
      (i + 1 < 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (sgw bs (i + 1)) :: wd ret :: tail) M') 336) ∧
      (i + 1 = 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s ret (wd 1 :: tail) M') 350) := by
  have hsg := sign_bit bs (i - 207) (by omega)
  have hsg1 : Fips204.bit bs (i - 207) ≤ 1 := by unfold Fips204.bit; omega
  have hset : ballSet P bs c i j = (c.set! i c[j]!).set! j (sgnOf (Fips204.bit bs (i - 207))) := by
    unfold ballSet ballSign sgnOf
    rw [show i + P.tau - 256 = i - 207 by rw [show P.tau = 49 from rfl]; omega]
  rw [hset]
  generalize Fips204.bit bs (i - 207) = sg at hsg1 hsg
  have hcode := code_eq sg hsg1
  have hcode' : (if sg = 1 then REP else 2 ^ 256 - REP) < 2 ^ 256 := by
    rw [REP_val]; split <;> norm_num
  have hnn : word M 4000 = negCount c := h.nneg
  have hnn' : negCount c ≤ 256 := by rw [negCount_eq]; exact cntTo_le c 256
  obtain ⟨hkf, hcntB, hfrA, hinv'⟩ := sinv_accept (nn := negCount c)
    (code := if sg = 1 then REP else 2 ^ 256 - REP) h hsz hi1 hi hji hhigh hsg1 rfl rfl
  have hsigns : sgw bs i < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans (le64_lt bs 0) (by norm_num))
  have hAB : Reach (accSt s ret tail j rl w o i (sgw bs i) M)
      (callState s 7691 (wd (byteAt M (IDX + j)) :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i ::
        wd (sgw bs i) :: wd ret :: tail)
        (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP))) 193 := by
    by_cases hk0 : byteAt M (IDX + j) = 0
    · have hMB : sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP) =
          memA M i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP) := by
        unfold sibMB; rw [if_pos hk0]
      rw [hMB, hk0]
      exact (b_accA0 hs htail hsized M rl w o i _ hi j hji sg hsg hsg1 _ hnn hnn' _ hcode hcode'
        hk0).mono (by omega)
    · obtain ⟨hk40, hbv⟩ := hkf hk0
      have hMB : sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP) =
          memB (memA M i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) i j
            (byteAt M (IDX + j)) (baseOf c j) := by
        unfold sibMB; rw [if_neg hk0]
      rw [hMB]
      exact (b_accA1 hs htail hsized M rl w o i _ hi j hji sg hsg hsg1 _ hnn hnn' _ hcode hcode'
        (byteAt M (IDX + j)) rfl (by omega) (by omega)).trans
        (b_accB hs htail hsized _ rl w o i _ j sg _ hi hji (by omega) _ hbv
          (by have := baseOf_le c j (by omega); omega))
  refine ⟨_, hfrA, hinv', fun hlast => ?_, fun hlast => ?_⟩
  · have hC := b_accC (ret := ret) hs htail hsized
      (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) rl w o i (sgw bs i) j sg
      (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 207) hcntB (by omega) hrl hrl'
    rw [sgw_succ bs hi1] at hC
    exact hAB.trans hC
  · exact hAB.trans (b_accD hs htail hsized
      (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) hjd hret rl w o i
      (sgw bs i) j sg (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 207) hcntB (by omega))

end

end Ball4

end MlDsaOptGlam65.Proofs
