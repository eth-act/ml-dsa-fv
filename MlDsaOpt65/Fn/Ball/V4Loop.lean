import MlDsaOpt65.Fn.Ball.V4Run
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, ML-DSA-65): the scan over the stream and the contract body

As `MlDsaOpt44/Fn/Ball/V4Loop.lean` without the on-demand second block: both
blocks are in `CB` on entry, and at `o = 0x440` (stream position 272) the
routine returns `0`. `sib_loop` recurses over the stream positions
`p = 8 … 272` with the potential `pot p i` (rejected bytes still ahead, `353`
per coefficient still to place, the failure exit). The `BASES` words start
zeroed (`SibFresh`), so the slots the scan has not written stay in range. -/

namespace MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

namespace Ball4

open MlDsaOptCommon.BallScan (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv sampleInBallOf_eq)

/-- Cost potential at stream position `p` with index `i`. -/
def pot (p i : Nat) : Nat := rs p + 353 * (256 - i) + 43

theorem rlOf_jd (r : Nat) (hr : r < 8) :
    Decode.isValidJumpDest MlDsaOpt65.optBytecode (rlOf r) = true := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;> simp only [rlOf, Nat.reduceMul, Nat.reduceAdd, Infra.isValidJumpDest_lit]

theorem rs_ge (p : Nat) (hp : p < 272) : rc (p % 8) ≤ rs p := by
  rw [rs_succ hp]; omega

theorem pot_bound {A R i : Nat} (h2 : A ≤ 83) (h3 : 40 ≤ R) (h4 : i + 1 = 256) :
    A + 350 ≤ R + 353 * (256 - i) + 43 := by omega

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem sib_loop (hs : Ctx s) (hr : RetOK Stack.sib ret tail) (hsized : 2865 ≤ s.activeWords.toNat)
    (m bs : ByteArray) (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x)) :
    ∀ n p z M, n = 272 - p → 8 ≤ p → p ≤ 272 → (ballFold P bs (p - 8)).2 < 256 →
      SInv m M (ballFold P bs (p - 8)).1 (ballFold P bs (p - 8)).2 →
      ∃ M' k', k' ≤ 264 ∧ SInv m M' (ballFold P bs k').1 (ballFold P bs k').2 ∧
        ballFold P bs 264 = ballFold P bs k' ∧
        Reach (posSt s ret tail bs p (ballFold P bs (p - 8)).2 z M)
          (callState s ret (wd (if (ballFold P bs 264).2 < 256 then 0 else 1) :: tail) M')
          (pot p (ballFold P bs (p - 8)).2)
  | 0, p, z, M, hn, hp8, hp, hlt, hinv => by
    have hp272 : p = 272 := by omega
    subst hp272
    have htail : tail.length ≤ 960 := by
      have := hr.depth; simp only [Stack.sib, Stack.leaf] at this; omega
    refine ⟨M, 264, le_rfl, hinv, rfl, ?_⟩
    rw [if_pos hlt]
    unfold posSt
    rw [if_pos (by norm_num)]
    exact (b_fail hs htail hsized M hr.jumpdest hr.small _ _).mono (by unfold pot; omega)
  | n + 1, p, z, M, hn, hp8, hp, hlt, hinv => by
    have htail : tail.length ≤ 960 := by
      have := hr.depth; simp only [Stack.sib, Stack.leaf] at this; omega
    have hp272 : p < 272 := by omega
    obtain ⟨hsz, hi1, hi2, -⟩ := ballFold_inv P bs (p - 8)
    have hhigh := ballFold_high bs (p - 8)
    have hsucc := ballFold_succ P bs (p - 8)
    rw [show 8 + (p - 8) = p by omega, show p - 8 + 1 = p + 1 - 8 by omega] at hsucc
    rcases hF : ballFold P bs (p - 8) with ⟨c, i⟩
    rw [hF] at hsz hi1 hi2 hhigh hsucc hlt hinv
    simp only at hsz hi1 hi2 hhigh hlt hinv ⊢
    have hi1' : 207 ≤ i := by have : P.tau = 49 := rfl; omega
    have hw : p % 8 = 0 → word M (88064 + 4 * p) = le64 bs p := fun h8 => by
      rw [show 88064 + 4 * p = CB + 32 * (p / 8) by simp only [CB]; omega,
        hinv.frame.word (by simp [CW, BASES, IDX, NNEG, CB]; omega), hcb _ (by omega),
        show 8 * (p / 8) = p by omega]
    have hrs := rs_succ hp272
    by_cases hacc : bs[p]!.toNat ≤ i
    · -- accept
      have hst : ballFold P bs (p + 1 - 8) = (ballSet P bs c i bs[p]!.toNat, i + 1) := by
        rw [hsucc]; unfold ballStep; rw [if_pos ⟨hlt, hacc⟩]
      have hA := byte_acc (ret := ret) (z := z) hs htail hsized bs M hp272 hw hacc hlt
      obtain ⟨M', hfr', hinv', hmid, hend⟩ := acc_chain (ret := ret) (rl := rlOf (p % 8))
        (w := le64 bs (p - p % 8)) (o := 4 * (p - p % 8)) hs htail hsized hr.jumpdest hr.small bs hinv
        hsz hi1' hlt hacc hhigh (rlOf_jd _ (Nat.mod_lt _ (by norm_num))) (by simp only [rlOf]; omega)
      have hinv'' : SInv m M' (ballFold P bs (p + 1 - 8)).1 (ballFold P bs (p + 1 - 8)).2 := by
        rw [hst]; exact hinv'
      have hcost : acost (p % 8) + 336 + (if p % 8 = 7 then 22 else 0) = rc (p % 8) + 353 := by
        unfold acost rc; split_ifs <;> omega
      by_cases hlast : i + 1 < 256
      · obtain ⟨M'', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr hsized m bs hcb n
          (p + 1) (rlOf (p % 8)) M' (by omega) (by omega) (by omega) (by rw [hst]; exact hlast) hinv''
        rw [hst] at hreach
        refine ⟨M'', k', hk', hinvF, hfold, ?_⟩
        have hB := acc_back (ret := ret) (i := i) hs htail hsized bs M' hp272
        exact (hA.trans ((hmid hlast).trans (hB.trans hreach))).mono (by unfold pot; omega)
      · have hfold : ballFold P bs 264 = ballFold P bs (p + 1 - 8) := by
          have := ballFold_stop bs (p + 1 - 8) (by rw [hst]; simp only; omega) (264 - (p + 1 - 8))
          rwa [show p + 1 - 8 + (264 - (p + 1 - 8)) = 264 by omega] at this
        refine ⟨M', p + 1 - 8, by omega, hinv'', hfold, ?_⟩
        rw [hfold, hst, if_neg (by simp only; omega)]
        have hle : acost (p % 8) ≤ 83 := by unfold acost; split <;> omega
        have hge := rs_ge p hp272
        have hi255 : i + 1 = 256 := by omega
        refine (hA.trans (hend hi255)).mono ?_
        have h40 : 40 ≤ rs p := le_trans (by unfold rc; split_ifs <;> omega) hge
        unfold pot
        exact pot_bound hle h40 hi255
    · -- reject
      have hst : ballFold P bs (p + 1 - 8) = (c, i) := by
        rw [hsucc]; unfold ballStep; rw [if_neg (fun h => hacc h.2)]
      have hR := byte_rej (ret := ret) (z := z) hs htail hsized bs M hp272 hw (by omega) hlt
      obtain ⟨M', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr hsized m bs hcb n
        (p + 1) bs[p]!.toNat M (by omega) (by omega) (by omega) (by rw [hst]; exact hlt)
        (by rw [hst]; exact hinv)
      rw [hst] at hreach
      refine ⟨M', k', hk', hinvF, hfold, ?_⟩
      exact (hR.trans hreach).mono (by unfold pot; omega)

end

/-- The final invariant is `CRep`. -/
theorem crep_of_sinv {m M : ByteArray} {c : Fips204.Poly} (h : SInv m M c 256) : CRep M c := by
  obtain ⟨-, hcw, hnneg, -, ⟨f, finj, fmem, fslot⟩, -, -⟩ := h
  have hget : ∀ s, s < 49 → ((List.range 49).map f)[s]! = f s := fun s hs => by
    rw [getElem!_pos ((List.range 49).map f) s (by simp; omega)]
    simp
  refine ⟨hcw, hnneg, (List.range 49).map f, by rw [List.length_map, List.length_range]; rfl, ?_, fun p => ?_, fun s hs => ?_⟩
  · exact List.Nodup.map_on (fun x hx y hy e => finj x y (by simpa using hx) (by simpa using hy) e)
      List.nodup_range
  · rw [← fmem p]; simp [List.mem_map, List.mem_range]
  · simp only [P] at hs
    rw [hget s hs]; exact (fslot s hs).1

theorem bases_le {m M : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i) (s : Nat)
    (hs : s < 49) : word M (BASES + 32 * s) ≤ 6112 := by
  obtain ⟨-, -, -, -, ⟨f, -, fmem, fslot⟩, -, hfree⟩ := h
  by_cases hsn : s < i - 207
  · rw [(fslot s hsn).1]
    have := baseOf_le c (f s) ((fmem (f s)).1 ⟨s, hsn, rfl⟩).1
    omega
  · exact hfree s (by omega) hs

end Ball4

open Ball4 MlDsaOptCommon.BallScan in
/-- The `sib` contract body (statement of `sib_call`). -/
theorem sib_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 34 → word m (CB + 32 * x) = le64 bs (8 * x)) (hz : SibFresh m) :
    ∃ m', (∀ c, Fips204.sampleInBallOf P bs = some c → CRep m' c) ∧
      (∀ i, i < P.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(CW, CW + 8192), (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf P bs).isSome] m' Gas.sib := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.sib, Stack.leaf] at this; omega
  have hsized : 2865 ≤ s.activeWords.toNat := hs.sized
  have hentry := b_entry (ret := ret) hs htail hsized m
  have h0 : SInv m m (ballFold P bs (8 - 8)).1 (ballFold P bs (8 - 8)).2 := by
    rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P]
    exact sinv_init m hz
  obtain ⟨M', k', hk', hinv, hfold, hreach⟩ := sib_loop (ret := ret) hs hr hsized m bs hcb
    264 8 0 m rfl (by omega) (by omega)
    (by rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P]; decide) h0
  rw [show 8 - 8 = 0 from rfl, MlDsaOptCommon.BallScan.ballFold_zero P] at hreach
  change Reach (posSt s ret tail bs 8 207 0 m) _ (pot 8 207) at hreach
  refine ⟨M', fun c hc => ?_, fun i hi => bases_le hinv i (by have : P.tau = 49 := rfl; omega),
    hinv.frame, ?_⟩
  · rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P] at hc
    split at hc
    · exact absurd hc (by simp)
    · rename_i hge
      simp only [Option.some.injEq] at hc
      subst hc
      rw [hfold] at hge ⊢
      have hi2 := (MlDsaOptCommon.BallScan.ballFold_inv P bs k').2.2.1
      have h256 : (ballFold P bs k').2 = 256 := by omega
      rw [h256] at hinv
      exact crep_of_sinv hinv
  · rw [call_iff, Entry.sib]
    have hflag : flag (Fips204.sampleInBallOf P bs).isSome =
        wd (if (ballFold P bs 264).2 < 256 then 0 else 1) := by
      rw [MlDsaOptCommon.BallScan.sampleInBallOf_eq P]
      by_cases h : (ballFold P bs 264).2 < 256 <;> simp [h, flag]
    rw [hflag]
    have hst : posSt s ret tail bs 8 207 0 m = headSt s ret tail 32 207 (word m 88064) m := by
      unfold posSt sgw
      rw [if_pos (by norm_num), show word m 88064 = le64 bs 0 by
        have := hcb 0 (by omega); simpa [CB] using this]
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
    rw [hst] at hreach
    refine ((hentry.trans hreach).mono ?_).of_eq rfl rfl
    unfold pot Gas.sib
    rw [rs_8]

end MlDsaOpt65.Proofs
