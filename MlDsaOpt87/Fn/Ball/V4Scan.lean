import MlDsaOpt87.Fn.Ball.V4Proof
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, ML-DSA-87): one stream position, the accept step, the squeeze

A position `p` (`8 ≤ p < 272`, byte `p` of the stream) is the loop head when
`p ≡ 0 (mod 8)` and the test of byte `p mod 8` of the lane otherwise (`posSt`); the
test of byte 0 is at `sibnok`, after the head's visit (`tstSt`). `byte_rej`, `byte_acc`
and `acc_back` move from position `p` to `p + 1` for a rejected byte, and into and out
of the shared accept step (`acc_chain`). The lane word is the replicated stream lane
`rep (le64 bs (p − p mod 8))`. `sq_step`: at `o = 544` (`p = 136`) the head
re-complements `KS`, runs `kf1` (the second block) and un-complements it. -/

namespace MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOpt87.Proofs.Infra

namespace Ball4

open MlDsaOptCommon.BallScan (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv sampleInBallOf_eq)

/-- Cost of the test of a rejected byte at lane offset `r` (`r = 0`: from `sibnok`). -/
def tc (r : Nat) : Nat := if r = 0 then 49 else if r = 7 then 62 else 40

/-- Cost of a rejected byte at lane offset `r`, with the loop head's visit (`48`) for `r = 0`. -/
def rc (r : Nat) : Nat := if r = 0 then 97 else if r = 7 then 62 else 40

/-- Cost of the rejected bytes `p … 271`. -/
def rs (p : Nat) : Nat := ((List.range (272 - p)).map fun d => rc ((p + d) % 8)).sum

theorem rs_succ {p : Nat} (hp : p < 272) : rs p = rc (p % 8) + rs (p + 1) := by
  unfold rs
  rw [show 272 - p = (272 - (p + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, List.map_map, Nat.add_zero]
  congr 2
  apply List.map_congr_left
  intro d _
  simp only [Function.comp]
  congr 2; omega

theorem rs_8 : rs 8 = 13167 := by decide +kernel

/-- The sign word after `i − 196` accepted bytes. -/
abbrev sgw (bs : ByteArray) (i : Nat) : Nat := le64 bs 0 / 2 ^ (i - 196)

/-- The state at stream position `p`. -/
def posSt (s : State) (ret : Nat) (tail : List UInt256) (bs : ByteArray) (p i z : Nat) (M : ByteArray) :
    State :=
  if p % 8 = 0 then headSt s ret tail (4 * p) i (sgw bs i) M
  else skipSt s ret tail (p % 8) z (rep (le64 bs (p - p % 8))) (4 * (p - p % 8)) i (sgw bs i) M

/-- The state of the test of byte `p` (for `p ≡ 0 (mod 8)` after the head's visit). -/
def tstSt (s : State) (ret : Nat) (tail : List UInt256) (bs : ByteArray) (p i z : Nat) (M : ByteArray) :
    State :=
  if p % 8 = 0 then nokSt s ret tail (4 * p) i (sgw bs i) M
  else skipSt s ret tail (p % 8) z (rep (le64 bs (p - p % 8))) (4 * (p - p % 8)) i (sgw bs i) M

theorem sgw_succ (bs : ByteArray) {i : Nat} (hi : 196 ≤ i) : sgw bs i / 2 = sgw bs (i + 1) := by
  unfold sgw
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (i - 196).succ = i + 1 - 196 by omega]

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem byte_rej (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i z : Nat} (hp : p < 272)
    (hw : p % 8 = 0 → word M (4 * p % 544) = rep (le64 bs p))
    (hji : i < bs[p]!.toNat) (hi : i < 256) :
    Reach (tstSt s ret tail bs p i z M) (posSt s ret tail bs (p + 1) i bs[p]!.toNat M) (tc (p % 8)) := by
  have hj' : bs[p]!.toNat < 256 := UInt8.toNat_lt _
  have hb := rep_lane_byte bs (p := p) rfl
  have hwl : rep (le64 bs (p - p % 8)) < 2 ^ 256 := rep_lt (le64_lt _ _)
  unfold tstSt posSt
  have h8 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨
    p % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hb hwl ⊢ <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.sub_zero, Nat.div_one] at hb hwl
  · rw [if_pos rfl, if_neg (by omega), show (p + 1) % 8 = 1 by omega, show p + 1 - 1 = p by omega]
    exact b_nok_rej hs htail hsized M (4 * p) i _ _ _ (by omega) (hw h) hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 2 by omega,
      show p + 1 - 2 = p - 1 by omega]
    exact b_skip_rej1 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 3 by omega,
      show p + 1 - 3 = p - 2 by omega]
    exact b_skip_rej2 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 4 by omega,
      show p + 1 - 4 = p - 3 by omega]
    exact b_skip_rej3 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 5 by omega,
      show p + 1 - 5 = p - 4 by omega]
    exact b_skip_rej4 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 6 by omega,
      show p + 1 - 6 = p - 5 by omega]
    exact b_skip_rej5 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_neg (by omega), show (p + 1) % 8 = 7 by omega,
      show p + 1 - 7 = p - 6 by omega]
    exact b_skip_rej6 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega), if_pos (by omega)]
    have h' := b_skip_rej7 (ret := ret) hs htail hsized M z _ (4 * (p - 7)) i (sgw bs i) _ hwl hb hji hj' hi
    rw [show 32 + 4 * (p - 7) = 4 * (p + 1) by omega] at h'
    exact h'

/-- The return label of the accept step for lane offset `r`. -/
abbrev rlOf (r : Nat) : Nat := 8865 + 24 * r

/-- Cost of an accepted byte's test. -/
def acost (r : Nat) : Nat := if r = 0 then 66 else 57

theorem byte_acc (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i z : Nat} (hp : p < 272)
    (hw : p % 8 = 0 → word M (4 * p % 544) = rep (le64 bs p))
    (hji : bs[p]!.toNat ≤ i) (hi : i < 256) :
    Reach (tstSt s ret tail bs p i z M)
      (accSt s ret tail bs[p]!.toNat (rlOf (p % 8)) (rep (le64 bs (p - p % 8))) (4 * (p - p % 8)) i
        (sgw bs i) M)
      (acost (p % 8)) := by
  have hj' : bs[p]!.toNat < 256 := UInt8.toNat_lt _
  have hb := rep_lane_byte bs (p := p) rfl
  have hwl : rep (le64 bs (p - p % 8)) < 2 ^ 256 := rep_lt (le64_lt _ _)
  unfold tstSt
  have h8 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨
    p % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at hb hwl ⊢ <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.sub_zero, Nat.div_one] at hb hwl
  · rw [if_pos rfl]
    exact b_nok_acc hs htail hsized M (4 * p) i _ _ _ (by omega) (hw h) hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc1 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc2 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc3 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc4 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc5 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc6 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi
  · rw [if_neg (by omega)]
    exact b_skip_acc7 hs htail hsized M z _ _ i _ _ hwl hb hji hj' hi

/-- Back from the accept step to position `p + 1`. -/
theorem acc_back (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat)
    (bs M : ByteArray) {p i : Nat} (hp : p < 272) :
    Reach (callState s (rlOf (p % 8)) (wd (rlOf (p % 8)) :: wd (rep (le64 bs (p - p % 8))) ::
        wd (4 * (p - p % 8)) :: wd (i + 1) :: wd (sgw bs (i + 1)) :: wd ret :: tail) M)
      (posSt s ret tail bs (p + 1) (i + 1) (rlOf (p % 8)) M) (if p % 8 = 7 then 22 else 0) := by
  unfold posSt
  by_cases h7 : p % 8 = 7
  · rw [if_pos h7, if_pos (by omega), h7]
    have h := b_tail8 (ret := ret) hs htail hsized M (rlOf 7) (rep (le64 bs (p - 7))) (4 * (p - 7))
      (i + 1) (sgw bs (i + 1))
    rw [show 32 + 4 * (p - 7) = 4 * (p + 1) by omega] at h
    exact h
  · rw [if_neg h7, if_neg (by omega), show (p + 1) % 8 = p % 8 + 1 by omega,
      show p + 1 - (p % 8 + 1) = p - p % 8 by omega]
    refine (Reach.refl _).of_eq rfl ?_
    simp only [skipSt, skipPc, rlOf, Nat.add_sub_cancel]

theorem code_eq (sg : Nat) (hsg : sg ≤ 1) :
    UInt256.ofNat (12554203470773361528352143580257209759168353591939024551938 * sg) -
        UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969 =
      UInt256.ofNat (if sg = 1 then REP else 2 ^ 256 - REP) := by
  rw [REP_val]
  rcases (by omega : sg = 0 ∨ sg = 1) with h | h <;> subst h <;> decide

/-- One accepted byte `j` at index `i`: the shared accept step on the invariant. -/
theorem acc_chain (hs : Ctx s) (htail : tail.length ≤ 960) (hsized : 2897 ≤ s.activeWords.toNat)
    (hjd : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true) (hret : ret < 2 ^ 16)
    {m M : ByteArray} {c : Fips204.Poly} {i j rl w o : Nat} (bs : ByteArray)
    (h : SInv m M c i) (hsz : c.size = 256) (hi1 : 196 ≤ i) (hi : i < 256) (hji : j ≤ i)
    (hhigh : ∀ t, i ≤ t → c[t]! = 0)
    (hrl : Decode.isValidJumpDest MlDsaOpt87.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    ∃ M', (∀ S, KSU M S → KSU M' S) ∧
      SInv m M' (ballSet P bs c i j) (i + 1) ∧
      (i + 1 < 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (sgw bs (i + 1)) :: wd ret :: tail) M') 336) ∧
      (i + 1 = 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s ret (wd 1 :: tail) M') 350) := by
  have hsg := sign_bit bs (i - 196) (by omega)
  have hsg1 : Fips204.bit bs (i - 196) ≤ 1 := by unfold Fips204.bit; omega
  have hset : ballSet P bs c i j = (c.set! i c[j]!).set! j (sgnOf (Fips204.bit bs (i - 196))) := by
    unfold ballSet ballSign sgnOf
    rw [show i + P.tau - 256 = i - 196 by simp only [tau_eq]; omega]
  rw [hset]
  generalize Fips204.bit bs (i - 196) = sg at hsg1 hsg
  have hcode := code_eq sg hsg1
  have hcode' : (if sg = 1 then REP else 2 ^ 256 - REP) < 2 ^ 256 := by
    rw [REP_val]; split <;> norm_num
  have hnn : word M 4000 = negCount c := h.nneg
  have hnn' : negCount c ≤ 256 := by rw [negCount_eq]; exact cntTo_le c 256
  obtain ⟨hkf, hcntB, hinv'⟩ := sinv_accept (nn := negCount c)
    (code := if sg = 1 then REP else 2 ^ 256 - REP) h hsz hi1 hi hji hhigh hsg1 rfl rfl
  have hsigns : sgw bs i < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans (le64_lt bs 0) (by norm_num))
  have hAB : Reach (accSt s ret tail j rl w o i (sgw bs i) M)
      (callState s 9177 (wd (byteAt M (IDX + j)) :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i ::
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
  refine ⟨_, fun S hK => ksu_scan hK c, hinv', fun hlast => ?_, fun hlast => ?_⟩
  · have hC := b_accC (ret := ret) hs htail hsized
      (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) rl w o i (sgw bs i) j sg
      (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 196) hcntB (by omega) hrl hrl'
    rw [sgw_succ bs hi1] at hC
    exact hAB.trans hC
  · exact hAB.trans (b_accD hs htail hsized
      (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) hjd hret rl w o i
      (sgw bs i) j sg (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 196) hcntB (by omega))

/-- Cost of the visit at `o = 544` beyond the plain visit (`48`): the second block. -/
def sqX : Nat := 136 + Gas.kf1

/-- At `o = 544`: re-complement, `kf1` (the second block), un-complement. -/
theorem sq_step (hs : Ctx s) (hr : RetOK Stack.sib ret tail) (htail : tail.length ≤ 960)
    {M : ByteArray} (hrc : RC1Table M) {cd : ByteArray} (hK : KSU M (permN 1 (S0 cd))) (i sg : Nat) :
    ∃ M1, KSU M1 (permN 2 (S0 cd)) ∧
      FrameExcept M M1 [(KS, KS + 800), (KB, KB + 800), (KZ, KZ + 800)] ∧
      Reach (headSt s ret tail 544 i sg M) (nokSt s ret tail 544 i sg M1) (48 + sqX) := by
  obtain ⟨M2, h2, f2, r2⟩ := sib_rpre hs htail M i sg
  have hK2 : KS1 M2 (permN 1 (S0 cd)) := ks1_of_flip hK h2
  obtain ⟨M3, h3, f3, c3⟩ := kf1_call hs (ret := 8805)
    (tail := [wd 544, wd i, wd sg, wd ret] ++ tail)
    (hr.callee (by simp [Stack.sib, Stack.kf1, Stack.leaf]) (by simp only [isValidJumpDest_lit])
      (by norm_num)) M2
    (fun a ha => by
      rw [f2.word (by simp only [avoids_cons, avoids_nil, and_true, KS, RC1]; omega)]
      exact hrc a ha)
  rw [call_iff] at c3
  have hK3 : KS1 M3 (permN 2 (S0 cd)) := by
    rw [permN_succ']
    exact h3 _ (MlDsaOpt44.Proofs.permN_size (MlDsaOpt44.Proofs.seedState_size _ _) 1) hK2
  obtain ⟨M4, h4, f4, r4⟩ := sib_rpost hs htail M3 i sg
  refine ⟨M4, ksu_of_flip hK3 h4, ?_, ?_⟩
  · refine ((f2.trans f3).trans f4).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h <;> subst h <;> simp
  · exact ((r2.trans c3).trans r4).mono (by unfold sqX; omega)

end

end Ball4

end MlDsaOpt87.Proofs
