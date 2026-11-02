import MlDsaOptGlam44.Fn.Ball.Scan
import MlDsaOptGlam44.Fn.Keccak
import MlDsaOptGlam44.Fn.Sponge
import MlDsaOpt44.Math.SpongeG234
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (glam): accept step and the `sibext` test

`acc_chain`: an accepted byte (blocks `A`, `B`, `C`/`D`) on the invariant (v4's).
`ext_flag0`: with `FLAG = 0` copy 0's head at `o = 544` goes straight to copy 1.
`ext_flag1`: with `FLAG = 1` it first copies c's saved kf4 states from `SC` to
`KS`, permutes them and extracts slot 0 into `CB[17, 34)`. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

namespace Ball4

open MlDsa44.Proofs.Sampling (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
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
theorem acc_chain (hs : Ctx s) (htail : tail.length ≤ 886) (hsized : 2616 ≤ s.activeWords.toNat)
    (hjd : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode ret = true) (hret : ret < 2 ^ 16)
    {rs : List (Nat × Nat)} {m M : ByteArray} {c : Fips204.Poly} {i j rl w o : Nat} (bs : ByteArray)
    (hrs : ∀ a, (∀ r ∈ rs, a < r.1 ∨ r.2 ≤ a) → ∀ r ∈ sibRegions, a < r.1 ∨ r.2 ≤ a)
    (h : SInv rs m M c i) (hsz : c.size = 256) (hi1 : 217 ≤ i) (hi : i < 256) (hji : j ≤ i)
    (hhigh : ∀ t, i ≤ t → c[t]! = 0)
    (hrl : Decode.isValidJumpDest MlDsaOptGlam44.optBytecode rl = true) (hrl' : rl < 2 ^ 16) :
    ∃ M', FrameExcept M M' sibRegions ∧
      SInv rs m M' (ballSet bs c i j) (i + 1) ∧
      (i + 1 < 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s rl (wd rl :: wd w :: wd o :: wd (i + 1) :: wd (sgw bs (i + 1)) :: wd ret :: tail) M') 336) ∧
      (i + 1 = 256 → Reach (accSt s ret tail j rl w o i (sgw bs i) M)
        (callState s ret (wd 1 :: tail) M') 350) := by
  have hsg := sign_bit bs (i - 217) (by omega)
  have hsg1 : Fips204.bit bs (i - 217) ≤ 1 := by unfold Fips204.bit; omega
  have hset : ballSet bs c i j = (c.set! i c[j]!).set! j (sgnOf (Fips204.bit bs (i - 217))) := by
    unfold ballSet ballSign sgnOf
    rw [show i + Fips204.tau - 256 = i - 217 by simp only [Fips204.tau]; omega]
  rw [hset]
  generalize Fips204.bit bs (i - 217) = sg at hsg1 hsg
  have hcode := code_eq sg hsg1
  have hcode' : (if sg = 1 then REP else 2 ^ 256 - REP) < 2 ^ 256 := by
    rw [REP_val]; split <;> norm_num
  have hnn : word M 4000 = negCount c := h.nneg
  have hnn' : negCount c ≤ 256 := by rw [negCount_eq]; exact cntTo_le c 256
  obtain ⟨hkf, hcntB, hfrA, hinv'⟩ := sinv_accept (nn := negCount c)
    (code := if sg = 1 then REP else 2 ^ 256 - REP) hrs h hsz hi1 hi hji hhigh hsg1 rfl rfl
  have hsigns : sgw bs i < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans (le64_lt bs 0) (by norm_num))
  have hAB : Reach (accSt s ret tail j rl w o i (sgw bs i) M)
      (callState s 8165 (wd (byteAt M (IDX + j)) :: wd sg :: wd j :: wd rl :: wd w :: wd o :: wd i ::
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
      (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 217) hcntB (by omega) hrl hrl'
    rw [sgw_succ bs hi1] at hC
    exact hAB.trans hC
  · exact hAB.trans (b_accD hs htail hsized
      (sibMB M c i j (negCount c) sg (if sg = 1 then REP else 2 ^ 256 - REP)) hjd hret rl w o i
      (sgw bs i) j sg (byteAt M (IDX + j)) hlast (by omega) hsg1 hsigns (i - 217) hcntB (by omega))

/-- Cost of the `FLAG = 1` squeeze (from copy 0's head at `o = 544` to copy 1's). -/
def extCost : Nat := 181 + Gas.kf4 + Gas.cext 17

/-- The regions the squeeze writes. -/
abbrev extRegions : List (Nat × Nat) := [(KS, KS + 800), (KB, KB + 800), (CB + 544, CB + 1088)]

/-- `sibext` with `FLAG = 0`. -/
theorem ext_flag0 (hs : Ctx s) (htail : tail.length ≤ 886) (hsized : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (hfl : word M FLAG = 0) (i sg : Nat) :
    Reach (headSt s ret tail 0 544 i sg M) (headSt s ret tail 1 544 i sg M) 46 :=
  b_ext0 hs htail hsized M i sg hfl

/-- `sibext` with `FLAG = 1`: squeeze c's second block into `CB[17, 34)`. -/
theorem ext_flag1 (hs : Ctx s) (hr : RetOK Stack.sib ret tail) (hsized : 2616 ≤ s.activeWords.toNat)
    (M : ByteArray) (hfl : word M FLAG = 1) (hrc : RC4Table M)
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hsc : St4At M SC S) (i sg : Nat) :
    ∃ M', FrameExcept M M' extRegions ∧
      (∀ x, x < 17 → word M' (CB + 32 * (17 + x)) =
        laneOf (EvmSemantics.Crypto.Keccak.permute (S 0)) x) ∧
      Reach (headSt s ret tail 0 544 i sg M) (headSt s ret tail 1 544 i sg M') extCost := by
  have htail : tail.length ≤ 886 := by
    have := hr.depth; simp only [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 2 ^ 64 := hs.small
  have h1 := b_ext1 (ret := ret) hs htail hsized M i sg hfl
  have h2 := Infra.reach_mcopy (pc := 8257) (d := 0) (src := 61504) (n := 800)
    (rest := wd 544 :: wd i :: wd sg :: wd ret :: tail) (m := M) hs ⟨3379, by decide⟩
    (by simp only [Infra.instrAt_lit]) (by simp only [Infra.pcAt_lit]) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by omega) (by simp; omega)
  set M2 := MachineState.writeBytes M (MachineState.readPadded M 61504 800) 0 with hM2
  have hks2 : KS4 M2 S := by
    intro x hx
    rw [hM2, show KS + 32 * x = 0 + 32 * x by rfl, word_mcopy _ (by omega) (by omega),
      show 61504 + (0 + 32 * x - 0) = SC + 32 * x by simp only [SC]; omega]
    exact hsc x hx
  have h3 := b_ext2 (ret := ret) hs htail hsized M2 i sg
  have hr4 : RetOK Stack.kf4 8265 ([wd 544, wd i, wd sg, wd ret] ++ tail) :=
    hr.callee (by simp [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf]) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
  obtain ⟨M3, hks3, hf3, hc3⟩ := kf4_call hs hr4 M2 trivial
  have hk3 := hks3 S hS hks2
  have h5 := b_ext3 (ret := ret) hs htail hsized M3 i sg
  have hr6 : RetOK Stack.cext 8279 ([wd 544, wd i, wd sg, wd ret] ++ tail) :=
    hr.callee (by simp [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf]) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
  obtain ⟨M4, hx4, hf4, hc4⟩ := cext_call (dst := 64032) (sh := 0) (n := 17) hs hr6 M3
    (by norm_num) (by norm_num) (by norm_num) (by simp only [KS]; omega) (by simp only [TOP]; omega)
  have h7 := b_ext4 (ret := ret) hs htail hsized M4 i sg
  refine ⟨M4, ?_, fun x hx => ?_, ?_⟩
  · intro a ha
    have r1 := ha (KS, KS + 800) (by simp)
    have r2 := ha (KB, KB + 800) (by simp)
    have r4 := ha (CB + 544, CB + 1088) (by simp)
    simp only [KS, KB, CB] at r1 r2 r4
    have c4 : ∀ r ∈ [(64032, 64032 + 32 * 17)], a < r.1 ∨ r.2 ≤ a := by simp; omega
    have c3 : ∀ r ∈ [(KS, KS + 800), (KB, KB + 800)], a < r.1 ∨ r.2 ≤ a := by simp [KS, KB]; omega
    have c2 : ∀ r ∈ [(0, 0 + 800)], a < r.1 ∨ r.2 ≤ a := by simp; omega
    rw [hf4 a c4, hf3 a c3, hM2, FrameExcept.mcopy M 61504 0 800 a c2]
  · rw [show CB + 32 * (17 + x) = 64032 + 32 * x by simp only [CB]; omega, hx4 x hx,
      cext_lane hk3 (sh := 0) (by norm_num) (by omega)]
  · have hc3' : Reach (callState s Entry.kf4 (wd 8265 :: wd 544 :: wd i :: wd sg :: wd ret :: tail) M2)
        (callState s 8265 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M3) Gas.kf4 := hc3
    have hc4' : Reach (callState s Entry.cext (wd 17 :: wd 0 :: wd 64032 :: wd 8279 :: wd 544 :: wd i ::
        wd sg :: wd ret :: tail) M3) (callState s 8279 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M4)
        (Gas.cext 17) := hc4
    have h2' : Reach (callState s 8257 (wd 0 :: wd 61504 :: wd 800 :: wd 544 :: wd i :: wd sg :: wd ret :: tail) M)
        (callState s 8258 (wd 544 :: wd i :: wd sg :: wd ret :: tail) M2) 78 := h2
    refine ((h1.trans (h2'.trans (h3.trans (hc3'.trans (h5.trans (hc4'.trans h7)))))).mono ?_)
    unfold extCost
    generalize Gas.kf4 = a
    generalize Gas.cext 17 = b
    omega

end

end Ball4

end MlDsaOptGlam44.Proofs
