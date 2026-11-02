import MlDsaOpt44.Fn.Ball.V4Run
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! # `sib` (v4, WP J): the scan over the stream and the contract body

`sib_loop` recurses over the stream positions `p = 8 … 272` with the
potential `pot p i` (rejected bytes still ahead, `353` per coefficient still
to place, the failure exit, and the second block's squeeze while `p ≤ 136`).
`sib_main` is the contract body under `hb0` (the `BASES` words start in range):
v4 does not initialise `BASES`, so on the failure path the unwritten slots keep
their old contents. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

namespace Ball4

open MlDsa44.Proofs.Sampling (ballFold ballStep ballSet ballSign ballFold_succ ballFold_zero
  ballFold_inv sampleInBallOf_eq)

/-- Cost potential at stream position `p` with index `i`. -/
def pot (p i : Nat) : Nat := rs p + 353 * (256 - i) + 72 + (if p ≤ 136 then extCost else 0)

/-- `LIM` before and after the second block's squeeze. -/
def LimOK (M : ByteArray) (p : Nat) : Prop := word M 3968 = if p ≤ 136 then 544 else 1088

/-- The stream lanes in `CB` (the second block once `p > 136`). -/
def CbOK (M bs : ByteArray) (p : Nat) : Prop :=
  ∀ x, x < 34 → (x < 17 ∨ 136 < p) → word M (CB + 32 * x) = le64 bs (8 * x)

/-- The regions the squeeze writes. -/
abbrev extRegions : List (Nat × Nat) :=
  [(KS, KS + 800), (KB, KB + 800), (LIM, LIM + 32), (CB + 544, CB + 1088)]

theorem sinv_ext {m M M' : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i) (hi : i ≤ 256)
    (hf : FrameExcept M M' extRegions) : SInv m M' c i := by
  obtain ⟨hfr, hcw, hnneg, hcnt, ⟨f, finj, fmem, fslot⟩, hidx0, hfree⟩ := h
  have hw : ∀ a, (a + 32 ≤ 3968 ∧ 1824 ≤ a) ∨ (4000 ≤ a ∧ a + 32 ≤ 64032) → word M' a = word M a :=
    fun a ha => FrameExcept.word hf (by simp [KS, KB, LIM, CB]; omega)
  have hb : ∀ a, 4000 ≤ a → a < 64032 → byteAt M' a = byteAt M a :=
    fun a h1 h2 => FrameExcept.byteAt hf (by simp [KS, KB, LIM, CB]; omega)
  refine ⟨fun a ha => ?_, fun t ht => ?_, ?_, ?_, ⟨f, finj, fmem, fun s hs => ?_⟩, fun t ht hz => ?_,
    fun s h1 h2 => ?_⟩
  · rw [hf a (fun r hr => ha r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)),
      hfr a ha]
  · rw [hw _ (by simp only [CW]; omega)]; exact hcw t ht
  · rw [hw _ (by simp only [NNEG]; omega)]; exact hnneg
  · rw [hw _ (by simp only [CNT]; omega)]; exact hcnt
  · have hf' := ((fmem (f s)).1 ⟨s, hs, rfl⟩).1
    rw [hw _ (by simp only [BASES]; omega), hb _ (by simp only [IDX]; omega) (by simp only [IDX]; omega)]
    exact fslot s hs
  · rw [hb _ (by simp only [IDX]; omega) (by simp only [IDX]; omega)]; exact hidx0 t ht hz
  · rw [hw _ (by simp only [BASES]; omega)]; exact hfree s h1 h2

theorem word_frame4 {m M : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i) {a : Nat}
    (ha : Avoids sibRegions4 a (a + 32)) : word M a = word m a := h.frame.word ha

theorem rlOf_jd (r : Nat) (hr : r < 8) :
    Decode.isValidJumpDest MlDsaOpt44.optBytecode (rlOf r) = true := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;> simp only [rlOf, Nat.reduceMul, Nat.reduceAdd, Infra.isValidJumpDest_lit]

theorem rs_ge (p : Nat) (hp : p < 272) : rc (p % 8) ≤ rs p := by
  rw [rs_succ hp]; omega

theorem rs_272 : rs 272 = 0 := rfl

theorem pot_bound {e0 e1 A R i : Nat} (h1 : e0 ≤ e1) (h2 : A ≤ 86) (h3 : 40 ≤ R) (h4 : i + 1 = 256) :
    e0 + (A + 350) ≤ R + 353 * (256 - i) + 72 + e1 := by omega

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem sib_loop (hs : Ctx s) (hr : RetOK Stack.sib ret tail) (hsized : 2616 ≤ s.activeWords.toNat)
    (m bs : ByteArray) (hrc : RC4Table m) (S : Nat → Fips202.SpongeState) (hS : Sized4 S)
    (hsc : St4At m SC S)
    (hc2 : ∀ x, x < 17 → le64 bs (136 + 8 * x) = laneOf (EvmSemantics.Crypto.Keccak.permute (S 0)) x) :
    ∀ n p z M, n = 272 - p → 8 ≤ p → p ≤ 272 → (ballFold bs (p - 8)).2 < 256 →
      SInv m M (ballFold bs (p - 8)).1 (ballFold bs (p - 8)).2 → LimOK M p → CbOK M bs p →
      ∃ M' k', k' ≤ 264 ∧ SInv m M' (ballFold bs k').1 (ballFold bs k').2 ∧
        ballFold bs 264 = ballFold bs k' ∧
        Reach (posSt s ret tail bs p (ballFold bs (p - 8)).2 z M)
          (callState s ret (wd (if (ballFold bs 264).2 < 256 then 0 else 1) :: tail) M')
          (pot p (ballFold bs (p - 8)).2)
  | 0, p, z, M, hn, hp8, hp, hlt, hinv, hlim, hcb => by
    have hp272 : p = 272 := by omega
    subst hp272
    have htail : tail.length ≤ 960 := by
      have := hr.depth; simp only [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf] at this; omega
    refine ⟨M, 264, le_rfl, hinv, rfl, ?_⟩
    rw [if_pos hlt]
    unfold posSt
    rw [if_pos (by norm_num)]
    exact (b_fail hs htail hsized M hr.jumpdest hr.small _ _ (by unfold LimOK at hlim; simpa using hlim)).mono
      (by unfold pot; omega)
  | n + 1, p, z, M, hn, hp8, hp, hlt, hinv, hlim, hcb => by
    have htail : tail.length ≤ 960 := by
      have := hr.depth; simp only [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf] at this; omega
    have hp272 : p < 272 := by omega
    obtain ⟨hsz, hi1, hi2, -⟩ := ballFold_inv bs (p - 8)
    have hhigh := ballFold_high bs (p - 8)
    have hsucc := ballFold_succ bs (p - 8)
    rw [show 8 + (p - 8) = p by omega, show p - 8 + 1 = p + 1 - 8 by omega] at hsucc
    rcases hF : ballFold bs (p - 8) with ⟨c, i⟩
    rw [hF] at hsz hi1 hi2 hhigh hsucc hlt hinv
    simp only at hsz hi1 hi2 hhigh hlt hinv ⊢
    -- the squeeze at `p = 136`
    have hstep0 : ∃ M0, SInv m M0 c i ∧ FrameExcept M M0 extRegions ∧
        word M0 3968 = (if p < 136 then 544 else 1088) ∧
        (∀ x, x < 34 → (x < 17 ∨ 136 ≤ p) → word M0 (CB + 32 * x) = le64 bs (8 * x)) ∧
        Reach (posSt s ret tail bs p i z M) (posSt s ret tail bs p i z M0)
          (if p = 136 then extCost else 0) := by
      by_cases h136 : p = 136
      · subst h136
        have hrcM : RC4Table M := fun k hk => by
          rw [word_frame4 hinv (by simp [RC4, KS, KB, LIM, CW, BASES, IDX, NNEG, CB]; omega)]
          exact hrc k hk
        have hscM : St4At M SC S := fun x hx => by
          rw [word_frame4 hinv (by simp [SC, KS, KB, LIM, CW, BASES, IDX, NNEG, CB]; omega)]
          exact hsc x hx
        obtain ⟨M0, hf0, hl0, hx0, hr0⟩ := ext_step hs hr hsized M (by unfold LimOK at hlim; simpa using hlim)
          hrcM S hS hscM i (sgw bs i)
        refine ⟨M0, sinv_ext hinv hi2 hf0, hf0, by simpa using hl0, fun x hx _ => ?_, ?_⟩
        · by_cases hx17 : x < 17
          · rw [FrameExcept.word hf0 (by simp [KS, KB, LIM, CB]; omega)]
            exact hcb x hx (Or.inl hx17)
          · have := hx0 (x - 17) (by omega)
            rw [show 17 + (x - 17) = x by omega] at this
            rw [this, ← hc2 (x - 17) (by omega), show 136 + 8 * (x - 17) = 8 * x by omega]
        · unfold posSt
          rw [if_pos (by norm_num), if_pos rfl]
          exact hr0
      · refine ⟨M, hinv, FrameExcept.refl _ _, ?_, fun x hx h => hcb x hx (by omega), ?_⟩
        · unfold LimOK at hlim; rw [hlim]; split <;> split <;> omega
        · rw [if_neg h136]; exact Reach.refl _
    obtain ⟨M0, hinv0, hf0, hl0, hc0, hr0⟩ := hstep0
    have hlimP : LimOK M0 (p + 1) := by
      unfold LimOK; rw [hl0]; split <;> split <;> omega
    have hcbP : CbOK M0 bs (p + 1) := fun x hx h => hc0 x hx (by omega)
    have hlim2 : word M0 3968 ≤ 1088 := by rw [hl0]; split <;> omega
    have hne : p % 8 = 0 → 4 * p ≠ word M0 3968 := fun _ => by rw [hl0]; split <;> omega
    have hw : p % 8 = 0 → word M0 (63488 + 4 * p) = le64 bs p := fun h8 => by
      have := hc0 (p / 8) (by omega) (by omega)
      rw [show CB + 32 * (p / 8) = 63488 + 4 * p by simp only [CB]; omega,
        show 8 * (p / 8) = p by omega] at this
      exact this
    have hpot : (if p = 136 then extCost else 0) + (if p + 1 ≤ 136 then extCost else 0) ≤
        (if p ≤ 136 then extCost else 0) := by
      split_ifs <;> omega
    have hrs := rs_succ hp272
    by_cases hacc : bs[p]!.toNat ≤ i
    · -- accept
      have hst : ballFold bs (p + 1 - 8) = (ballSet bs c i bs[p]!.toNat, i + 1) := by
        rw [hsucc]; unfold ballStep; rw [if_pos ⟨hlt, hacc⟩]
      have hA := byte_acc (ret := ret) (z := z) hs htail hsized bs M0 hp272 rfl hlim2 hne hw hacc hlt
      obtain ⟨M', hfr', hinv', hmid, hend⟩ := acc_chain (ret := ret) (rl := rlOf (p % 8))
        (w := le64 bs (p - p % 8)) (o := 4 * (p - p % 8)) hs htail hsized hr.jumpdest hr.small bs hinv0
        hsz hi1 hlt hacc hhigh (rlOf_jd _ (Nat.mod_lt _ (by norm_num))) (by simp only [rlOf]; omega)
      have hinv'' : SInv m M' (ballFold bs (p + 1 - 8)).1 (ballFold bs (p + 1 - 8)).2 := by
        rw [hst]; exact hinv'
      have hl' : LimOK M' (p + 1) := by
        unfold LimOK; rw [FrameExcept.word hfr' (by simp [CW, BASES, IDX, NNEG])]; exact hlimP
      have hc' : CbOK M' bs (p + 1) := fun x hx h => by
        rw [FrameExcept.word hfr' (by simp [CW, BASES, IDX, NNEG, CB]; omega)]; exact hcbP x hx h
      have hcost : acost (p % 8) + 336 + (if p % 8 = 7 then 22 else 0) = rc (p % 8) + 353 := by
        unfold acost rc; split_ifs <;> omega
      by_cases hlast : i + 1 < 256
      · obtain ⟨M'', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr hsized m bs hrc S hS hsc hc2 n
          (p + 1) (rlOf (p % 8)) M' (by omega) (by omega) (by omega) (by rw [hst]; exact hlast) hinv'' hl' hc'
        rw [hst] at hreach
        refine ⟨M'', k', hk', hinvF, hfold, ?_⟩
        have hB := acc_back (ret := ret) (i := i) hs htail hsized bs M' hp272
        exact ((hr0.trans (hA.trans ((hmid hlast).trans (hB.trans hreach))))).mono
          (by unfold pot; omega)
      · have hfold : ballFold bs 264 = ballFold bs (p + 1 - 8) := by
          have := ballFold_stop bs (p + 1 - 8) (by rw [hst]; simp only; omega) (264 - (p + 1 - 8))
          rwa [show p + 1 - 8 + (264 - (p + 1 - 8)) = 264 by omega] at this
        refine ⟨M', p + 1 - 8, by omega, hinv'', hfold, ?_⟩
        rw [hfold, hst, if_neg (by simp only; omega)]
        have hle : acost (p % 8) ≤ 86 := by unfold acost; split <;> omega
        have hge := rs_ge p hp272
        have hi255 : i + 1 = 256 := by omega
        have hfin := hr0.trans (hA.trans (hend hi255))
        refine hfin.mono ?_
        have hcmp : (if p = 136 then extCost else 0) ≤ (if p ≤ 136 then extCost else 0) := by
          split_ifs <;> omega
        have h40 : 40 ≤ rs p := le_trans (by unfold rc; split_ifs <;> omega) hge
        unfold pot
        exact pot_bound hcmp hle h40 hi255
    · -- reject
      have hst : ballFold bs (p + 1 - 8) = (c, i) := by
        rw [hsucc]; unfold ballStep; rw [if_neg (fun h => hacc h.2)]
      have hR := byte_rej (ret := ret) (z := z) hs htail hsized bs M0 hp272 rfl hlim2 hne hw
        (by omega) hlt
      obtain ⟨M', k', hk', hinvF, hfold, hreach⟩ := sib_loop hs hr hsized m bs hrc S hS hsc hc2 n
        (p + 1) bs[p]!.toNat M0 (by omega) (by omega) (by omega) (by rw [hst]; exact hlt)
        (by rw [hst]; exact hinv0) hlimP hcbP
      rw [hst] at hreach
      refine ⟨M', k', hk', hinvF, hfold, ?_⟩
      exact (hr0.trans (hR.trans hreach)).mono (by unfold pot; omega)

end

/-- The final invariant is `CRep`. -/
theorem crep_of_sinv {m M : ByteArray} {c : Fips204.Poly} (h : SInv m M c 256) : CRep M c := by
  obtain ⟨-, hcw, hnneg, -, ⟨f, finj, fmem, fslot⟩, -, -⟩ := h
  have hget : ∀ s, s < 39 → ((List.range 39).map f)[s]! = f s := fun s hs => by
    rw [getElem!_pos ((List.range 39).map f) s (by simp; omega)]
    simp
  refine ⟨hcw, hnneg, (List.range 39).map f, by simp [Fips204.tau], ?_, fun p => ?_, fun s hs => ?_⟩
  · exact List.Nodup.map_on (fun x hx y hy e => finj x y (by simpa using hx) (by simpa using hy) e)
      List.nodup_range
  · rw [← fmem p]; simp [List.mem_map, List.mem_range]
  · simp only [Fips204.tau] at hs
    rw [hget s hs]; exact (fslot s hs).1

theorem bases_le {m M : ByteArray} {c : Fips204.Poly} {i : Nat} (h : SInv m M c i) (s : Nat)
    (hs : s < 39) : word M (BASES + 32 * s) ≤ 6112 := by
  obtain ⟨-, -, -, -, ⟨f, -, fmem, fslot⟩, -, hfree⟩ := h
  by_cases hsn : s < i - 217
  · rw [(fslot s hsn).1]
    have := baseOf_le c (f s) ((fmem (f s)).1 ⟨s, hsn, rfl⟩).1
    omega
  · exact hfree s (by omega) hs

end Ball4

open Ball4 in
/-- The `sib` contract body, assuming the `BASES` words start in range (`hb0`;
see the module docstring). -/
theorem sib_main {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.sib ret tail) (m : ByteArray) (hrc : RC4Table m)
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hsc : St4At m SC S)
    (bs : ByteArray) (hbs : bs.size = 272)
    (hcb : ∀ x, x < 17 → word m (CB + 32 * x) = le64 bs (8 * x))
    (hc2 : ∀ x, x < 17 → le64 bs (136 + 8 * x) = laneOf (EvmSemantics.Crypto.Keccak.permute (S 0)) x)
    (hz : SibFresh m) (hb0 : ∀ i, i < Fips204.tau → word m (BASES + 32 * i) ≤ 6112) :
    ∃ m', (∀ c, Fips204.sampleInBallOf bs = some c → CRep m' c) ∧
      (∀ i, i < Fips204.tau → word m' (BASES + 32 * i) ≤ 6112) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (LIM, LIM + 32), (CW, CW + 8192),
        (BASES, BASES + 2048), (IDX, IDX + 256), (NNEG, NNEG + 64), (CB + 544, CB + 1088)] ∧
      Call s Entry.sib [] ret tail m [flag (Fips204.sampleInBallOf bs).isSome] m' Gas.sib := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.sib, Stack.kf4, Stack.cext, Stack.leaf] at this; omega
  have hsized : 2616 ≤ s.activeWords.toNat := hs.sized
  have hentry := b_entry (ret := ret) hs htail hsized m
  set M1 := MachineState.writeBytes m (Data.Bytes.natToBytesPadded 544 32) 3968 with hM1
  have hf1 : FrameExcept m M1 extRegions := fun a ha => by
    rw [hM1]; exact FrameExcept.mstore m 3968 544 a (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ha (LIM, LIM + 32) (by simp))
  have h0 : SInv m M1 (MlDsa44.Proofs.Sampling.ballFold bs (8 - 8)).1
      (MlDsa44.Proofs.Sampling.ballFold bs (8 - 8)).2 := by
    rw [show 8 - 8 = 0 from rfl, MlDsa44.Proofs.Sampling.ballFold_zero]
    have := sinv_ext (sinv_init m hz (fun i hi => hb0 i (by simpa [Fips204.tau] using hi))) (by norm_num) hf1
    -- `sinv_init` uses `m` as the reference memory
    exact this
  have hl1 : LimOK M1 8 := by
    unfold LimOK; rw [hM1, word_mstore _ _ _ (by norm_num)]; rfl
  have hc1 : CbOK M1 bs 8 := fun x hx h => by
    rw [hM1, word_mstore_disjoint _ _ (by simp only [CB]; omega)]
    exact hcb x (by omega)
  obtain ⟨M', k', hk', hinv, hfold, hreach⟩ := sib_loop (ret := ret) hs hr hsized m bs hrc S hS hsc
    hc2 264 8 0 M1 rfl (by omega) (by omega)
    (by rw [show 8 - 8 = 0 from rfl, MlDsa44.Proofs.Sampling.ballFold_zero]; decide) h0 hl1 hc1
  rw [show 8 - 8 = 0 from rfl, MlDsa44.Proofs.Sampling.ballFold_zero] at hreach
  refine ⟨M', fun c hc => ?_, fun i hi => bases_le hinv i (by simpa [Fips204.tau] using hi),
    hinv.frame, ?_⟩
  · rw [MlDsa44.Proofs.Sampling.sampleInBallOf_eq] at hc
    split at hc
    · exact absurd hc (by simp)
    · rename_i hge
      simp only [Option.some.injEq] at hc
      subst hc
      rw [hfold] at hge ⊢
      have hi2 := (MlDsa44.Proofs.Sampling.ballFold_inv bs k').2.2.1
      have h256 : (MlDsa44.Proofs.Sampling.ballFold bs k').2 = 256 := by omega
      rw [h256] at hinv
      exact crep_of_sinv hinv
  · rw [call_iff, Entry.sib]
    have hflag : flag (Fips204.sampleInBallOf bs).isSome =
        wd (if (MlDsa44.Proofs.Sampling.ballFold bs 264).2 < 256 then 0 else 1) := by
      rw [MlDsa44.Proofs.Sampling.sampleInBallOf_eq]
      by_cases h : (MlDsa44.Proofs.Sampling.ballFold bs 264).2 < 256 <;> simp [h, flag]
    rw [hflag]
    have hst : posSt s ret tail bs 8 217 0 M1 = headSt s ret tail 32 217 (word m 63488) M1 := by
      unfold posSt sgw
      rw [if_pos (by norm_num), show word m 63488 = le64 bs 0 by
        have := hcb 0 (by omega); simpa [CB] using this]
      norm_num
    rw [hst] at hreach
    refine ((hentry.trans hreach).mono ?_).of_eq rfl rfl
    unfold pot Gas.sib extCost
    rw [rs_8]
    simp only [show (8 : Nat) ≤ 136 from by norm_num, if_true]
    generalize Gas.kf4 = a
    generalize Gas.cext 17 = b
    omega

end MlDsaOpt44.Proofs
