
theorem padLane_hi {r x : Nat} (hr : r < 136) (hx : 17 ≤ x) : padLane r x = 0 := by
  unfold padLane; rw [if_neg (by omega), if_neg (by omega), Nat.xor_zero]

/-- Exit: padding, the final permutation and the copy of μ's lanes to `FIN`. -/
theorem mu_finish {s : State} (hs : Ctx s) (b : Bool)
    {m M : ByteArray}
    (hI : MuInv s.executionEnv.calldata m M ((muMsgW s.executionEnv.calldata).size / 136)) :
    ∃ M', FinMu M' s.executionEnv.calldata ∧ RC1Table M' ∧
      FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] ∧
      Reach (callState s 5727 [wd ((muMsgW s.executionEnv.calldata).size -
          136 * ((muMsgW s.executionEnv.calldata).size / 136)),
          wd (3802 + 136 * ((muMsgW s.executionEnv.calldata).size / 136)), flag b] M)
        (callState s 5926 [flag b] M') (23 + 100 + Gas.kf1 + 102) := by
  set cd := s.executionEnv.calldata with hcdef
  set L := (muMsgW cd).size
  set n := L / 136
  have hr : L - 136 * n = L % 136 := by omega
  have hr' : L % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have h1 := mu_exit hs b M (len := L - 136 * n) (off := 3802 + 136 * n) (by omega)
  obtain ⟨M5, f5, fr5, r5⟩ := mu_pad hs b M (len := L - 136 * n) (off := 3802 + 136 * n) (by omega)
  set S'' := Fips202.xorBlock 136 (muPad cd) (L / 136 * 136) (absorbPre 136 (muPad cd) n)
  have hS'' : S''.size = 25 := by rw [xorBlock_size, absorbPre_size]
  have hK : KS1 M5 S'' := fun x hx => by
    rw [f5 x hx, hI.ks x hx, hr, rep_cpl_xor _ (muLanes_lt _ _ _) (padLane_lt _ _),
      laneOf_xorBlock _ _ (absorbPre_size _ _ n) (by norm_num) x]
    unfold muLanes
    by_cases h : x < 17
    · rw [if_pos (by omega), if_pos h, show muPad cd =
        Fips202.pad 136 0x1F (muMsgW cd) from rfl, le64_pad_last _ h, Nat.xor_assoc,
        show 136 * n = L / 136 * 136 by ring]
    · rw [if_neg (by omega), if_neg h, Nat.xor_zero, padLane_hi hr' (by omega), Nat.xor_zero]
  obtain ⟨M6, hk6, hf6, hc6⟩ := kf1_call hs (ret := 5868) (tail := [flag b])
    (retOK_mu (by decide) (by simp) (by simp only [isValidJumpDest_lit]) (by norm_num)) M5
    ((hI.rc1).frame fr5 (by avoids_tac))
  have hP : (muPad cd).size = (n + 1) * 136 := by
    rw [show muPad cd = Fips202.pad 136 0x1F (muMsgW cd) from rfl, pad_size _ _ (by norm_num)]
  have hK6 : KS1 M6 (Fips202.absorb 136 (muPad cd)) := by
    rw [absorb_eq _ _ (n + 1) (by norm_num) hP, absorbPre_succ,
      show n * 136 = L / 136 * 136 from rfl]
    exact hk6 S'' hS'' hK
  obtain ⟨M7, f7, fr7, r7⟩ := mu_copy hs b M6
  rw [call_iff] at hc6
  have hfr : FrameExcept m M7 [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] := by
    refine (((hI.fr.trans fr5).trans hf6).trans fr7).mono ?_
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KS, KB, FIN]
  refine ⟨M7, fun x hx => ?_, ((hI.rc1.frame fr5 (by avoids_tac)).frame hf6 (by avoids_tac)).frame fr7
    (by avoids_tac), hfr, (((h1.trans r5).trans hc6).trans r7).mono (by omega)⟩
  rw [f7 x hx, hK6 x (by omega), le64_muOf_absorb cd hx]
  have hl := laneOf_lt (Fips202.absorb 136 (muPad cd)) x
  split
  · rename_i h
    exact not_rep_cpl (by rcases h with rfl | rfl <;> decide) hl
  · rename_i h
    unfold cpl
    rw [if_neg (by interval_cases x <;> simp_all [complemented])]

theorem seg_mu_proof {s : State} (hs : Ctx s) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m : ByteArray} (hI : Inv5 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv6 s.executionEnv.calldata m' ∧
      Reach (callState s 4648 [flag b] m) (callState s 5926 [flag b] m')
        (Gas.pMu (mlenOf s.executionEnv.calldata)) := by
  have hfit : s.executionEnv.calldata.size < 18446744073709551616 := hs.calldataFits
  have hl : 3732 ≤ s.executionEnv.calldata.size := hcd
  -- the invariant from any frame avoiding the Keccak state and `FIN`
  have inv6 : ∀ M', FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] →
      FinMu M' s.executionEnv.calldata → RC1Table M' → Inv6 s.executionEnv.calldata M' :=
    fun M' hfr hmu hrc =>
      { rc1 := hrc
        tbl := hI.tbl.frame hfr (by avoids_tac)
        hp := hI.hp.frame hfr (by avoids_tac)
        acc := hI.acc.frame hfr (by avoids_tac)
        cb := fun x hx => by
          rw [word_frame hfr (lo := CB) (hi := CB + 1088) (by avoids_tac) (by omega) (by omega)]
          exact hI.cb x hx
        fresh := hI.fresh.frame hfr (by avoids_tac) (by avoids_tac) (by avoids_tac)
        fmu := hmu }
  by_cases hsh : mlenOf s.executionEnv.calldata ≤ 69
  · have hlt : s.executionEnv.calldata.size < 3802 := by unfold mlenOf at hsh; omega
    obtain ⟨M', f, fr, r⟩ := mu_short hs b m hfit hlt (fun x hx => by
      rw [hI.mu hsh x hx]; exact le64_lt _ _)
    have hfr : FrameExcept m M' [(KS, KS + 800), (KB, KB + 800), (FIN, FIN + 256)] := by
      refine fr.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp [KS, KB, FIN]
    refine ⟨M', inv6 M' hfr (fun x hx => by rw [f x hx, hI.mu hsh x hx])
      (hI.rc1.frame fr (by avoids_tac)), ?_⟩
    unfold Gas.pMu; rw [if_pos hsh]; exact r
  · have hlong : 3802 ≤ s.executionEnv.calldata.size := by unfold mlenOf at hsh; omega
    have r0 := mu_chk_long hs b m hfit hlong
    obtain ⟨M0, hI0, r1⟩ := mu_setup hs hcd b hI.trl hI.rc1
    have hL := muMsgW_size s.executionEnv.calldata hcd
    rw [← hL] at r1
    obtain ⟨M, hIn, r2⟩ := mu_loop hs hcd b hI0 ((muMsgW s.executionEnv.calldata).size / 136)
      (Nat.mul_div_le _ _)
    obtain ⟨M', hmu, hrc, hfr, r3⟩ := mu_finish hs b hIn
    refine ⟨M', inv6 M' hfr hmu hrc, (((r0.trans r1).trans r2).trans r3).mono ?_⟩
    unfold Gas.pMu
    rw [if_neg hsh, hL]
    unfold mlenOf
    rw [Nat.add_mul, Nat.one_mul]
    omega

end MlDsaOpt44.Proofs
