
theorem lane0_eq (Y : Nat) : M64 &&& Y = lane Y 0 := by
  have := laneK_eq Y 0; simpa using this

theorem rhoW_lo (cd : ByteArray) {k : Nat} (hk : k < 4) : rhoW cd k = spread (le64 cd (8 * k)) := by
  unfold rhoW; rw [if_pos hk]

theorem rhoW_hi (cd : ByteArray) {k : Nat} (hk : k < 4) :
    rhoW cd (4 + k) = spread (le64 cd (CTOFF + 8 * k)) := by
  unfold rhoW; rw [if_neg (by omega), show 4 + k - 4 = k by omega]

theorem seg_rho_proof {s : State} (hs : Ctx s) {m : ByteArray}
    (hI : Inv3 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv4 s.executionEnv.calldata m' ∧
      Reach (callState s 3078 [flag b] m) (callState s 3439 [flag b] m') Gas.pRho := by
  generalize hcd : s.executionEnv.calldata = cd at hI
  have hY0 := bswapNet_lt (word cd 0)
  have hY1 := bswapNet_lt (word cd 1312)
  have hW : ∀ k, rhoW cd k < 2 ^ 256 := rhoW_lt cd
  have hr : ∀ (r : Nat) (Y : Nat), Decode.isValidJumpDest MlDsaOpt44.optBytecode r = true →
      r < 2 ^ 16 → RetOK Stack.spr r (wd Y :: rhoK b) := fun r Y hj hl =>
    retOK_main (by decide) (by simp [rhoK]) hj hl
  -- lanes of the two byte-swapped words
  have l0 : ∀ k, k < 4 → lane (bswapNet (word cd 0)) (3 - k) = le64 cd (8 * k) := fun k hk => by
    rw [lane_bswapNet cd 0 (by omega)]; congr 1; omega
  have l1 : ∀ k, k < 4 → lane (bswapNet (word cd 1312)) (3 - k) = le64 cd (CTOFF + 8 * k) :=
    fun k hk => by rw [lane_bswapNet cd 1312 (by omega)]; unfold CTOFF; congr 1; omega
  have e0 : spread (bswapNet (word cd 0) / 2 ^ 192) = rhoW cd 0 := by
    rw [lane3_eq hY0, rhoW_lo cd (by omega), ← l0 0 (by omega)]
  have e1 : spread (M64 &&& bswapNet (word cd 0) / 2 ^ (64 * 2)) = rhoW cd 1 := by
    rw [laneK_eq, rhoW_lo cd (by omega), ← l0 1 (by omega)]
  have e2 : spread (M64 &&& bswapNet (word cd 0) / 2 ^ (64 * 1)) = rhoW cd 2 := by
    rw [laneK_eq, rhoW_lo cd (by omega), ← l0 2 (by omega)]
  have e3 : spread (M64 &&& bswapNet (word cd 0)) = rhoW cd 3 := by
    rw [lane0_eq, rhoW_lo cd (by omega), ← l0 3 (by omega)]
  have e4 : spread (bswapNet (word cd 1312) / 2 ^ 192) = rhoW cd 4 := by
    rw [lane3_eq hY1, rhoW_hi cd (k := 0) (by omega), ← l1 0 (by omega)]
  have e5 : spread (M64 &&& bswapNet (word cd 1312) / 2 ^ (64 * 2)) = rhoW cd 5 := by
    rw [laneK_eq, rhoW_hi cd (k := 1) (by omega), ← l1 1 (by omega)]
  have e6 : spread (M64 &&& bswapNet (word cd 1312) / 2 ^ (64 * 1)) = rhoW cd 6 := by
    rw [laneK_eq, rhoW_hi cd (k := 2) (by omega), ← l1 2 (by omega)]
  have e7 : spread (M64 &&& bswapNet (word cd 1312)) = rhoW cd 7 := by
    rw [lane0_eq, rhoW_hi cd (k := 3) (by omega), ← l1 3 (by omega)]
  subst hcd
  let Y0 := bswapNet (word s.executionEnv.calldata 0)
  let Y1 := bswapNet (word s.executionEnv.calldata 1312)
  let W := rhoW s.executionEnv.calldata
  have c0 := spr_call hs (hr 3259 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 0) (v := Y0 / 2 ^ 192) (by omega)
  have c1 := spr_call hs (hr 3278 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 1) (v := M64 &&& Y0 / 2 ^ (64 * 2)) (by rw [laneK_eq]; unfold lane; omega)
  have c2 := spr_call hs (hr 3297 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 2) (v := M64 &&& Y0 / 2 ^ (64 * 1)) (by rw [laneK_eq]; unfold lane; omega)
  have c3 := spr_call hs (hr 3313 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 3) (v := M64 &&& Y0) (by rw [lane0_eq]; unfold lane; omega)
  have c4 := spr_call hs (hr 3374 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 4) (v := Y1 / 2 ^ 192) (by omega)
  have c5 := spr_call hs (hr 3393 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 5) (v := M64 &&& Y1 / 2 ^ (64 * 2)) (by rw [laneK_eq]; unfold lane; omega)
  have c6 := spr_call hs (hr 3412 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 6) (v := M64 &&& Y1 / 2 ^ (64 * 1)) (by rw [laneK_eq]; unfold lane; omega)
  have c7 := spr_call hs (hr 3428 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 7) (v := M64 &&& Y1) (by rw [lane0_eq]; unfold lane; omega)
  rw [call_iff, e0] at c0
  rw [call_iff, e1] at c1
  rw [call_iff, e2] at c2
  rw [call_iff, e3] at c3
  rw [call_iff, e4] at c4
  rw [call_iff, e5] at c5
  rw [call_iff, e6] at c6
  rw [call_iff, e7] at c7
  have h := (rho_b0 hs b m).trans ((rho_b1 hs b Y0 hY0 _).trans (c0.trans
    ((rho_b2 hs b Y0 hY0 m W (hW 0)).trans (c1.trans
    ((rho_b3 hs b Y0 hY0 m W (hW 1)).trans (c2.trans
    ((rho_b4 hs b Y0 hY0 m W (hW 2)).trans (c3.trans
    ((rho_b5 hs b Y0 m W (hW 3)).trans ((rho_b6 hs b Y1 hY1 _).trans (c4.trans
    ((rho_b7 hs b Y1 hY1 m W (hW 4)).trans (c5.trans
    ((rho_b8 hs b Y1 hY1 m W (hW 5)).trans (c6.trans
    ((rho_b9 hs b Y1 hY1 m W (hW 6)).trans (c7.trans
    (rho_b10 hs b Y1 m W (hW 7)))))))))))))))))))
  have hfr : FrameExcept m (storeWords m RHO1 W 8) [(RHO1, RHO1 + 256)] :=
    FrameExcept.storeWords m RHO1 W 8
  refine ⟨storeWords m RHO1 W 8,
    ⟨⟨hI.rc4.frame hfr (by avoids_tac), hI.rc1.frame hfr (by avoids_tac),
      hI.tbl.frame hfr (by avoids_tac), hI.zhat.frame hfr (by avoids_tac),
      hI.hp.frame hfr (by avoids_tac), hI.zMisc.frame hfr (by avoids_tac),
      hI.zCw.frame hfr (by avoids_tac), hI.zHigh.frame hfr (by avoids_tac)⟩,
      fun x hx => ⟨?_, ?_⟩⟩, h.mono (by unfold Gas.pRho; omega)⟩
  · rw [word_storeWords (hW x) 8 (by omega), rhoW_lo _ hx]
  · rw [word_storeWords (hW (4 + x)) 8 (by omega), rhoW_hi _ hx]

end MlDsaOpt44.Proofs
