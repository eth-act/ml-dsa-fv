theorem mu_pad {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) {len off : Nat} (hlen : len < 136) :
    ∃ M', (∀ x, x < 25 → word M' (KS + 32 * x) = word M (KS + 32 * x) ^^^ rep (padLane len x)) ∧
      FrameExcept M M' [(KS, KS + 800)] ∧
      Reach (callState s 5766 [wd len, wd off, flag b] M) (callState s 19576 [wd 5868, flag b] M') 100 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  have h7 : 7 &&& len ≤ 7 := Nat.and_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 3
  · opt44_reach [1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948] with [word_mstore_disjoint]
    rfl
  · intro x hx
    have hm8 : len % 8 < 8 := Nat.mod_lt _ (by omega)
    have hk : 7 &&& len = len % 8 := by
      rw [Nat.and_comm, show (7 : Nat) = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    have hA : 194590153796987103689458225493986751267109480675054880555039 * 2 ^ (len % 8 * 8) =
        rep (31 * 2 ^ (8 * (len % 8))) := by
      unfold rep REP pack4; rw [show 8 * (len % 8) = len % 8 * 8 by ring]; norm_num; ring
    have hB : (57896044618658097714924043372037294308723028227884584459520880401941320957952 : Nat) =
        rep (2 ^ 63) := by unfold rep REP pack4; norm_num
    have hAl : 31 * 2 ^ (8 * (len % 8)) < 2 ^ 64 := by interval_cases (len % 8) <;> norm_num
    have hBl : (2 : Nat) ^ 63 < 2 ^ 64 := by norm_num
    rw [hk, hA, hB]
    simp only [KS, Nat.zero_add]
    rw [xor_mod_lit (rep_lt_lit hAl) (word_lt_lit _ _)]
    have hAw : rep (31 * 2 ^ (8 * (len % 8))) ^^^ word M (len / 8 * 32) < 2 ^ 256 :=
      Nat.xor_lt_two_pow (rep_lt hAl) (word_lt _ _)
    rw [word_wrL _ (Nat.mod_lt _ (by norm_num)) (by omega), word_wr _ hAw (by omega), word_wr _ hAw (by omega)]
    unfold padLane
    split_ifs <;> simp (disch := first | omega | exact hAl | exact hBl | exact rep_lt_lit hAl | exact rep_lt_lit hBl | exact word_lt_lit _ _ | norm_num) only [← rep_xor, rep_zero, Nat.xor_zero, Nat.zero_xor, xor_mod_lit, rep_lt_lit, word_lt_lit]
    all_goals first
      | (exfalso; omega)
      | (rw [show len / 8 * 32 = 32 * x by omega]; try simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm])
      | simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm]
      | (rw [show 32 * x = 512 by omega]; try simp only [Nat.xor_assoc, Nat.xor_comm, nxor_left_comm])
  · simp only [KS]
    repeat (refine frame_wr (by omega) (by omega) ?_)
    exact FrameExcept.refl _ _
