import MlDsaOpt44.Fn.Kf4.Blocks1
import MlDsaOpt44.Fn.Kf4.Blocks2
import MlDsaOpt44.Fn.Kf4.Hom
import MlDsaOpt44.Fn.Kf4.Slot
import MlDsaOpt44.Fn.Kf4.RoundMem
import MlDsaOpt44.Budget
/-!
# `kf4`: composition

* `round_spec`: one round of the model (`roundM`) applies `Keccak.round` to each
  slot of the interleaved, lane-complemented state (`KSW`);
* `iter_reach`: one loop iteration is the fourteen blocks of `Blocks1`/`Blocks2`
  (3324 gas) and computes `iterM`;
* `kf4_spec`: entry, eleven iterations jumping back, the last one exiting:
  `4 + 11 · 3352 + 3324 + 38 = 40238 = Gas.kf4`.
-/

namespace MlDsaOpt44.Proofs.Kf4

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto.Keccak
open MlDsaOptCommon

/-- The 25 words at `base` hold the four states `S`, interleaved and complemented. -/
def KSW (M : ByteArray) (base : Nat) (S : Nat → Array UInt64) : Prop :=
  ∀ x, x < 25 → ldY M (base + 32 * x) = W fun k => cplU x (S k)[x]!

theorem round_spec (M : ByteArray) (src dst rca : Nat) (hsd : src + 800 ≤ dst ∨ dst + 800 ≤ src)
    (S : Nat → Array UInt64) (hS : ∀ k, k < 4 → (S k).size = 25) (rc : UInt64)
    (hA : KSW M src S) (hrc : ldY M rca = W fun _ => rc) :
    KSW (roundM M src dst rca) dst (fun k => round (S k) rc) := by
  intro x hx
  have hc : (fun i : Fin 25 => ldY M (src + 32 * i.val)) =
      fun i => W (fun k => cplU i.val (S k)[i.val]!) := funext fun i => hA i.val i.isLt
  interval_cases x
  · simp only [Nat.reduceMul]
    rw [roundM_0 _ _ _ _ hsd, hc, hrc, out00_W]
    exact W_congr fun k hk => slot00 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_1 _ _ _ _ hsd, hc, hrc, out01_W]
    exact W_congr fun k hk => slot01 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_2 _ _ _ _ hsd, hc, hrc, out02_W]
    exact W_congr fun k hk => slot02 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_3 _ _ _ _ hsd, hc, hrc, out03_W]
    exact W_congr fun k hk => slot03 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_4 _ _ _ _ hsd, hc, hrc, out04_W]
    exact W_congr fun k hk => slot04 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_5 _ _ _ _ hsd, hc, hrc, out10_W]
    exact W_congr fun k hk => slot10 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_6 _ _ _ _ hsd, hc, hrc, out11_W]
    exact W_congr fun k hk => slot11 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_7 _ _ _ _ hsd, hc, hrc, out12_W]
    exact W_congr fun k hk => slot12 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_8 _ _ _ _ hsd, hc, hrc, out13_W]
    exact W_congr fun k hk => slot13 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_9 _ _ _ _ hsd, hc, hrc, out14_W]
    exact W_congr fun k hk => slot14 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_10 _ _ _ _ hsd, hc, hrc, out20_W]
    exact W_congr fun k hk => slot20 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_11 _ _ _ _ hsd, hc, hrc, out21_W]
    exact W_congr fun k hk => slot21 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_12 _ _ _ _ hsd, hc, hrc, out22_W]
    exact W_congr fun k hk => slot22 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_13 _ _ _ _ hsd, hc, hrc, out23_W]
    exact W_congr fun k hk => slot23 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_14 _ _ _ _ hsd, hc, hrc, out24_W]
    exact W_congr fun k hk => slot24 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_15 _ _ _ _ hsd, hc, hrc, out30_W]
    exact W_congr fun k hk => slot30 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_16 _ _ _ _ hsd, hc, hrc, out31_W]
    exact W_congr fun k hk => slot31 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_17 _ _ _ _ hsd, hc, hrc, out32_W]
    exact W_congr fun k hk => slot32 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_18 _ _ _ _ hsd, hc, hrc, out33_W]
    exact W_congr fun k hk => slot33 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_19 _ _ _ _ hsd, hc, hrc, out34_W]
    exact W_congr fun k hk => slot34 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_20 _ _ _ _ hsd, hc, hrc, out40_W]
    exact W_congr fun k hk => slot40 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_21 _ _ _ _ hsd, hc, hrc, out41_W]
    exact W_congr fun k hk => slot41 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_22 _ _ _ _ hsd, hc, hrc, out42_W]
    exact W_congr fun k hk => slot42 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_23 _ _ _ _ hsd, hc, hrc, out43_W]
    exact W_congr fun k hk => slot43 (S k) (hS k hk) rc
  · simp only [Nat.reduceMul]
    rw [roundM_24 _ _ _ _ hsd, hc, hrc, out44_W]
    exact W_congr fun k hk => slot44 (S k) (hS k hk) rc

theorem ldY_frame {M M' : ByteArray} {rs : List (Nat × Nat)} (h : FrameExcept M M' rs) {a : Nat}
    (ha : Avoids rs a (a + 32)) : ldY M' a = ldY M a := by
  rw [ldY_eq, ldY_eq, FrameExcept.word h ha]

/-- The two rounds of one iteration. -/
theorem iter_spec (M : ByteArray) (rp : Nat) (hrp : 2048 ≤ rp) (S : Nat → Array UInt64)
    (hS : ∀ k, k < 4 → (S k).size = 25) (rc0 rc1 : UInt64) (hA : KSW M 0 S)
    (hrc0 : ldY M rp = W fun _ => rc0) (hrc1 : ldY M (32 + rp) = W fun _ => rc1) :
    KSW (iterM M rp) 0 (fun k => round (round (S k) rc0) rc1) ∧
      FrameExcept M (iterM M rp) [(0, 800), (1024, 1824)] := by
  have h1 := round_spec M 0 1024 rp (by omega) S hS rc0 hA hrc0
  have hf1 := roundM_frame M 0 1024 rp
  have hrc1' : ldY (roundM M 0 1024 rp) (32 + rp) = W fun _ => rc1 := by
    rw [ldY_frame hf1 (by simp only [avoids_cons, avoids_nil, and_true]; omega)]; exact hrc1
  have h2 := round_spec (roundM M 0 1024 rp) 1024 0 (32 + rp) (by omega) _
    (fun k _ => round_size (S k) rc0) rc1 h1 hrc1'
  refine ⟨h2, ?_⟩
  have hf2 := roundM_frame (roundM M 0 1024 rp) 1024 0 (32 + rp)
  refine FrameExcept.mono (FrameExcept.trans hf1 hf2) ?_
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨(1024, 1824), by simp, le_rfl, le_rfl⟩
  · exact ⟨(0, 800), by simp, le_rfl, by simp⟩

/-! ## The loop -/

/-- The first `n` Keccak rounds. -/
def rounds (A : Array UInt64) (n : Nat) : Array UInt64 :=
  (List.range n).foldl (fun A i => round A RC[i]!) A

theorem permute_eq (A : Array UInt64) : permute A = rounds A 24 := by
  simp only [permute, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, pure_bind, rounds, List.range_eq_range']

theorem rounds_two (A : Array UInt64) (k : Nat) :
    rounds A (2 * k + 2) = round (round (rounds A (2 * k)) RC[2 * k]!) RC[2 * k + 1]! := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rounds_size {A : Array UInt64} (h : A.size = 25) : ∀ n, (rounds A n).size = 25
  | 0 => h
  | n + 1 => by
    simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_size _ _

/-- Memory after `j` loop iterations. -/
def memIter (M : ByteArray) : Nat → ByteArray
  | 0 => M
  | j + 1 => iterM (memIter M j) (2048 + 64 * j)

theorem rc_ldY {M : ByteArray} (hrc : RC4Table M) {i : Nat} (hi : i < 24) :
    ldY M (2048 + 32 * i) = W fun _ => RC[i]! := by
  rw [ldY_eq, show (2048 : Nat) = RC4 from rfl, hrc i hi]; rfl

theorem memIter_spec {M : ByteArray} {S : Nat → Array UInt64} (hS : ∀ k, k < 4 → (S k).size = 25)
    (hA : KSW M 0 S) (hrc : RC4Table M) :
    ∀ j, j ≤ 12 → KSW (memIter M j) 0 (fun k => rounds (S k) (2 * j)) ∧
      FrameExcept M (memIter M j) [(0, 800), (1024, 1824)]
  | 0, _ => ⟨by simpa [rounds, memIter] using hA, FrameExcept.refl _ _⟩
  | j + 1, hj => by
    obtain ⟨hA', hf⟩ := memIter_spec hS hA hrc j (by omega)
    have hav : ∀ a, 2048 ≤ a → Avoids [(0, 800), (1024, 1824)] a (a + 32) := by
      intro a ha; simp only [avoids_cons, avoids_nil, and_true]; omega
    have hrc0 : ldY (memIter M j) (2048 + 64 * j) = W fun _ => RC[2 * j]! := by
      rw [ldY_frame hf (hav _ (by omega)), show 2048 + 64 * j = 2048 + 32 * (2 * j) by ring]
      exact rc_ldY hrc (by omega)
    have hrc1 : ldY (memIter M j) (32 + (2048 + 64 * j)) = W fun _ => RC[2 * j + 1]! := by
      rw [ldY_frame hf (hav _ (by omega)), show 32 + (2048 + 64 * j) = 2048 + 32 * (2 * j + 1) by ring]
      exact rc_ldY hrc (by omega)
    obtain ⟨hA'', hf'⟩ := iter_spec (memIter M j) (2048 + 64 * j) (by omega) _
      (fun k hk => rounds_size (hS k hk) _) _ _ hA' hrc0 hrc1
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      simp only [rounds_two]
      exact hA''
    · refine FrameExcept.mono (FrameExcept.trans hf hf') ?_
      intro r hr
      exact ⟨r, by simp only [List.mem_append] at hr; rcases hr with h | h <;> exact h, le_rfl, le_rfl⟩

theorem iterM_frame (M : ByteArray) (rp : Nat) :
    FrameExcept M (iterM M rp) [(0, 800), (1024, 1824)] := by
  refine FrameExcept.mono (FrameExcept.trans (roundM_frame M 0 1024 rp)
    (roundM_frame (roundM M 0 1024 rp) 1024 0 (32 + rp))) ?_
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨(1024, 1824), by simp, le_rfl, le_rfl⟩
  · exact ⟨(0, 800), by simp, le_rfl, by simp⟩

theorem memIter_frame (M : ByteArray) :
    ∀ j, FrameExcept M (memIter M j) [(0, 800), (1024, 1824)]
  | 0 => FrameExcept.refl _ _
  | j + 1 => frame_trans (memIter_frame M j) (iterM_frame _ _)

/-! ## Traces -/

theorem iter_reach {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (htl : tail.length ≤ 960) (haw : s.activeWords.toNat ≤ 18446744073709551616)
    (hsz : 2065 ≤ s.activeWords.toNat) (M : ByteArray) (r : Nat) (hr : r ≤ 2752) :
    Reach (callState s 21036 (wd r :: wd ret :: tail) M)
      (callState s 22539 (wd r :: wd ret :: tail) (iterM M r)) 3324 := by
  have hr' : r ≤ 2784 := by omega
  have h1 := ((((((r1_cols (ret := ret) hs htl haw hsz M r hr').trans
    (r1_ds hs htl haw hsz M r hr' _ _ _ _ _)).trans
    (r1_row0 hs htl haw hsz M r hr' (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0))).trans
    (r1_row1 hs htl haw hsz (rM1 M 0 1024 r) r hr' (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0))).trans
    (r1_row2 hs htl haw hsz (rM2 M 0 1024 r) r hr' (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0))).trans
    (r1_row3 hs htl haw hsz (rM3 M 0 1024 r) r hr' (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0))).trans
    (r1_row4 hs htl haw hsz (rM4 M 0 1024 r) r hr' (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0))
  have hR : row4 (rM4 M 0 1024 r) 0 1024 (thD0 M 0) (thD1 M 0) (thD2 M 0) (thD3 M 0) (thD4 M 0) =
      roundM M 0 1024 r := rfl
  rw [hR] at h1
  set M1 := roundM M 0 1024 r
  have h2 := ((((((r2_cols (ret := ret) hs htl haw hsz M1 r hr').trans
    (r2_ds hs htl haw hsz M1 r hr' _ _ _ _ _)).trans
    (r2_row0 hs htl haw hsz M1 r hr' (thD0 M1 1024) (thD1 M1 1024) (thD2 M1 1024) (thD3 M1 1024) (thD4 M1 1024))).trans
    (r2_row1 hs htl haw hsz (rM1 M1 1024 0 (32 + r)) r hr' (thD0 M1 1024) (thD1 M1 1024) (thD2 M1 1024) (thD3 M1 1024) (thD4 M1 1024))).trans
    (r2_row2 hs htl haw hsz (rM2 M1 1024 0 (32 + r)) r hr' (thD0 M1 1024) (thD1 M1 1024) (thD2 M1 1024) (thD3 M1 1024) (thD4 M1 1024))).trans
    (r2_row3 hs htl haw hsz (rM3 M1 1024 0 (32 + r)) r hr' (thD0 M1 1024) (thD1 M1 1024) (thD2 M1 1024) (thD3 M1 1024) (thD4 M1 1024))).trans
    (r2_row4 hs htl haw hsz (rM4 M1 1024 0 (32 + r)) r hr' (thD0 M1 1024) (thD1 M1 1024) (thD2 M1 1024) (thD3 M1 1024) (thD4 M1 1024))
  exact (h1.trans h2).mono (by norm_num)

theorem toNat_W (f : Nat → UInt64) : (W f).toNat = il fun k => (f k).toNat := by
  unfold W; exact toNat_ofNat_of_lt (il_lt _)

theorem ksw_of_ks4 {M : ByteArray} {S : Nat → Array UInt64} (h : KS4 M S) : KSW M 0 S := by
  intro x hx
  rw [ldY_eq, show (0 : Nat) = KS from rfl, h x hx]
  unfold W
  simp only [toNat_cplU, laneOf]

theorem ks4_of_ksw {M : ByteArray} {S : Nat → Array UInt64} (h : KSW M 0 S) : KS4 M S := by
  intro x hx
  have := congrArg UInt256.toNat (h x hx)
  rw [ldY_eq, toNat_ofNat_of_lt (word_lt _ _), toNat_W] at this
  rw [show KS = 0 from rfl, this]
  simp only [toNat_cplU, laneOf]

theorem kf4_spec {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kf4 ret tail) (m : ByteArray) (hrc : RC4Table m) :
    ∃ m', (∀ S, Sized4 S → KS4 m S → KS4 m' fun k => permute (S k)) ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800)] ∧
      Call s Entry.kf4 [] ret tail m [] m' Gas.kf4 := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.kf4, Stack.leaf] at this; omega
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : 2065 ≤ s.activeWords.toNat := hs.sized
  refine ⟨memIter m 12, ?_, ?_, ?_⟩
  · intro S hS hK
    have := (memIter_spec hS (ksw_of_ks4 hK) hrc 12 le_rfl).1
    apply ks4_of_ksw
    simpa only [permute_eq] using this
  · simpa only [KS, KB] using memIter_frame m 12
  · let I : Nat → State := fun j => callState s 21036 (wd (2048 + 64 * j) :: wd ret :: tail) (memIter m j)
    have hbody : ∀ j, j < 11 → Reach (I j) (I (j + 1)) 3352 := by
      intro j hj
      have h := (iter_reach (ret := ret) hs htl haw hsz (memIter m j) (2048 + 64 * j) (by omega)).trans
        (kf4_back hs htl (iterM (memIter m j) (2048 + 64 * j)) (2048 + 64 * j) (by omega))
      exact h.of_eq rfl (by simp only [I, memIter]; congr 3; ring)
    have hlast := (iter_reach (ret := ret) hs htl haw hsz (memIter m 11) (2048 + 64 * 11) (by omega)).trans
      (kf4_exit hs htl (iterM (memIter m 11) (2048 + 64 * 11)) (2048 + 64 * 11) (by omega)
        hr.jumpdest hr.small)
    have h := ((kf4_entry hs htl m).trans (Reach.loop (I := I) 11 hbody)).trans hlast
    rw [call_iff, Entry.kf4, Gas.kf4]
    exact (h.mono (by norm_num)).of_eq (by simp) rfl

end MlDsaOpt44.Proofs.Kf4
