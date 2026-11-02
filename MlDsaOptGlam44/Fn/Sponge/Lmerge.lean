import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam44.Budget
import MlDsaOptGlam44.Layout
/- Ported from `MlDsaOpt44/Fn/Sponge/Lmerge.lean` by `scripts/proofgen_port.py --glam 44`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `lmerge`: `dst[w] := b' ^ ((a[w] ^ b') & ma)`, `b' = b[w] << sl`

`k` iterations of 11 unrolled words; the source addresses are formed as
`p + (b − a)`, `p + (dst − a)` modulo `2^256` from the pointer `p` into `a`.
Each word reads `a[w]`, `b[w]` before it writes `dst[w]` (`dst = a` allowed).
-/

namespace MlDsaOptGlam44.Proofs.WP4

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam44.Proofs.Infra

/-- The word `lmerge` stores, reading `b` at `ab` and `a` at `aa` (`glam44_block` form). -/
def lw (M : ByteArray) (ma sl ab aa : Nat) : Nat :=
  (ma &&& (word M ab * 2 ^ sl ^^^ word M aa) ^^^ word M ab * 2 ^ sl) % 115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The memory after one iteration at pointer `p` (`b` row at `pb`, `dst` row at `pd`). -/
def lbody (M : ByteArray) (ma sl p pb pd : Nat) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes M
      (Data.Bytes.natToBytesPadded (lw M ma sl pb p) 32) pd)
      (Data.Bytes.natToBytesPadded (lw M ma sl (32 + pb) (32 + p)) 32) (32 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (64 + pb) (64 + p)) 32) (64 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (96 + pb) (96 + p)) 32) (96 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (128 + pb) (128 + p)) 32) (128 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (160 + pb) (160 + p)) 32) (160 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (192 + pb) (192 + p)) 32) (192 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (224 + pb) (224 + p)) 32) (224 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (256 + pb) (256 + p)) 32) (256 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (288 + pb) (288 + p)) 32) (288 + pd))
      (Data.Bytes.natToBytesPadded (lw M ma sl (320 + pb) (320 + p)) 32) (320 + pd)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem lmerge_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (M : ByteArray) {p e sl db ma dd pb pd : Nat}
    (hp : p + 352 ≤ 66080) (hpb : pb + 352 ≤ 66080) (hpd : pd + 352 ≤ 66080)
    (he : 352 + p < e) (he' : e < 2 ^ 256) (hsl : sl < 256)
    (hb : ∀ c, c < 352 → (c + p + db) % 2 ^ 256 = c + pb)
    (hb0 : (p + db) % 2 ^ 256 = pb)
    (hd : ∀ c, c < 352 → (dd + (c + p)) % 2 ^ 256 = c + pd)
    (hd0 : (dd + p) % 2 ^ 256 = pd)
    (hda : pd = p ∨ pd + 352 ≤ p ∨ p + 352 ≤ pd) (hdb' : pd + 352 ≤ pb ∨ pb + 352 ≤ pd) :
    Reach (callState s 18542 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s 18542 (wd (352 + p) :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail)
        (lbody M ma sl p pb pd)) 683 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  simp only [Nat.reducePow] at hb hb0 hd hd0
  glam44_rreach [7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731, 7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7749, 7750, 7751, 7752, 7753, 7754, 7755, 7756, 7757, 7758, 7759, 7760, 7761, 7762, 7763, 7764, 7765, 7766, 7767, 7768, 7769, 7770, 7771, 7772, 7773, 7774, 7775, 7776, 7777, 7778, 7779, 7780, 7781, 7782, 7783, 7784, 7785, 7786, 7787, 7788, 7789, 7790, 7791, 7792, 7793, 7794, 7795, 7796, 7797, 7798, 7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815, 7816, 7817, 7818, 7819, 7820, 7821, 7822, 7823, 7824, 7825, 7826, 7827, 7828, 7829, 7830, 7831, 7832, 7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853, 7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861, 7862, 7863, 7864, 7865, 7866, 7867, 7868, 7869, 7870, 7871, 7872, 7873, 7874, 7875, 7876, 7877, 7878, 7879, 7880, 7881, 7882, 7883, 7884, 7885, 7886, 7887, 7888, 7889, 7890, 7891, 7892, 7893, 7894, 7895, 7896, 7897, 7898, 7899, 7900, 7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7933, 7934, 7935, 7936, 7937, 7938, 7939, 7940] with [word_mstore_disjoint, hb, hb0, hd, hd0, he]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem lmerge_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (M : ByteArray) {p sl db ma dd pb pd : Nat}
    (hp : p + 352 ≤ 66080) (hpb : pb + 352 ≤ 66080) (hpd : pd + 352 ≤ 66080)
    (hsl : sl < 256)
    (hb : ∀ c, c < 352 → (c + p + db) % 2 ^ 256 = c + pb)
    (hb0 : (p + db) % 2 ^ 256 = pb)
    (hd : ∀ c, c < 352 → (dd + (c + p)) % 2 ^ 256 = c + pd)
    (hd0 : (dd + p) % 2 ^ 256 = pd)
    (hda : pd = p ∨ pd + 352 ≤ p ∨ p + 352 ≤ pd) (hdb' : pd + 352 ≤ pb ∨ pb + 352 ≤ pd) :
    Reach (callState s 18542 (wd p :: wd (352 + p) :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s ret tail (lbody M ma sl p pb pd)) 703 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  simp only [Nat.reducePow] at hb hb0 hd hd0
  glam44_rreach [7715, 7716, 7717, 7718, 7719, 7720, 7721, 7722, 7723, 7724, 7725, 7726, 7727, 7728, 7729, 7730, 7731, 7732, 7733, 7734, 7735, 7736, 7737, 7738, 7739, 7740, 7741, 7742, 7743, 7744, 7745, 7746, 7747, 7748, 7749, 7750, 7751, 7752, 7753, 7754, 7755, 7756, 7757, 7758, 7759, 7760, 7761, 7762, 7763, 7764, 7765, 7766, 7767, 7768, 7769, 7770, 7771, 7772, 7773, 7774, 7775, 7776, 7777, 7778, 7779, 7780, 7781, 7782, 7783, 7784, 7785, 7786, 7787, 7788, 7789, 7790, 7791, 7792, 7793, 7794, 7795, 7796, 7797, 7798, 7799, 7800, 7801, 7802, 7803, 7804, 7805, 7806, 7807, 7808, 7809, 7810, 7811, 7812, 7813, 7814, 7815, 7816, 7817, 7818, 7819, 7820, 7821, 7822, 7823, 7824, 7825, 7826, 7827, 7828, 7829, 7830, 7831, 7832, 7833, 7834, 7835, 7836, 7837, 7838, 7839, 7840, 7841, 7842, 7843, 7844, 7845, 7846, 7847, 7848, 7849, 7850, 7851, 7852, 7853, 7854, 7855, 7856, 7857, 7858, 7859, 7860, 7861, 7862, 7863, 7864, 7865, 7866, 7867, 7868, 7869, 7870, 7871, 7872, 7873, 7874, 7875, 7876, 7877, 7878, 7879, 7880, 7881, 7882, 7883, 7884, 7885, 7886, 7887, 7888, 7889, 7890, 7891, 7892, 7893, 7894, 7895, 7896, 7897, 7898, 7899, 7900, 7901, 7902, 7903, 7904, 7905, 7906, 7907, 7908, 7909, 7910, 7911, 7912, 7913, 7914, 7915, 7916, 7917, 7918, 7919, 7920, 7921, 7922, 7923, 7924, 7925, 7926, 7927, 7928, 7929, 7930, 7931, 7932, 7933, 7934, 7935, 7936, 7937, 7938, 7939, 7940, 7941, 7942, 7943, 7944, 7945, 7946, 7947] with [word_mstore_disjoint, hb, hb0, hd, hd0, lt_self_iff_false, hj]
  rfl

theorem lmerge_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (M : ByteArray) (p e sl db ma dd : Nat) :
    Reach (callState s 18541 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s 18542 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M) 1 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  glam44_rreach [7714] with []

theorem lw_lt (M : ByteArray) (ma sl ab aa : Nat) : lw M ma sl ab aa < 2 ^ 256 :=
  Nat.mod_lt _ (by norm_num)

theorem word_lbody_out (M : ByteArray) (ma sl p pb pd : Nat) {y : Nat}
    (h : y + 32 ≤ pd ∨ pd + 352 ≤ y) : word (lbody M ma sl p pb pd) y = word M y := by
  unfold lbody
  simp (disch := omega) only [word_mstore_disjoint]

theorem word_lbody_in (M : ByteArray) (ma sl p pb pd : Nat) {i : Nat} (hi : i < 11) :
    word (lbody M ma sl p pb pd) (32 * i + pd) = lw M ma sl (32 * i + pb) (32 * i + p) := by
  interval_cases i <;>
    simp (disch := first | omega | exact lw_lt _ _ _ _ _) only [lbody, Nat.reduceMul,
      Nat.zero_add, word_mstore_disjoint, word_mstore]

theorem frame_step {M M' : ByteArray} {lo hi a v : Nat} (h : FrameExcept M M' [(lo, hi)])
    (h1 : lo ≤ a) (h2 : a + 32 ≤ hi) :
    FrameExcept M (MachineState.writeBytes M' (Data.Bytes.natToBytesPadded v 32) a) [(lo, hi)] :=
  (h.trans (FrameExcept.mstore _ _ _)).mono (by
    intro r hr
    refine ⟨(lo, hi), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega)

theorem frame_lbody (M : ByteArray) (ma sl p pb pd : Nat) :
    FrameExcept M (lbody M ma sl p pb pd) [(pd, pd + 352)] := by
  unfold lbody
  repeat' first | exact FrameExcept.refl _ _ | apply frame_step
  all_goals omega

/-- The memory after `j` iterations. -/
def lmem (m : ByteArray) (a b dst ma sl : Nat) : Nat → ByteArray
  | 0 => m
  | j + 1 => lbody (lmem m a b dst ma sl j) ma sl (a + 352 * j) (b + 352 * j) (dst + 352 * j)

theorem lmem_inv (m : ByteArray) {a b dst k : Nat} (ma sl : Nat)
    (hda : dst = a ∨ dst + 352 * k ≤ a ∨ a + 352 * k ≤ dst)
    (hdb : dst + 352 * k ≤ b ∨ b + 352 * k ≤ dst) :
    ∀ j, j ≤ k →
      (∀ y, (y + 32 ≤ dst ∨ dst + 352 * j ≤ y) → word (lmem m a b dst ma sl j) y = word m y) ∧
      (∀ w, w < 11 * j →
        word (lmem m a b dst ma sl j) (dst + 32 * w) = lw m ma sl (b + 32 * w) (a + 32 * w)) ∧
      FrameExcept m (lmem m a b dst ma sl j) [(dst, dst + 352 * j)]
  | 0, _ => ⟨fun _ _ => rfl, fun w hw => by omega, FrameExcept.refl _ _⟩
  | j + 1, hj => by
    obtain ⟨hA, hB, hC⟩ := lmem_inv m ma sl hda hdb j (by omega)
    simp only [lmem]
    refine ⟨fun y hy => ?_, fun w hw => ?_, ?_⟩
    · rw [word_lbody_out _ _ _ _ _ _ (by omega), hA y (by omega)]
    · by_cases hw' : w < 11 * j
      · rw [word_lbody_out _ _ _ _ _ _ (by omega), hB w hw']
      · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 11 ∧ w = 11 * j + i := ⟨w - 11 * j, by omega, by omega⟩
        rw [show dst + 32 * (11 * j + i) = 32 * i + (dst + 352 * j) by omega,
          word_lbody_in _ _ _ _ _ _ hi]
        unfold lw
        rw [hA _ (by omega), hA _ (by omega), show 32 * i + (b + 352 * j) = b + 32 * (11 * j + i) by omega,
          show 32 * i + (a + 352 * j) = a + 32 * (11 * j + i) by omega]
    · exact (hC.trans (frame_lbody _ _ _ _ _ _)).mono (by
        intro r hr
        refine ⟨(dst, dst + 352 * (j + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega)

theorem lw_eq (m : ByteArray) (ma sl ab aa : Nat) (hma : ma < 2 ^ 256) :
    lw m ma sl ab aa =
      let b' := word m ab * 2 ^ sl % 2 ^ 256
      b' ^^^ ((word m aa ^^^ b') &&& ma) := by
  unfold lw
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) = 2 ^ 256 by norm_num, Nat.xor_mod_two_pow, Nat.and_mod_two_pow,
    Nat.xor_mod_two_pow, Nat.mod_eq_of_lt hma, Nat.mod_eq_of_lt (word_lt m aa)]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases ma.testBit i <;> cases (word m aa).testBit i <;>
    cases (word m ab * 2 ^ sl % 2 ^ 256).testBit i <;> rfl

set_option maxRecDepth 100000 in
theorem lmerge_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (m : ByteArray) {dst a b ma sl k : Nat}
    (hk : 1 ≤ k) (hdst : dst + 352 * k ≤ TOP) (ha : a + 352 * k ≤ TOP) (hb : b + 352 * k ≤ TOP)
    (hda : dst = a ∨ dst + 352 * k ≤ a ∨ a + 352 * k ≤ dst)
    (hdb : dst + 352 * k ≤ b ∨ b + 352 * k ≤ dst) (hma : ma < 2 ^ 256) (hsl : sl < 256) :
    ∃ m', (∀ w, w < 11 * k → word m' (dst + 32 * w) =
        let b' := word m (b + 32 * w) * 2 ^ sl % 2 ^ 256
        b' ^^^ ((word m (a + 32 * w) ^^^ b') &&& ma)) ∧
      FrameExcept m m' [(dst, dst + 352 * k)] ∧
      Call s Entry.lmerge [wd a, wd (a + 352 * k), wd sl, wd ((b + 2 ^ 256 - a) % 2 ^ 256), wd ma,
        wd ((dst + 2 ^ 256 - a) % 2 ^ 256)] ret tail m [] m' (Gas.lmerge k) := by
  simp only [TOP] at hdst ha hb
  obtain ⟨-, hB, hC⟩ := lmem_inv m ma sl hda hdb k le_rfl
  refine ⟨lmem m a b dst ma sl k, fun w hw => by rw [hB w hw, lw_eq _ _ _ _ _ hma], hC, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  generalize hdb' : (b + 2 ^ 256 - a) % 2 ^ 256 = db
  generalize hdd' : (dst + 2 ^ 256 - a) % 2 ^ 256 = dd
  have hdbl : db < 2 ^ 256 := hdb' ▸ Nat.mod_lt _ (by norm_num)
  have hddl : dd < 2 ^ 256 := hdd' ▸ Nat.mod_lt _ (by norm_num)
  have hB' : ∀ j c, c < 352 → j ≤ k → (c + (a + 352 * j) + db) % 2 ^ 256 = c + (b + 352 * j) := by
    intro j c hc hj; subst hdb'; omega
  have hD' : ∀ j c, c < 352 → j ≤ k → (dd + (c + (a + 352 * j))) % 2 ^ 256 = c + (dst + 352 * j) := by
    intro j c hc hj; subst hdd'; omega
  let I : Nat → State := fun j =>
    callState s 18542 (wd (a + 352 * j) :: wd (a + 352 * (k + 1)) :: wd sl :: wd db :: wd ma ::
      wd dd :: wd ret :: tail) (lmem m a b dst ma sl j)
  have hbody : ∀ j, j < k → Reach (I j) (I (j + 1)) 683 := by
    intro j hj
    have h := lmerge_body hs hr (lmem m a b dst ma sl j) (p := a + 352 * j) (e := a + 352 * (k + 1))
      (sl := sl) (db := db) (ma := ma) (dd := dd) (pb := b + 352 * j) (pd := dst + 352 * j)
      (by omega) (by omega) (by omega) (by omega) (by omega) hsl
      (fun c hc => hB' j c hc (by omega)) (by simpa using hB' j 0 (by norm_num) (by omega))
      (fun c hc => hD' j c hc (by omega)) (by simpa using hD' j 0 (by norm_num) (by omega))
      (by omega) (by omega)
    rwa [show 352 + (a + 352 * j) = a + 352 * (j + 1) by omega] at h
  have hloop := Reach.loop (I := I) k hbody
  have hlast := lmerge_last hs hr (lmem m a b dst ma sl k) (p := a + 352 * k)
      (sl := sl) (db := db) (ma := ma) (dd := dd) (pb := b + 352 * k) (pd := dst + 352 * k)
      (by omega) (by omega) (by omega) hsl
      (fun c hc => hB' k c hc le_rfl) (by simpa using hB' k 0 (by norm_num) le_rfl)
      (fun c hc => hD' k c hc le_rfl) (by simpa using hD' k 0 (by norm_num) le_rfl)
      (by omega) (by omega)
  rw [show 352 + (a + 352 * k) = a + 352 * (k + 1) by omega] at hlast
  have hentry := lmerge_entry hs hr m a (a + 352 * (k + 1)) sl db ma dd
  rw [call_iff, Entry.lmerge, Gas.lmerge]
  refine ((hentry.trans (hloop.trans hlast)).mono (by omega)).of_eq (by simp [I]) rfl

end MlDsaOptGlam44.Proofs.WP4
