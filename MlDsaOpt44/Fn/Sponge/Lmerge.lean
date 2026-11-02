import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOpt44.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `lmerge`: `dst[w] := b' ^ ((a[w] ^ b') & ma)`, `b' = b[w] << sl`

`k` iterations of 11 unrolled words; the source addresses are formed as
`p + (b − a)`, `p + (dst − a)` modulo `2^256` from the pointer `p` into `a`.
Each word reads `a[w]`, `b[w]` before it writes `dst[w]` (`dst = a` allowed).
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

/-- The word `lmerge` stores, reading `b` at `ab` and `a` at `aa` (`opt44_block` form). -/
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
    Reach (callState s 11452 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s 11452 (wd (352 + p) :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail)
        (lbody M ma sl p pb pd)) 683 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  simp only [Nat.reducePow] at hb hb0 hd hd0
  opt44_reach [4930, 4931, 4932, 4933, 4934, 4935, 4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943, 4944, 4945, 4946, 4947, 4948, 4949, 4950, 4951, 4952, 4953, 4954, 4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155] with [word_mstore_disjoint, hb, hb0, hd, hd0, he]

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
    Reach (callState s 11452 (wd p :: wd (352 + p) :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s ret tail (lbody M ma sl p pb pd)) 703 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  simp only [Nat.reducePow] at hb hb0 hd hd0
  opt44_reach [4930, 4931, 4932, 4933, 4934, 4935, 4936, 4937, 4938, 4939, 4940, 4941, 4942, 4943, 4944, 4945, 4946, 4947, 4948, 4949, 4950, 4951, 4952, 4953, 4954, 4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4969, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977, 4978, 4979, 4980, 4981, 4982, 4983, 4984, 4985, 4986, 4987, 4988, 4989, 4990, 4991, 4992, 4993, 4994, 4995, 4996, 4997, 4998, 4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5084, 5085, 5086, 5087, 5088, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5161, 5162] with [word_mstore_disjoint, hb, hb0, hd, hd0, lt_self_iff_false, hj]
  rfl

theorem lmerge_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.lmerge ret tail) (M : ByteArray) (p e sl db ma dd : Nat) :
    Reach (callState s 11451 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M)
      (callState s 11452 (wd p :: wd e :: wd sl :: wd db :: wd ma :: wd dd :: wd ret :: tail) M) 1 := by
  have := hr.depth; simp only [Stack.lmerge, Stack.leaf] at this
  opt44_reach [4929] with []

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
    callState s 11452 (wd (a + 352 * j) :: wd (a + 352 * (k + 1)) :: wd sl :: wd db :: wd ma ::
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

end MlDsaOpt44.Proofs.WP4
