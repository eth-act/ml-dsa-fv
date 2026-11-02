import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOpt44.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `kmove`: `KS[x] := (((src[x] << sl) >> sr) & msk) | (KS[x] & keep)`

Five iterations (`x = 0x280, 0x1e0, …, 0`) of five unrolled lanes. Every lane
reads `src[x]` and `KS[x]` before it is written, so the stored value is a
function of the entry memory (`kw m`), also when `src = KS`.
-/

namespace MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.Infra

/-- The word `kmove` stores at address `a` (in `opt44_block` normal form). -/
def kw (M : ByteArray) (src sl sr msk keep a : Nat) : Nat :=
  (keep &&& word M a ||| msk &&& word M (a + src) * 2 ^ sl %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2 ^ sr) %
    115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The memory after one iteration of the loop at `x`. -/
def kbody (M : ByteArray) (src sl sr msk keep x : Nat) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes
      (MachineState.writeBytes
        (MachineState.writeBytes
          (MachineState.writeBytes M
            (Data.Bytes.natToBytesPadded (kw M src sl sr msk keep x) 32) x)
          (Data.Bytes.natToBytesPadded (kw M src sl sr msk keep (32 + x)) 32) (32 + x))
        (Data.Bytes.natToBytesPadded (kw M src sl sr msk keep (64 + x)) 32) (64 + x))
      (Data.Bytes.natToBytesPadded (kw M src sl sr msk keep (96 + x)) 32) (96 + x))
    (Data.Bytes.natToBytesPadded (kw M src sl sr msk keep (128 + x)) 32) (128 + x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem kmove_body {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (M : ByteArray) {x src sl sr msk keep : Nat}
    (hx : 160 ≤ x) (hx' : x + 160 ≤ 800) (hsrc' : src + 800 ≤ 66080) (hsl : sl < 256) (hsr : sr < 256) :
    Reach (callState s 11328 (wd x :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s 11328 (wd (x - 160) :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail)
        (kbody M src sl sr msk keep x)) 326 := by
  have := hr.depth; simp only [Stack.kmove, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  opt44_reach [4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873, 4874, 4875, 4876, 4877, 4878, 4879, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890, 4891, 4892, 4893, 4894, 4895, 4896, 4897, 4898, 4899, 4900, 4901, 4902, 4903, 4904, 4905, 4906, 4907, 4908, 4909, 4910, 4911, 4912, 4913, 4914, 4915, 4916, 4917, 4918, 4919, 4920, 4921] with [word_mstore_disjoint]

theorem kmove_wrap :
    UInt256.ofNat 0 - UInt256.ofNat 160 =
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639776 :=
  by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem kmove_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (M : ByteArray) {src sl sr msk keep : Nat}
    (hsrc' : src + 800 ≤ 66080) (hsl : sl < 256) (hsr : sr < 256) :
    Reach (callState s 11328 (wd 0 :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s ret tail (kbody M src sl sr msk keep 0)) 346 := by
  have := hr.depth; simp only [Stack.kmove, Stack.leaf] at this
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  opt44_reach [4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869, 4870, 4871, 4872, 4873, 4874, 4875, 4876, 4877, 4878, 4879, 4880, 4881, 4882, 4883, 4884, 4885, 4886, 4887, 4888, 4889, 4890, 4891, 4892, 4893, 4894, 4895, 4896, 4897, 4898, 4899, 4900, 4901, 4902, 4903, 4904, 4905, 4906, 4907, 4908, 4909, 4910, 4911, 4912, 4913, 4914, 4915, 4916, 4917, 4918, 4919, 4920, 4921, 4922, 4923, 4924, 4925, 4926, 4927, 4928] with [word_mstore_disjoint, kmove_wrap, hj]
  rfl

theorem kmove_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (M : ByteArray) (src sl sr msk keep : Nat) :
    Reach (callState s 11324 (wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s 11328 (wd 640 :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M) 4 := by
  have := hr.depth; simp only [Stack.kmove, Stack.leaf] at this
  opt44_reach [4813, 4814] with []

theorem kw_lt (M : ByteArray) (src sl sr msk keep a : Nat) : kw M src sl sr msk keep a < 2 ^ 256 :=
  Nat.mod_lt _ (by norm_num)

theorem word_kbody_out (M : ByteArray) (src sl sr msk keep x : Nat) {a : Nat}
    (ha : a + 32 ≤ x ∨ x + 160 ≤ a) : word (kbody M src sl sr msk keep x) a = word M a := by
  unfold kbody
  rw [word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega),
    word_mstore_disjoint _ _ (by omega), word_mstore_disjoint _ _ (by omega),
    word_mstore_disjoint _ _ (by omega)]

theorem word_kbody_in (M : ByteArray) (src sl sr msk keep x : Nat) {y : Nat}
    (hx : x % 32 = 0) (h1 : x ≤ 32 * y) (h2 : 32 * y < x + 160) :
    word (kbody M src sl sr msk keep x) (32 * y) = kw M src sl sr msk keep (32 * y) := by
  have h : 32 * y = x ∨ 32 * y = 32 + x ∨ 32 * y = 64 + x ∨ 32 * y = 96 + x ∨ 32 * y = 128 + x := by
    omega
  unfold kbody
  rcases h with h | h | h | h | h <;> rw [h] <;>
    simp (disch := first | omega | exact kw_lt _ _ _ _ _ _ _) only [word_mstore_disjoint, word_mstore]

theorem frame_kbody (M : ByteArray) (src sl sr msk keep x : Nat) :
    FrameExcept M (kbody M src sl sr msk keep x) [(x, x + 160)] := by
  unfold kbody
  refine ((((FrameExcept.mstore _ _ _).trans (FrameExcept.mstore _ _ _)).trans
    (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)).trans (FrameExcept.mstore _ _ _)
    |>.mono ?_
  intro r hr
  refine ⟨(x, x + 160), by simp, ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega

/-- The memory after `j` loop iterations. -/
def kmem (m : ByteArray) (src sl sr msk keep : Nat) : Nat → ByteArray
  | 0 => m
  | j + 1 => kbody (kmem m src sl sr msk keep j) src sl sr msk keep (640 - 160 * j)

theorem kmem_inv (m : ByteArray) {src : Nat} (sl sr msk keep : Nat) (hsrc : src = 0 ∨ 800 ≤ src) :
    ∀ j, j ≤ 5 →
      (∀ a, (a + 32 ≤ 800 - 160 * j ∨ 800 ≤ a) → word (kmem m src sl sr msk keep j) a = word m a) ∧
      (∀ y, y < 25 → 25 - 5 * j ≤ y →
        word (kmem m src sl sr msk keep j) (32 * y) = kw m src sl sr msk keep (32 * y)) ∧
      FrameExcept m (kmem m src sl sr msk keep j) [(0, 800)]
  | 0, _ => ⟨fun _ _ => rfl, fun y hy h => by omega, FrameExcept.refl _ _⟩
  | j + 1, hj => by
    obtain ⟨hA, hB, hC⟩ := kmem_inv m sl sr msk keep hsrc j (by omega)
    simp only [kmem]
    refine ⟨fun a ha => ?_, fun y hy h => ?_, ?_⟩
    · rw [word_kbody_out _ _ _ _ _ _ _ (by omega), hA a (by omega)]
    · by_cases hy' : 32 * y < 800 - 160 * j
      · rw [word_kbody_in _ _ _ _ _ _ _ (by omega) (by omega) (by omega)]
        unfold kw
        rw [hA _ (by omega)]
        rcases hsrc with rfl | hsrc
        · rw [Nat.add_zero, hA _ (by omega)]
        · rw [hA _ (by omega)]
      · rw [word_kbody_out _ _ _ _ _ _ _ (by omega), hB y hy (by omega)]
    · exact (hC.trans (frame_kbody _ _ _ _ _ _ _)).mono (by
        intro r hr
        refine ⟨(0, 800), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega)

theorem kw_eq (m : ByteArray) (src sl sr msk keep y : Nat) (hmsk : msk < 2 ^ 256)
    (hkeep : keep < 2 ^ 256) :
    kw m src sl sr msk keep (32 * y) =
      (word m (src + 32 * y) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (KS + 32 * y) &&& keep) := by
  unfold kw
  have hlt : (keep &&& word m (32 * y) ||| msk &&& word m (32 * y + src) * 2 ^ sl %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2 ^ sr) <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left hkeep) (lt_of_le_of_lt Nat.and_le_left hmsk)
  rw [Nat.mod_eq_of_lt hlt, Nat.or_comm, Nat.and_comm keep, Nat.and_comm msk, KS,
    Nat.zero_add, Nat.add_comm src]
  rfl

theorem kmove_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.kmove ret tail) (m : ByteArray) {src sl sr msk keep : Nat}
    (hsrc : src = KS ∨ KS + 800 ≤ src) (hsrc' : src + 800 ≤ TOP) (hsl : sl < 256) (hsr : sr < 256)
    (hmsk : msk < 2 ^ 256) (hkeep : keep < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (KS + 32 * x) =
        (word m (src + 32 * x) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (KS + 32 * x) &&& keep)) ∧
      FrameExcept m m' [(KS, KS + 800)] ∧
      Call s Entry.kmove [wd keep, wd msk, wd sr, wd sl, wd src] ret tail m [] m' Gas.kmove := by
  simp only [KS, TOP, Nat.zero_add] at hsrc hsrc'
  obtain ⟨-, hB, hC⟩ := kmem_inv m sl sr msk keep hsrc 5 le_rfl
  refine ⟨kmem m src sl sr msk keep 5, fun x hx => ?_, by simpa [KS] using hC, ?_⟩
  · rw [KS, Nat.zero_add, hB x hx (by omega), kw_eq _ _ _ _ _ _ _ hmsk hkeep, KS, Nat.zero_add]
  let I : Nat → State := fun j =>
    callState s 11328 (wd (640 - 160 * j) :: wd keep :: wd msk :: wd sr :: wd sl :: wd src ::
      wd ret :: tail) (kmem m src sl sr msk keep j)
  have hbody : ∀ j, j < 4 → Reach (I j) (I (j + 1)) 326 := by
    intro j hj
    have h := kmove_body hs hr (kmem m src sl sr msk keep j) (x := 640 - 160 * j) (src := src)
      (sl := sl) (sr := sr) (msk := msk) (keep := keep) (by omega) (by omega) hsrc' hsl hsr
    rwa [show 640 - 160 * j - 160 = 640 - 160 * (j + 1) by omega] at h
  have hloop := Reach.loop (I := I) 4 hbody
  have hlast := kmove_last hs hr (kmem m src sl sr msk keep 4) (src := src) (sl := sl) (sr := sr)
    (msk := msk) (keep := keep) hsrc' hsl hsr
  have hentry := kmove_entry hs hr m src sl sr msk keep
  rw [call_iff, Entry.kmove, Gas.kmove]
  exact ((hentry.trans hloop).trans hlast).of_eq (by simp) rfl

end MlDsaOpt44.Proofs.WP4
