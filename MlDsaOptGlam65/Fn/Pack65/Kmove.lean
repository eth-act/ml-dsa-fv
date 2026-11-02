import MlDsaOpt44.Fn.Sponge.Mem
import MlDsaOptGlam65.Infra.Reach
import MlDsaOptGlam65.Infra.Reflect
/- Adapted by hand from `MlDsaOptGlam44/Fn/Sponge/Kmove.lean` (glam 65 indices,
`TOP = 0x16220`); `Entry`/`Gas`/`Stack` appear as literals and the wrapper in
`Fn/Pack65.lean` restates the contract with the layout names. -/
set_option maxHeartbeats 0
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `kmove`: `KS[x] := (((src[x] << sl) >> sr) & msk) | (KS[x] & keep)`

Five iterations (`x = 0x280, 0x1e0, …, 0`) of five unrolled lanes. Every lane
reads `src[x]` and `KS[x]` before it is written, so the stored value is a
function of the entry memory (`kw m`), also when `src = KS`.
-/

namespace MlDsaOptGlam65.Proofs.Pack65

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.WP4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOptGlam65.Proofs.Infra

/-- The word `kmove` stores at address `a` (in `glam65_block` normal form). -/
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
    (hr : RetOK 74 ret tail) (M : ByteArray) {x src sl sr msk keep : Nat}
    (hx : 160 ≤ x) (hx' : x + 160 ≤ 800) (hsrc' : src + 800 ≤ 90656) (hsl : sl < 256) (hsr : sr < 256) :
    Reach (callState s 18103 (wd x :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s 18103 (wd (x - 160) :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail)
        (kbody M src sl sr msk keep x)) 326 := by
  have := hr.depth
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  glam65_rreach [7533, 7534, 7535, 7536, 7537, 7538, 7539, 7540, 7541, 7542, 7543, 7544, 7545, 7546, 7547, 7548, 7549, 7550, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559, 7560, 7561, 7562, 7563, 7564, 7565, 7566, 7567, 7568, 7569, 7570, 7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7603, 7604, 7605, 7606, 7607, 7608, 7609, 7610, 7611, 7612, 7613, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7621, 7622, 7623, 7624, 7625, 7626, 7627, 7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639] with [word_mstore_disjoint]

theorem kmove_wrap :
    UInt256.ofNat 0 - UInt256.ofNat 160 =
      UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639776 :=
  by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem kmove_last {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) {src sl sr msk keep : Nat}
    (hsrc' : src + 800 ≤ 90656) (hsl : sl < 256) (hsr : sr < 256) :
    Reach (callState s 18103 (wd 0 :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s ret tail (kbody M src sl sr msk keep 0)) 346 := by
  have := hr.depth
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized; simp only [memWords] at hsz
  have hret := hr.small
  have hj := hr.jumpdest
  glam65_rreach [7533, 7534, 7535, 7536, 7537, 7538, 7539, 7540, 7541, 7542, 7543, 7544, 7545, 7546, 7547, 7548, 7549, 7550, 7551, 7552, 7553, 7554, 7555, 7556, 7557, 7558, 7559, 7560, 7561, 7562, 7563, 7564, 7565, 7566, 7567, 7568, 7569, 7570, 7571, 7572, 7573, 7574, 7575, 7576, 7577, 7578, 7579, 7580, 7581, 7582, 7583, 7584, 7585, 7586, 7587, 7588, 7589, 7590, 7591, 7592, 7593, 7594, 7595, 7596, 7597, 7598, 7599, 7600, 7601, 7602, 7603, 7604, 7605, 7606, 7607, 7608, 7609, 7610, 7611, 7612, 7613, 7614, 7615, 7616, 7617, 7618, 7619, 7620, 7621, 7622, 7623, 7624, 7625, 7626, 7627, 7628, 7629, 7630, 7631, 7632, 7633, 7634, 7635, 7636, 7637, 7638, 7639, 7640, 7641, 7642, 7643, 7644, 7645, 7646] with [word_mstore_disjoint, kmove_wrap, hj]
  rfl

theorem kmove_entry {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (M : ByteArray) (src sl sr msk keep : Nat) :
    Reach (callState s 18099 (wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M)
      (callState s 18103 (wd 640 :: wd keep :: wd msk :: wd sr :: wd sl :: wd src :: wd ret :: tail) M) 4 := by
  have := hr.depth
  glam65_rreach [7531, 7532] with []

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
      (word m (src + 32 * y) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (32 * y) &&& keep) := by
  unfold kw
  have hlt : (keep &&& word m (32 * y) ||| msk &&& word m (32 * y + src) * 2 ^ sl %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 / 2 ^ sr) <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left hkeep) (lt_of_le_of_lt Nat.and_le_left hmsk)
  rw [Nat.mod_eq_of_lt hlt, Nat.or_comm, Nat.and_comm keep, Nat.and_comm msk,
    Nat.add_comm src]
  rfl

theorem kmove_call_aux {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK 74 ret tail) (m : ByteArray) {src sl sr msk keep : Nat}
    (hsrc : src = 0 ∨ 800 ≤ src) (hsrc' : src + 800 ≤ 90656) (hsl : sl < 256) (hsr : sr < 256)
    (hmsk : msk < 2 ^ 256) (hkeep : keep < 2 ^ 256) :
    ∃ m', (∀ x, x < 25 → word m' (32 * x) =
        (word m (src + 32 * x) * 2 ^ sl % 2 ^ 256 / 2 ^ sr &&& msk) ||| (word m (32 * x) &&& keep)) ∧
      FrameExcept m m' [(0, 800)] ∧
      Call s 18099 [wd keep, wd msk, wd sr, wd sl, wd src] ret tail m [] m' 1654 := by
  obtain ⟨-, hB, hC⟩ := kmem_inv m sl sr msk keep hsrc 5 le_rfl
  refine ⟨kmem m src sl sr msk keep 5, fun x hx => ?_, hC, ?_⟩
  · rw [hB x hx (by omega), kw_eq _ _ _ _ _ _ _ hmsk hkeep]
  let I : Nat → State := fun j =>
    callState s 18103 (wd (640 - 160 * j) :: wd keep :: wd msk :: wd sr :: wd sl :: wd src ::
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
  rw [call_iff]
  exact ((hentry.trans hloop).trans hlast).of_eq (by simp) rfl

end MlDsaOptGlam65.Proofs.Pack65
