import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Sponge
import MlDsaOpt44.Math.SpongeG234
import MlDsaOpt44.Fn.Keccak
import MlDsaOpt44.Fn.Blk
import MlDsaOpt44.Fn.Fix
import MlDsaOpt44.Fn.Sponge
set_option warningAsError true
/-!
# Building blocks of the mixed SIMD groups (`seg_g2`, `seg_win`)

* `HBlocks m ab fl St n`: the heads (first 256 candidates, first 32 flag
  words) of the first `n` squeezed blocks of a group are at `ab` / `fl`,
  block `b` made from the slot states `St b`;
* `kb_round`, `kbh_round`: glue, `kf4`, glue, `blk b` (resp. `blkh` for
  block 4);
* `ks4_trabs_full`: what `trabs` does to the `tr` slot `sh` (one full block
  of the padded public key); `absorb_round`: `trabs` then `kb_round`.
-/

namespace MlDsaOpt44.Proofs.Ex

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.Infra

theorem KS4.congr {m : ByteArray} {S S' : Nat → Fips202.SpongeState} (h : KS4 m S)
    (hS : ∀ k, k < 4 → S k = S' k) : KS4 m S' := fun x hx => by
  rw [h x hx]; exact il_congr fun k hk => by rw [hS k hk]

theorem KS4.frame {m m' : ByteArray} {rs : List (Nat × Nat)} {S : Nat → Fips202.SpongeState}
    (h : KS4 m S) (hf : FrameExcept m m' rs) (ha : Avoids rs KS (KS + 800)) : KS4 m' S := fun x hx => by
  rw [word_frame hf ha (a := KS + 32 * x) (by omega) (by omega)]; exact h x hx

theorem pack4_congr {v w : Nat → Nat} (h : ∀ k, k < 4 → v k = w k) : pack4 v = pack4 w := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem flagWord_congr {F G : Nat → Fips202.SpongeState} (h : ∀ k, k < 4 → F k = G k) (g : Nat) :
    flagWord F g = flagWord G g := by
  unfold flagWord
  have e : ((List.range 8).map fun i => pack4 fun k => cand (F k) (8 * g + i) + 2 ^ 23 - Fips204.q) =
      (List.range 8).map fun i => pack4 fun k => cand (G k) (8 * g + i) + 2 ^ 23 - Fips204.q :=
    List.map_congr_left fun i _ => pack4_congr fun k hk => by rw [h k hk]
  rw [e]

theorem sized4_permute {S : Nat → Fips202.SpongeState} (hS : Sized4 S) :
    Sized4 fun k => Keccak.permute (S k) := fun k hk => permute_size (hS k hk)

/-- The heads of blocks `0 … n − 1` of a SIMD group at `ab` / `fl`, block `b`
made from the slot states `St b`. -/
def HBlocks (m : ByteArray) (ab fl : Nat) (St : Nat → Nat → Fips202.SpongeState) (n : Nat) : Prop :=
  ∀ b, b < n →
    (∀ i, i < 56 → b * 56 + i < 256 → word m (ab + 1792 * b + 32 * i) = pack4 fun k => cand (St b k) i) ∧
    (∀ g, g < 7 → b * 7 + g < 32 → word m (fl + 224 * b + 32 * g) = flagWord (St b) g)

theorem HBlocks.zero (m : ByteArray) (ab fl : Nat) (St : Nat → Nat → Fips202.SpongeState) :
    HBlocks m ab fl St 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem HBlocks.frame {m m' : ByteArray} {ab fl : Nat} {St : Nat → Nat → Fips202.SpongeState} {n : Nat}
    {rs : List (Nat × Nat)} (h : HBlocks m ab fl St n) (hf : FrameExcept m m' rs)
    (ha : Avoids rs ab (ab + 1792 * n)) (hb : Avoids rs fl (fl + 224 * n)) : HBlocks m' ab fl St n :=
  fun b hbn => ⟨fun i hi hh => by
      rw [word_frame hf ha (a := ab + 1792 * b + 32 * i) (by omega) (by omega)]; exact (h b hbn).1 i hi hh,
    fun g hg hh => by
      rw [word_frame hf hb (a := fl + 224 * b + 32 * g) (by omega) (by omega)]; exact (h b hbn).2 g hg hh⟩

theorem HBlocks.congr {m : ByteArray} {ab fl : Nat} {St St' : Nat → Nat → Fips202.SpongeState} {n : Nat}
    (h : HBlocks m ab fl St n) (hS : ∀ b, b < n → ∀ k, k < 4 → St b k = St' b k) :
    HBlocks m ab fl St' n :=
  fun b hb => ⟨fun i hi hh => by rw [(h b hb).1 i hi hh]; exact pack4_congr fun k hk => by rw [hS b hb k hk],
    fun g hg hh => by rw [(h b hb).2 g hg hh]; exact flagWord_congr (fun k hk => by rw [hS b hb k hk]) g⟩

/-- Five block heads at `ABUF` / `FL` make slot `sl` a `gfix` slot. -/
theorem HBlocks.slotHead {m : ByteArray} {St : Nat → Nat → Fips202.SpongeState}
    (h : HBlocks m ABUF FL St 5) {sl : Nat} (hsl : sl < 4) {I : Fips202.SpongeState}
    (hSt : ∀ b, b < 5 → St b sl = permN (b + 1) I) : SlotHead m sl I := by
  refine ⟨fun t ht => ?_, fun g hg => ?_⟩
  · have hb : t / 56 < 5 := by omega
    rw [show ABUF + 32 * t = ABUF + 1792 * (t / 56) + 32 * (t % 56) by omega,
      (h _ hb).1 _ (Nat.mod_lt _ (by norm_num)) (by omega), lane_pack4_cand _ _ hsl, hSt _ hb]
    rfl
  · have hb : g / 7 < 5 := by omega
    rw [show FL + 32 * g = FL + 224 * (g / 7) + 32 * (g % 7) by omega,
      (h _ hb).2 _ (Nat.mod_lt _ (by norm_num)) (by omega), flagBit_flagWord _ _ hsl, hSt _ hb]
    rw [any_congr_mem (q := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) fun i hi => by
      rw [List.mem_range] at hi
      unfold candI
      rw [show (8 * g + i) / 56 = g / 7 by omega, show (8 * g + i) % 56 = 8 * (g % 7) + i by omega]]

/-- Disjointness of a block buffer pair at `ab` / `fl` from `KS`, below `TOP`. -/
structure BufOK (ab fl : Nat) : Prop where
  lo1 : KS + 800 ≤ ab
  hi1 : ab + 1792 * 5 ≤ TOP
  lo2 : KS + 800 ≤ fl
  hi2 : fl + 224 * 5 ≤ TOP
  dj : ab + 1792 * 5 ≤ fl ∨ fl + 224 * 5 ≤ ab
  rc : RC4 + 768 ≤ ab ∧ RC4 + 768 ≤ fl

theorem bufOK_abuf : BufOK ABUF FL := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- One squeeze of a group: glue, `kf4`, glue, `blk b` (`b < 4`). -/
theorem kb_round {s : State} (hs : Ctx s) {tl stk : List UInt256} (htl : tl.length ≤ 8) {m : ByteArray}
    {pc0 r1 r2 c1 c2 b ab fl : Nat} (hb : b < 4) (hbuf : BufOK ab fl)
    (g1 : Reach (callState s pc0 stk m) (callState s 22529 (wd r1 :: tl) m) c1)
    (g2 : ∀ m', Reach (callState s r1 tl m')
      (callState s 9025 (wd (fl + 224 * b) :: wd (ab + 1792 * b) :: wd r2 :: tl) m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m ab fl St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ HBlocks m' ab fl St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ab + 1792 * b, ab + 1792 * b + 1792),
        (fl + 224 * b, fl + 224 * b + 224)] ∧
      Reach (callState s pc0 stk m) (callState s r2 tl m') (c1 + Gas.kf4 + c2 + Gas.blk) := by
  obtain ⟨hab, hab', hfl, hfl', hd, ⟨hrcab, hrcfl⟩⟩ := hbuf
  simp only [KS, TOP, RC4] at hab hab' hfl hfl' hrcab hrcfl
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := tl)
    (retOK_main (by decide) htl hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blk_call hs (ret := r2) (tail := tl)
    (retOK_main (by decide) htl hj2 hr2) m1 (abp := ab + 1792 * b) (flp := fl + 224 * b)
    (by unfold KS; omega) (by unfold TOP; omega) (by unfold KS; omega) (by unfold TOP; omega) (by omega)
  obtain ⟨hA, hF⟩ := hbk _ (sized4_permute hS) hks1
  have ha2 : Avoids [(ab + 1792 * b, ab + 1792 * b + 1792), (fl + 224 * b, fl + 224 * b + 224)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS]; omega
  have hB1 := hB.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true, KS, KB]; omega)
    (by simp only [avoids_cons, avoids_nil, and_true, KS, KB]; omega)
  refine ⟨m2, KS4.frame hks1 hf2 ha2, fun b' hb' => ?_, (hrc.frame hf1 (by avoids_tac)).frame hf2
    (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega), FrameExcept.trans hf1 hf2,
    ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = b
  · subst hbb
    exact ⟨fun i hi _ => by rw [hA i hi]; exact pack4_congr fun k hk => by rw [hSt k hk],
      fun g hg _ => by rw [hF g hg]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · exact (hB1.frame hf2 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true]; omega)) b' (by omega)

/-- The last squeeze of a group: glue, `kf4`, glue, `blkh` (block 4). -/
theorem kbh_round {s : State} (hs : Ctx s) {tl stk : List UInt256} (htl : tl.length ≤ 8) {m : ByteArray}
    {pc0 r1 r2 c1 c2 ab fl : Nat} (hbuf : BufOK ab fl)
    (g1 : Reach (callState s pc0 stk m) (callState s 22529 (wd r1 :: tl) m) c1)
    (g2 : ∀ m', Reach (callState s r1 tl m')
      (callState s 10203 (wd (fl + 224 * 4) :: wd (ab + 1792 * 4) :: wd r2 :: tl) m') c2)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m ab fl St 4)
    (hSt : ∀ k, k < 4 → St 4 k = Keccak.permute (S k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute (S k)) ∧ HBlocks m' ab fl St 5 ∧ RC4Table m' ∧
      FrameExcept m m' [(KS, KS + 800), (KB, KB + 800), (ab + 1792 * 4, ab + 1792 * 4 + 1024),
        (fl + 224 * 4, fl + 224 * 4 + 128)] ∧
      Reach (callState s pc0 stk m) (callState s r2 tl m') (c1 + Gas.kf4 + c2 + Gas.blkh) := by
  obtain ⟨hab, hab', hfl, hfl', hd, ⟨hrcab, hrcfl⟩⟩ := hbuf
  simp only [KS, TOP, RC4] at hab hab' hfl hfl' hrcab hrcfl
  obtain ⟨m1, hk, hf1, hc1⟩ := kf4_call hs (ret := r1) (tail := tl)
    (retOK_main (by decide) htl hj1 hr1) m hrc
  have hks1 := hk S hS hks
  obtain ⟨m2, hbk, hf2, hc2⟩ := blkh_call hs (ret := r2) (tail := tl)
    (retOK_main (by decide) htl hj2 hr2) m1 (abp := ab + 1792 * 4) (flp := fl + 224 * 4)
    (by unfold KS; omega) (by unfold TOP; omega) (by unfold KS; omega) (by unfold TOP; omega) (by omega)
  obtain ⟨hA, hF⟩ := hbk _ (sized4_permute hS) hks1
  have ha2 : Avoids [(ab + 1792 * 4, ab + 1792 * 4 + 1024), (fl + 224 * 4, fl + 224 * 4 + 128)]
      KS (KS + 800) := by simp only [avoids_cons, avoids_nil, and_true, KS]; omega
  have hB1 := hB.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true, KS, KB]; omega)
    (by simp only [avoids_cons, avoids_nil, and_true, KS, KB]; omega)
  refine ⟨m2, KS4.frame hks1 hf2 ha2, fun b' hb' => ?_, (hrc.frame hf1 (by avoids_tac)).frame hf2
    (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega), FrameExcept.trans hf1 hf2,
    ((g1.trans hc1).trans (g2 m1)).trans hc2⟩
  by_cases hbb : b' = 4
  · subst hbb
    exact ⟨fun i _ hh => by rw [hA i (by omega)]; exact pack4_congr fun k hk => by rw [hSt k hk],
      fun g _ hh => by rw [hF g (by omega)]; exact flagWord_congr (fun k hk => by rw [hSt k hk]) g⟩
  · exact (hB1.frame hf2 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true]; omega)) b' (by omega)

/-! ## `trabs` on the `tr` slot -/

theorem lmL_top1 : ∀ k, k < 4 →
    lane 0xffffffffffffffff000000000000000000000000000000000000000000000000 k = 0 ∨
      lane 0xffffffffffffffff000000000000000000000000000000000000000000000000 k = M64 := by
  decide

theorem lmL_top3 : ∀ k, k < 4 →
    lane 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 k = 0 ∨
      lane 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 k = M64 := by
  decide

/-- `trabs`'s post with `kp = 0`, normalised. -/
theorem trabs_norm {m m' : ByteArray} {cd : ByteArray} {off lm n4 sh : Nat}
    (hpost : ∀ x, x < 25 → word m' (KS + 32 * x) =
      if 0 ≤ KS + 32 * x ∧ KS + 32 * x < 0 + 128 * n4 then
        word m (KS + 32 * x) ^^^ spread (trLane cd off lm n4 ((KS + 32 * x - 0) / 32)) * 2 ^ sh
      else word m (KS + 32 * x)) :
    ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * n4 then trLane cd off lm n4 x else 0) * 2 ^ sh := by
  intro x hx
  rw [hpost x hx]
  by_cases h : x < 4 * n4
  · rw [if_pos (by unfold KS; omega), if_pos h, show (KS + 32 * x - 0) / 32 = x by unfold KS; omega]
  · rw [if_neg (by unfold KS; omega), if_neg h, spread_zero, Nat.zero_mul, Nat.xor_zero]

theorem trLane_lt' (cd : ByteArray) (off lm n4 u : Nat) : trLane cd off lm n4 u < 2 ^ 64 := by
  unfold trLane; exact Nat.mod_lt _ (by norm_num)

/-- `S` with slot `sh` replaced by `T`. -/
def upd (S : Nat → Fips202.SpongeState) (sh : Nat) (T : Fips202.SpongeState) : Nat → Fips202.SpongeState :=
  fun k => if k = sh then T else S k

theorem upd_sized {S : Nat → Fips202.SpongeState} (hS : Sized4 S) {sh : Nat} {T : Fips202.SpongeState}
    (hT : T.size = 25) : Sized4 (upd S sh T) := fun k hk => by
  unfold upd; split
  · exact hT
  · exact hS k hk

/-- A full block `j < 9` of the padded public key, absorbed into slot `sh`. -/
theorem ks4_trabs_full {m m' : ByteArray} {cd : ByteArray} (hcd : 1312 ≤ cd.size)
    {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S) {sh j : Nat} (hsh : sh < 4) (hj : j < 9)
    (hw : ∀ x, x < 25 → word m' (KS + 32 * x) =
      word m (KS + 32 * x) ^^^ spread (if x < 4 * 5 then
        trLane cd (136 * j) 0xffffffffffffffff000000000000000000000000000000000000000000000000 5 x
        else 0) * 2 ^ sh) :
    KS4 m' (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf cd)) (j * 136) (S sh))) := by
  refine ks4_xor_slot hsh hks _ (fun x _ => by
    split
    · exact trLane_lt' _ _ _ _ _
    · norm_num) hw _ ?_
  intro x hx
  rw [laneOf_xorBlock _ _ (hS sh hsh) (by norm_num)]
  by_cases h17 : x < 17
  · rw [if_pos (by norm_num; omega), if_pos (by omega), trLane_eq cd lm_top1,
      if_neg (by omega), le64_padPk_full hcd (by omega), Nat.mul_comm j]
  · rw [if_neg (by norm_num; omega)]
    by_cases h20 : x < 20
    · rw [if_pos (by omega), trLane_eq cd lm_top1, if_pos (by omega), Nat.xor_zero]
    · rw [if_neg (by omega), Nat.xor_zero]

/-- One absorbing squeeze of the `tr` slot `sh`: glue, `trabs` (full block `j`),
glue, `kf4`, glue, `blk b`. -/
theorem absorb_round {s : State} (hs : Ctx s) (hcd : 1312 ≤ s.executionEnv.calldata.size)
    {tl : List UInt256} (htl : tl.length ≤ 8) {m : ByteArray}
    {pc0 r0 r1 r2 c0 c1 c2 b j off sh ab fl : Nat} (hb : b < 4) (hj : j < 9) (hsh : sh < 4)
    (hoff : off = 136 * j) (hbuf : BufOK ab fl)
    (g0 : Reach (callState s pc0 tl m) (callState s 11702
      (wd 0 :: wd 0xffffffffffffffff000000000000000000000000000000000000000000000000 :: wd 5 :: wd sh ::
        wd off :: wd r0 :: tl) m) c0)
    (g1 : ∀ m', Reach (callState s r0 tl m') (callState s 22529 (wd r1 :: tl) m') c1)
    (g2 : ∀ m', Reach (callState s r1 tl m')
      (callState s 9025 (wd (fl + 224 * b) :: wd (ab + 1792 * b) :: wd r2 :: tl) m') c2)
    (hj0 : Decode.isValidJumpDest optBytecode r0 = true) (hr0 : r0 < 2 ^ 16)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m ab fl St b)
    (hSt : ∀ k, k < 4 → St b k = Keccak.permute
      (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh)) k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute
        (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh)) k)) ∧
      HBlocks m' ab fl St (b + 1) ∧ RC4Table m' ∧
      FrameExcept m m' ([(0, 0 + 128 * 5)] ++ [(KS, KS + 800), (KB, KB + 800),
        (ab + 1792 * b, ab + 1792 * b + 1792), (fl + 224 * b, fl + 224 * b + 224)]) ∧
      Reach (callState s pc0 tl m) (callState s r2 tl m')
        (c0 + Gas.trabs 5 + (c1 + Gas.kf4 + c2 + Gas.blk)) := by
  obtain ⟨m1, hw, hf1, hc1⟩ := trabs_call hs (ret := r0) (tail := tl)
    (retOK_main (by decide) htl hj0 hr0) m (off := off) (sh := sh) (n4 := 5)
    (lm := 0xffffffffffffffff000000000000000000000000000000000000000000000000) (kp := 0)
    (by subst hoff; omega) hsh (by norm_num) (by norm_num) lmL_top1 (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have hks1 := ks4_trabs_full hcd hS hks hsh hj (by subst hoff; exact trabs_norm hw)
  have hS1 := upd_sized hS (sh := sh)
    (T := Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh))
    (by rw [xorBlock_size]; exact hS sh hsh)
  have hab := hbuf.lo1; have hfl := hbuf.lo2
  simp only [KS] at hab hfl
  obtain ⟨m2, hks2, hB2, hrc2, hf2, hc2⟩ := kb_round hs htl hb hbuf (g1 m1) g2 hj1 hr1 hj2 hr2
    (hrc.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega)) hS1 hks1
    (hB.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true]; omega)) hSt
  exact ⟨m2, hks2, hB2, hrc2, FrameExcept.trans hf1 hf2, (g0.trans hc1).trans hc2⟩

/-- `absorb_round` with `blkh` (block 4). -/
theorem absorb_round_h {s : State} (hs : Ctx s) (hcd : 1312 ≤ s.executionEnv.calldata.size)
    {tl : List UInt256} (htl : tl.length ≤ 8) {m : ByteArray}
    {pc0 r0 r1 r2 c0 c1 c2 j off sh ab fl : Nat} (hj : j < 9) (hsh : sh < 4)
    (hoff : off = 136 * j) (hbuf : BufOK ab fl)
    (g0 : Reach (callState s pc0 tl m) (callState s 11702
      (wd 0 :: wd 0xffffffffffffffff000000000000000000000000000000000000000000000000 :: wd 5 :: wd sh ::
        wd off :: wd r0 :: tl) m) c0)
    (g1 : ∀ m', Reach (callState s r0 tl m') (callState s 22529 (wd r1 :: tl) m') c1)
    (g2 : ∀ m', Reach (callState s r1 tl m')
      (callState s 10203 (wd (fl + 224 * 4) :: wd (ab + 1792 * 4) :: wd r2 :: tl) m') c2)
    (hj0 : Decode.isValidJumpDest optBytecode r0 = true) (hr0 : r0 < 2 ^ 16)
    (hj1 : Decode.isValidJumpDest optBytecode r1 = true) (hr1 : r1 < 2 ^ 16)
    (hj2 : Decode.isValidJumpDest optBytecode r2 = true) (hr2 : r2 < 2 ^ 16)
    (hrc : RC4Table m) {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    {St : Nat → Nat → Fips202.SpongeState} (hB : HBlocks m ab fl St 4)
    (hSt : ∀ k, k < 4 → St 4 k = Keccak.permute
      (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh)) k)) :
    ∃ m', KS4 m' (fun k => Keccak.permute
        (upd S sh (Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh)) k)) ∧
      HBlocks m' ab fl St 5 ∧ RC4Table m' ∧
      FrameExcept m m' ([(0, 0 + 128 * 5)] ++ [(KS, KS + 800), (KB, KB + 800),
        (ab + 1792 * 4, ab + 1792 * 4 + 1024), (fl + 224 * 4, fl + 224 * 4 + 128)]) ∧
      Reach (callState s pc0 tl m) (callState s r2 tl m')
        (c0 + Gas.trabs 5 + (c1 + Gas.kf4 + c2 + Gas.blkh)) := by
  obtain ⟨m1, hw, hf1, hc1⟩ := trabs_call hs (ret := r0) (tail := tl)
    (retOK_main (by decide) htl hj0 hr0) m (off := off) (sh := sh) (n4 := 5)
    (lm := 0xffffffffffffffff000000000000000000000000000000000000000000000000) (kp := 0)
    (by subst hoff; omega) hsh (by norm_num) (by norm_num) lmL_top1 (by unfold KS; norm_num)
    (by unfold KS; norm_num) (by norm_num)
  have hks1 := ks4_trabs_full hcd hS hks hsh hj (by subst hoff; exact trabs_norm hw)
  have hS1 := upd_sized hS (sh := sh)
    (T := Fips202.xorBlock 136 (Fips202.pad 136 0x1F (pkOf s.executionEnv.calldata)) (j * 136) (S sh))
    (by rw [xorBlock_size]; exact hS sh hsh)
  have hab := hbuf.lo1; have hfl := hbuf.lo2
  simp only [KS] at hab hfl
  obtain ⟨m2, hks2, hB2, hrc2, hf2, hc2⟩ := kbh_round hs htl hbuf (g1 m1) g2 hj1 hr1 hj2 hr2
    (hrc.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true, RC4]; omega)) hS1 hks1
    (hB.frame hf1 (by simp only [avoids_cons, avoids_nil, and_true]; omega)
      (by simp only [avoids_cons, avoids_nil, and_true]; omega)) hSt
  exact ⟨m2, hks2, hB2, hrc2, FrameExcept.trans hf1 hf2, (g0.trans hc1).trans hc2⟩

end MlDsaOpt44.Proofs.Ex
