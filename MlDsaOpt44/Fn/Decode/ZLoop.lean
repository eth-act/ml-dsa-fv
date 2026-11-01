import MlDsaOpt44.Fn.Decode.ZBlocks
import MlDsaOpt44.Fn.Decode.ZMath
import MlDsaOpt44.Budget
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The loops of `dz` (WP8)

`ZInvM cd m₀ M T`: the words `ZH + 32 t` for `t < T` hold the lanes
`zLane cd · t`, and `M` differs from `m₀` only inside `ZH`. `ZInvA cd acc T`:
the accumulated flag word has no `zBitsN` bit iff every coefficient below `T`
passes the norm check. A gather step adds three coefficients, a chunk twelve
(the last chunk is clamped back to `244` and re-checks `244 … 251`).
-/

namespace MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

local notation "MBL" => (1645498280219470655563407987279682868948834857825835856559341567 : Nat)

/-- All four norm checks of coefficient `t`. -/
def zok (cd : ByteArray) (t : Nat) : Prop :=
  ∀ k, k < 4 → 78 < rawZ cd k t ∧ rawZ cd k t < 262066

def ZInvM (cd m₀ M : ByteArray) (T : Nat) : Prop :=
  FrameExcept m₀ M [(ZH, ZH + 8192)] ∧
    ∀ t, t < T → word M (ZH + 32 * t) = pack4 (fun k => zLane cd k t)

def ZInvA (cd : ByteArray) (acc T : Nat) : Prop :=
  acc < 2 ^ 256 ∧ (acc &&& zBitsN = 0 ↔ ∀ t, t < T → zok cd t)

theorem pack4_congr {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : pack4 a = pack4 b := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- The raw word of step `kk` of gather `g` in the chunk at coefficient `4 u`. -/
theorem raw_pack {cd : ByteArray} (hcd : HDR ≤ cd.size) {u g kk off : Nat} (hoff : off = Z0 + 9 * u)
    (hg : g ≤ 3) (hkk : kk ≤ 2) (ht : 4 * u + 3 * g + kk < 256) :
    zR (gW (54 * g) (leNat cd off 32) (leNat cd (576 + off) 32)
        (leNat cd (1152 + off) 32) (leNat cd (1728 + off) 32) / 2 ^ (18 * kk)) =
      pack4 (fun k => rawZ cd k (4 * u + 3 * g + kk)) := by
  have h := zR_gW (fun k => leNat cd (576 * k + off) 32) (54 * g) kk hkk
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at h
  rw [h]
  refine pack4_congr fun k hk => ?_
  rw [show 576 * k + off = Z0 + 9 * u + 576 * k by omega]
  exact le_rawZ hcd hg hkk hk (by omega)

theorem zLane_eq (cd : ByteArray) (k t : Nat) : zLane cd k t = 8511489 - rawZ cd k t := by
  unfold zLane; rw [show (Fips204.q : Nat) = 8380417 from rfl]; norm_num

theorem zv_raw (cd : ByteArray) (t : Nat) :
    zv (pack4 (fun k => rawZ cd k t)) = pack4 (fun k => zLane cd k t) := by
  rw [zv_pack (fun k _ => rawZ_lt cd k t)]
  exact pack4_congr fun k _ => (zLane_eq cd k t).symm

theorem zLane_lt' (cd : ByteArray) (k t : Nat) : zLane cd k t < 2 ^ 64 := by
  unfold zLane; rw [show (Fips204.q : Nat) = 8380417 from rfl]; omega

theorem zf_raw (cd : ByteArray) (t : Nat) :
    zf (pack4 (fun k => rawZ cd k t)) &&& zBitsN = 0 ↔ zok cd t :=
  zf_and (fun k _ => rawZ_lt cd k t)

/-! ## One gather step -/

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem z_gstep (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m₀ M : ByteArray} {u g T acc dp off gp gs e : Nat} (hg : g ≤ 3) (hu : 4 * u + 12 ≤ 256)
    (hdp : dp = ZH + 128 * u) (hoff : off = Z0 + 9 * u) (hgp : gp = dp + 96 * g)
    (hgs : gs = 54 * g)
    (hM : ZInvM s.executionEnv.calldata m₀ M (max T (4 * u + 3 * g)))
    (hA : ZInvA s.executionEnv.calldata acc (max T (4 * u + 3 * g))) :
    ∃ M' acc', ZInvM s.executionEnv.calldata m₀ M' (max T (4 * u + 3 * g + 3)) ∧
      ZInvA s.executionEnv.calldata acc' (max T (4 * u + 3 * g + 3)) ∧
      Reach (callState s 8440 (wd gp :: wd gs :: wd (leNat s.executionEnv.calldata (1728 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1152 + off) 32) ::
          wd (leNat s.executionEnv.calldata (576 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s 8824 (wd (96 + gp) :: wd (54 + gs) :: wd (leNat s.executionEnv.calldata (1728 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1152 + off) 32) ::
          wd (leNat s.executionEnv.calldata (576 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') 307 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hgp96 : gp + 96 ≤ ZH + 8192 := by simp only [ZH] at hdp ⊢; omega
  have hmem : gp + 96 ≤ 32 * s.activeWords.toNat := by simp only [ZH] at hgp96; omega
  generalize hcdv : s.executionEnv.calldata = cd at hM hA hcd ⊢
  have hV : ∀ a, leNat cd a 32 < 2 ^ 256 := fun a => leNat_lt cd a 32
  set W := gW gs (leNat cd off 32) (leNat cd (576 + off) 32) (leNat cd (1152 + off) 32)
    (leNat cd (1728 + off) 32) with hW
  have hWlt : W < 2 ^ 256 := by
    rw [hW, ← gW_mod]; exact Nat.mod_lt _ (by norm_num)
  have h1 := z_g1 (ret := ret) (tail := tail) hs htl M (gp := gp) (gs := gs) (dp := dp) (off := off) (acc := acc)
    (e := e) (by omega) (hV off) (hV (576 + off)) (hV (1152 + off)) (hV (1728 + off))
  have h2 := z_g2 hs M (W := W) (gp := gp) (x1 := gs) (x2 := leNat cd (1728 + off) 32)
    (x3 := leNat cd (1152 + off) 32) (x4 := leNat cd (576 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) haw (by omega)
  have h3 := z_g3 hs (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp) (Lf := zf (zR W)) (W := W) (gp := gp) (x1 := gs) (x2 := leNat cd (1728 + off) 32)
    (x3 := leNat cd (1152 + off) 32) (x4 := leNat cd (576 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) hWlt haw
    (by omega)
  have h4 := z_g4 hs (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)
    (Data.Bytes.natToBytesPadded (zv (zR (W / 262144))) 32) (32 + gp)) (Lf := zf (zR (W / 262144)) ||| zf (zR W)) (W := W) (gp := gp) (x1 := gs)
    (x2 := leNat cd (1728 + off) 32)
    (x3 := leNat cd (1152 + off) 32) (x4 := leNat cd (576 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) hWlt haw
    (by omega)
  have h5 := z_g5 (ret := ret) (tail := tail) hs htl (MachineState.writeBytes (MachineState.writeBytes
    (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)
    (Data.Bytes.natToBytesPadded (zv (zR (W / 262144))) 32) (32 + gp))
    (Data.Bytes.natToBytesPadded (zv (zR (W / 68719476736))) 32) (64 + gp))
    (Lf := zf (zR (W / 68719476736)) ||| (zf (zR (W / 262144)) ||| zf (zR W))) (W := W) (gp := gp)
    (gs := gs) (V0 := leNat cd off 32) (V1 := leNat cd (576 + off) 32) (V2 := leNat cd (1152 + off) 32)
    (V3 := leNat cd (1728 + off) 32) (dp := dp) (off := off) (acc := acc) (e := e)
  refine ⟨_, _, ?_, ?_, ((h1.trans (h2.trans (h3.trans (h4.trans h5)))).mono (by norm_num))⟩
  · -- memory
    clear_value W
    have hR : ∀ kk, kk ≤ 2 → zR (W / 2 ^ (18 * kk)) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + kk)) := by
      intro kk hkk
      rw [hW, hgs]
      exact raw_pack hcd hoff hg hkk (by omega)
    have hR0 : zR W = pack4 (fun k => rawZ cd k (4 * u + 3 * g)) := by simpa using hR 0 (by omega)
    have hR1 : zR (W / 262144) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 1)) := by
      simpa using hR 1 (by omega)
    have hR2 : zR (W / 68719476736) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 2)) := by
      simpa using hR 2 (by omega)
    rw [hR0, hR1, hR2, zv_raw, zv_raw, zv_raw]
    obtain ⟨hfr, hw⟩ := hM
    have hlt : ∀ t, pack4 (fun k => zLane cd k t) < 2 ^ 256 := fun t =>
      pack4_lt' fun k _ => (zLane_lt' cd k t)
    refine ⟨?_, fun t ht => ?_⟩
    · refine FrameExcept.mono (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hfr
        (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) ?_
      intro r hr
      refine ⟨(ZH, ZH + 8192), by simp, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [ZH] at hgp96 hdp ⊢ <;> omega
    · have hgpt : gp = ZH + 32 * (4 * u + 3 * g) := by omega
      by_cases h2 : t = 4 * u + 3 * g + 2
      · subst h2
        rw [show ZH + 32 * (4 * u + 3 * g + 2) = 64 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h1 : t = 4 * u + 3 * g + 1
      · subst h1
        rw [show ZH + 32 * (4 * u + 3 * g + 1) = 32 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h0 : t = 4 * u + 3 * g
      · subst h0
        rw [show ZH + 32 * (4 * u + 3 * g) = gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      exact hw t (by omega)
  · -- accumulator
    clear_value W
    have hR : ∀ kk, kk ≤ 2 → zR (W / 2 ^ (18 * kk)) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + kk)) := by
      intro kk hkk
      rw [hW, hgs]
      exact raw_pack hcd hoff hg hkk (by omega)
    have hR0 : zR W = pack4 (fun k => rawZ cd k (4 * u + 3 * g)) := by simpa using hR 0 (by omega)
    have hR1 : zR (W / 262144) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 1)) := by
      simpa using hR 1 (by omega)
    have hR2 : zR (W / 68719476736) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 2)) := by
      simpa using hR 2 (by omega)
    obtain ⟨hlt, hiff⟩ := hA
    refine ⟨Nat.or_lt_two_pow hlt (Nat.or_lt_two_pow (zf_zR_lt _)
      (Nat.or_lt_two_pow (zf_zR_lt _) (zf_zR_lt _))), ?_⟩
    rw [hR0, hR1, hR2, or_and_eq_zero, or_and_eq_zero, or_and_eq_zero, hiff, zf_raw, zf_raw, zf_raw]
    constructor
    · rintro ⟨ha, h2, h1, h0⟩ t ht
      by_cases e2 : t = 4 * u + 3 * g + 2
      · subst e2; exact h2
      by_cases e1 : t = 4 * u + 3 * g + 1
      · subst e1; exact h1
      by_cases e0 : t = 4 * u + 3 * g
      · subst e0; exact h0
      exact ha t (by omega)
    · intro h
      exact ⟨fun t ht => h t (by omega), h _ (by omega), h _ (by omega), h _ (by omega)⟩

/-! ## One chunk: four loads, four gather steps -/

theorem z_chunk (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {m₀ M : ByteArray} {u T acc dp off e : Nat} (hu : 4 * u + 12 ≤ 256) (hT : 4 * u ≤ T)
    (hdp : dp = ZH + 128 * u) (hoff : off = Z0 + 9 * u)
    (hM : ZInvM s.executionEnv.calldata m₀ M T) (hA : ZInvA s.executionEnv.calldata acc T) :
    ∃ M' acc', ZInvM s.executionEnv.calldata m₀ M' (max T (4 * u + 12)) ∧
      ZInvA s.executionEnv.calldata acc' (max T (4 * u + 12)) ∧
      Reach (callState s 8048 (wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s 8824 (wd (dp + 384) :: wd 216 :: wd (leNat s.executionEnv.calldata (1728 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1152 + off) 32) ::
          wd (leNat s.executionEnv.calldata (576 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') 1986 := by
  have hoff64 : off < 2 ^ 64 := by simp only [Z0] at hoff; omega
  have l0 := z_load0 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e) hoff64
  have l1 := z_load1 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) hoff64
  have l2 := z_load2 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32) hoff64
  have l3 := z_load3 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + off) 32) hoff64
  obtain ⟨M1, a1, hM1, hA1, r1⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hcd (g := 0)
    (gp := dp) (gs := 0) (by omega) hu hdp hoff (by omega) rfl
    (by rwa [show max T (4 * u + 3 * 0) = T by omega]) (by rwa [show max T (4 * u + 3 * 0) = T by omega])
  have n1 := z_gnext (ret := ret) (tail := tail) hs htl M1 (gp := 96 + dp) (gs := 54 + 0)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + off) 32) (V3 := leNat s.executionEnv.calldata (1728 + off) 32)
    (dp := dp) (off := off) (acc := a1) (e := e) (by omega)
  obtain ⟨M2, a2, hM2, hA2, r2⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hcd (g := 1)
    (gp := 96 + dp) (gs := 54 + 0) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega]) (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega])
  have n2 := z_gnext (ret := ret) (tail := tail) hs htl M2 (gp := 96 + (96 + dp)) (gs := 54 + (54 + 0))
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + off) 32) (V3 := leNat s.executionEnv.calldata (1728 + off) 32)
    (dp := dp) (off := off) (acc := a2) (e := e) (by omega)
  obtain ⟨M3, a3, hM3, hA3, r3⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hcd (g := 2)
    (gp := 96 + (96 + dp)) (gs := 54 + (54 + 0)) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega]) (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega])
  have n3 := z_gnext (ret := ret) (tail := tail) hs htl M3 (gp := 96 + (96 + (96 + dp)))
    (gs := 54 + (54 + (54 + 0)))
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + off) 32) (V3 := leNat s.executionEnv.calldata (1728 + off) 32)
    (dp := dp) (off := off) (acc := a3) (e := e) (by omega)
  obtain ⟨M4, a4, hM4, hA4, r4⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hcd (g := 3)
    (gp := 96 + (96 + (96 + dp))) (gs := 54 + (54 + (54 + 0))) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega]) (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega])
  refine ⟨M4, a4, by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega],
    by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega], ?_⟩
  have h := l0.trans (l1.trans (l2.trans (l3.trans (r1.trans (n1.trans (r2.trans (n2.trans
    (r3.trans (n3.trans r4)))))))))
  refine (h.mono (by norm_num)).of_eq rfl ?_
  rw [show 96 + (96 + (96 + (96 + dp))) = dp + 384 by omega,
    show 54 + (54 + (54 + (54 + 0))) = 216 by norm_num]

/-! ## The chunk loop and the whole subroutine -/

theorem z_chunks (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (m : ByteArray) : ∀ j, j ≤ 20 → ∃ M acc, ZInvM s.executionEnv.calldata m M (12 * j) ∧
      ZInvA s.executionEnv.calldata acc (12 * j) ∧
      Reach (callState s 8048 (wd ZH :: wd Z0 :: wd 0 :: wd MBL :: wd (ZH + 7808) :: wd ret :: tail) m)
        (callState s 8048 (wd (ZH + 384 * j) :: wd (Z0 + 27 * j) :: wd acc :: wd MBL :: wd (ZH + 7808) ::
          wd ret :: tail) M) (2097 * j)
  | 0, _ => ⟨m, 0, ⟨FrameExcept.refl _ _, fun t ht => absurd ht (by omega)⟩,
      ⟨by norm_num, by simp⟩, (Reach.refl _).of_eq rfl (by simp)⟩
  | j + 1, hj => by
    obtain ⟨M, acc, hM, hA, r⟩ := z_chunks hs htl hcd m j (by omega)
    obtain ⟨M', acc', hM', hA', c⟩ := z_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
      (u := 3 * j) (dp := ZH + 384 * j) (off := Z0 + 27 * j) (by omega) (by omega) (by omega) (by omega) hM hA
    have x := z_nc (ret := ret) (tail := tail) hs htl M' (gp := ZH + 384 * j + 384)
      (V0 := leNat s.executionEnv.calldata (Z0 + 27 * j) 32)
      (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 27 * j)) 32)
      (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 27 * j)) 32)
      (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 27 * j)) 32)
      (dp := ZH + 384 * j) (off := Z0 + 27 * j) (acc := acc') (e := ZH + 7808)
      (by simp only [ZH]; omega) (by simp only [ZH]; omega)
    refine ⟨M', acc', by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega],
      by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega], ?_⟩
    refine ((r.trans (c.trans x)).mono (by omega)).of_eq rfl ?_
    rw [show 384 + (ZH + 384 * j) = ZH + 384 * (j + 1) by omega,
      show 27 + (Z0 + 27 * j) = Z0 + 27 * (j + 1) by omega]

theorem dz_main (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (m : ByteArray)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', ∃ f, f < 2 ^ 256 ∧ ((f &&& zBitsN = 0) ↔ okZ s.executionEnv.calldata = true) ∧
      (∀ t, t < 256 → word m' (ZH + 32 * t) = pack4 fun k => zLane s.executionEnv.calldata k t) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.dz [wd ZH, wd Z0] ret tail m [wd f] m' Gas.dz := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.dz, Stack.leaf] at this; omega
  have en := z_entry (ret := ret) (tail := tail) hs htl m
  obtain ⟨M, acc, hM, hA, r⟩ := z_chunks (ret := ret) hs htl hcd m 20 le_rfl
  obtain ⟨M', acc', hM', hA', c⟩ := z_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
    (u := 60) (dp := ZH + 384 * 20) (off := Z0 + 27 * 20) (by omega) (by omega) (by omega) (by omega) hM hA
  have x := z_clamp (ret := ret) (tail := tail) hs htl M' (gp := ZH + 384 * 20 + 384)
    (V0 := leNat s.executionEnv.calldata (Z0 + 27 * 20) 32)
    (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 27 * 20)) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 27 * 20)) 32)
    (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 27 * 20)) 32)
    (dp := ZH + 384 * 20) (off := Z0 + 27 * 20) (acc := acc') (e := ZH + 7808)
    (by norm_num [ZH]) (by norm_num [ZH]) (by norm_num [ZH]) (by norm_num [Z0])
  have hx : 384 + (ZH + 384 * 20) - 256 = ZH + 7808 := by norm_num [ZH]
  have hy : 27 + (Z0 + 27 * 20) - 18 = Z0 + 9 * 61 := by norm_num [Z0]
  rw [hx, hy] at x
  obtain ⟨M'', f, hM'', hA'', c'⟩ := z_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
    (u := 61) (dp := ZH + 7808) (off := Z0 + 9 * 61) (by omega) (by omega) (by norm_num [ZH]) rfl
    hM' hA'
  have ex := z_exit (ret := ret) (tail := tail) hs hr htl M'' (gp := ZH + 7808 + 384)
    (V0 := leNat s.executionEnv.calldata (Z0 + 9 * 61) 32)
    (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 9 * 61)) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 9 * 61)) 32)
    (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 9 * 61)) 32)
    (dp := ZH + 7808) (off := Z0 + 9 * 61) (acc := f)
  have hcov : max (max (12 * 20) (4 * 60 + 12)) (4 * 61 + 12) = 256 := by norm_num
  rw [hcov] at hM'' hA''
  obtain ⟨hfr, hw⟩ := hM''
  obtain ⟨hlt, hiff⟩ := hA''
  refine ⟨M'', f, hlt, ?_, hw, hfr, ?_⟩
  · rw [hiff, okZ_iff hcd]
    exact ⟨fun h k hk t ht => h t ht k hk, fun h t ht k hk => h k hk t ht⟩
  · rw [call_iff, Entry.dz, Gas.dz]
    exact ((en.trans (r.trans (c.trans (x.trans (c'.trans ex))))).mono (by norm_num)).of_eq
      (by simp) (by simp)

end

end MlDsaOpt44.Proofs.DecodeZ
