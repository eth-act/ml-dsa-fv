import MlDsaOpt87.Fn.Decode.ZBlocks
import MlDsaOpt87.Fn.Decode.ZMath
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The loops of `dz` (ML-DSA-87, WP G2)

Generalisation of `MlDsaOpt44/Fn/Decode/ZLoop.lean` to 20-bit fields and to the
row group `G < 2` (base `[ZH + 0x2000 G, Z0 + 2560 G]`, lanes `k` = polynomials
`4 G + k`). `ZInvM cd G m₀ M T`: the words below `T` hold the lanes `zLane`, and `M`
differs from `m₀` only in the destination block. `ZInvA cd G acc T`: per lane `j`,
the accumulated flag word has no `zFlagBit j` bit iff every field of polynomial
`4 G + j` below `T` passes the norm check.
-/

namespace MlDsaOpt87.Proofs.DecodeZ

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.DecodeZ

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa

local notation "MBL" => (6582011952183088782295924477334101861609978183833731334774194175 : Nat)

/-- The norm check of field `t` of polynomial `p`. -/
def lok (cd : ByteArray) (p t : Nat) : Prop := 120 < rawZ cd p t ∧ rawZ cd p t < 1048456

def ZInvM (cd : ByteArray) (G : Nat) (m₀ M : ByteArray) (T : Nat) : Prop :=
  FrameExcept m₀ M [(ZH + 0x2000 * G, ZH + 0x2000 * G + 8192)] ∧
    ∀ t, t < T → word M (ZH + 0x2000 * G + 32 * t) = pack4 (fun k => zLane cd (4 * G + k) t)

def ZInvA (cd : ByteArray) (G acc T : Nat) : Prop :=
  acc < 2 ^ 256 ∧ ∀ j, j < 4 → (acc &&& zFlagBit j = 0 ↔ ∀ t, t < T → lok cd (4 * G + j) t)

theorem pack4_congr {a b : Nat → Nat} (h : ∀ k, k < 4 → a k = b k) : pack4 a = pack4 b := by
  unfold pack4; rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- The raw word of step `kk` of gather `g` in the chunk at coefficient `4 u`. -/
theorem raw_pack (cd : ByteArray) {G u g kk off : Nat} (hoff : off = Z0 + 2560 * G + 10 * u)
    (hg : g ≤ 3) (hkk : kk ≤ 2) (ht : 4 * u + 3 * g + kk < 256) :
    zR (gW (60 * g) (leNat cd off 32) (leNat cd (640 + off) 32)
        (leNat cd (1280 + off) 32) (leNat cd (1920 + off) 32) / 2 ^ (20 * kk)) =
      pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + kk)) := by
  have h := zR_gW (fun k => leNat cd (640 * k + off) 32) (60 * g) kk hkk
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at h
  rw [h]
  refine pack4_congr fun k hk => ?_
  rw [show 640 * k + off = Z0 + 2560 * G + 10 * u + 640 * k by omega]
  exact le_rawZ cd hg hkk ht

theorem zLane_eq (cd : ByteArray) (k t : Nat) : zLane cd k t = 8904705 - rawZ cd k t := by
  unfold zLane; rw [show (Fips204.q : Nat) = 8380417 from rfl]; norm_num

theorem zv_raw (cd : ByteArray) (G t : Nat) :
    zv (pack4 (fun k => rawZ cd (4 * G + k) t)) = pack4 (fun k => zLane cd (4 * G + k) t) := by
  rw [zv_pack (fun k _ => rawZ_lt cd (4 * G + k) t)]
  exact pack4_congr fun k _ => (zLane_eq cd (4 * G + k) t).symm

theorem zLane_lt' (cd : ByteArray) (k t : Nat) : zLane cd k t < 2 ^ 64 := by
  unfold zLane; rw [show (Fips204.q : Nat) = 8380417 from rfl]; omega

theorem zf_raw (cd : ByteArray) (G t : Nat) {j : Nat} (hj : j < 4) :
    zf (pack4 (fun k => rawZ cd (4 * G + k) t)) &&& zFlagBit j = 0 ↔ lok cd (4 * G + j) t :=
  zf_lane (fun k _ => rawZ_lt cd (4 * G + k) t) hj

/-! ## One gather step -/

section
variable {s : State} {ret : Nat} {tail : List UInt256}

theorem z_gstep (hs : Ctx s) (htl : tail.length ≤ 960) {G : Nat} (hG : G < 2)
    {m₀ M : ByteArray} {u g T acc dp off gp gs e : Nat} (hg : g ≤ 3) (hu : 4 * u + 12 ≤ 256)
    (hdp : dp = ZH + 0x2000 * G + 128 * u) (hoff : off = Z0 + 2560 * G + 10 * u) (hgp : gp = dp + 96 * g)
    (hgs : gs = 60 * g)
    (hM : ZInvM s.executionEnv.calldata G m₀ M (max T (4 * u + 3 * g)))
    (hA : ZInvA s.executionEnv.calldata G acc (max T (4 * u + 3 * g))) :
    ∃ M' acc', ZInvM s.executionEnv.calldata G m₀ M' (max T (4 * u + 3 * g + 3)) ∧
      ZInvA s.executionEnv.calldata G acc' (max T (4 * u + 3 * g + 3)) ∧
      Reach (callState s 10613 (wd gp :: wd gs :: wd (leNat s.executionEnv.calldata (1920 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1280 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s 10929 (wd (96 + gp) :: wd (60 + gs) :: wd (leNat s.executionEnv.calldata (1920 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1280 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') 307 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hgp96 : gp + 96 ≤ ZH + 0x2000 * G + 8192 := by omega
  have hmem : gp + 96 ≤ 32 * s.activeWords.toNat := by simp only [ZH] at hgp96; omega
  generalize hcdv : s.executionEnv.calldata = cd at hM hA ⊢
  have hV : ∀ a, leNat cd a 32 < 2 ^ 256 := fun a => leNat_lt cd a 32
  set W := gW gs (leNat cd off 32) (leNat cd (640 + off) 32) (leNat cd (1280 + off) 32)
    (leNat cd (1920 + off) 32) with hW
  have hWlt : W < 2 ^ 256 := by
    rw [hW, ← gW_mod]; exact Nat.mod_lt _ (by norm_num)
  have h1 := z_g1 (ret := ret) (tail := tail) hs htl M (gp := gp) (gs := gs) (dp := dp) (off := off) (acc := acc)
    (e := e) (by omega) (hV off) (hV (640 + off)) (hV (1280 + off)) (hV (1920 + off))
  have h2 := z_g2 hs M (W := W) (gp := gp) (x1 := gs) (x2 := leNat cd (1920 + off) 32)
    (x3 := leNat cd (1280 + off) 32) (x4 := leNat cd (640 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) haw (by omega)
  have h3 := z_g3 hs (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp) (Lf := zf (zR W)) (W := W) (gp := gp) (x1 := gs) (x2 := leNat cd (1920 + off) 32)
    (x3 := leNat cd (1280 + off) 32) (x4 := leNat cd (640 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) hWlt haw
    (by omega)
  have h4 := z_g4 hs (MachineState.writeBytes (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)
    (Data.Bytes.natToBytesPadded (zv (zR (W / 1048576))) 32) (32 + gp)) (Lf := zf (zR (W / 1048576)) ||| zf (zR W)) (W := W) (gp := gp) (x1 := gs)
    (x2 := leNat cd (1920 + off) 32)
    (x3 := leNat cd (1280 + off) 32) (x4 := leNat cd (640 + off) 32) (x5 := leNat cd off 32)
    (x6 := dp) (x7 := off) (x8 := acc) (rest := wd e :: wd ret :: tail) (by simp; omega) hWlt haw
    (by omega)
  have h5 := z_g5 (ret := ret) (tail := tail) hs htl (MachineState.writeBytes (MachineState.writeBytes
    (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv (zR W)) 32) gp)
    (Data.Bytes.natToBytesPadded (zv (zR (W / 1048576))) 32) (32 + gp))
    (Data.Bytes.natToBytesPadded (zv (zR (W / 1099511627776))) 32) (64 + gp))
    (Lf := zf (zR (W / 1099511627776)) ||| (zf (zR (W / 1048576)) ||| zf (zR W))) (W := W) (gp := gp)
    (gs := gs) (V0 := leNat cd off 32) (V1 := leNat cd (640 + off) 32) (V2 := leNat cd (1280 + off) 32)
    (V3 := leNat cd (1920 + off) 32) (dp := dp) (off := off) (acc := acc) (e := e)
  refine ⟨_, _, ?_, ?_, ((h1.trans (h2.trans (h3.trans (h4.trans h5)))).mono (by norm_num))⟩
  · -- memory
    clear_value W
    have hR : ∀ kk, kk ≤ 2 → zR (W / 2 ^ (20 * kk)) =
        pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + kk)) := by
      intro kk hkk
      rw [hW, hgs]
      exact raw_pack cd hoff hg hkk (by omega)
    have hR0 : zR W = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g)) := by simpa using hR 0 (by omega)
    have hR1 : zR (W / 1048576) = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + 1)) := by
      simpa using hR 1 (by omega)
    have hR2 : zR (W / 1099511627776) = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + 2)) := by
      simpa using hR 2 (by omega)
    rw [hR0, hR1, hR2, zv_raw, zv_raw, zv_raw]
    obtain ⟨hfr, hw⟩ := hM
    have hlt : ∀ t, pack4 (fun k => zLane cd (4 * G + k) t) < 2 ^ 256 := fun t =>
      pack4_lt' fun k _ => (zLane_lt' cd _ t)
    refine ⟨?_, fun t ht => ?_⟩
    · refine FrameExcept.mono (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hfr
        (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) ?_
      intro r hr
      refine ⟨(ZH + 0x2000 * G, ZH + 0x2000 * G + 8192), by simp, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
    · have hgpt : gp = ZH + 0x2000 * G + 32 * (4 * u + 3 * g) := by omega
      by_cases h2 : t = 4 * u + 3 * g + 2
      · subst h2
        rw [show ZH + 0x2000 * G + 32 * (4 * u + 3 * g + 2) = 64 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h1 : t = 4 * u + 3 * g + 1
      · subst h1
        rw [show ZH + 0x2000 * G + 32 * (4 * u + 3 * g + 1) = 32 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h0 : t = 4 * u + 3 * g
      · subst h0
        rw [show ZH + 0x2000 * G + 32 * (4 * u + 3 * g) = gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      exact hw t (by omega)
  · -- accumulator
    clear_value W
    have hR : ∀ kk, kk ≤ 2 → zR (W / 2 ^ (20 * kk)) =
        pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + kk)) := by
      intro kk hkk
      rw [hW, hgs]
      exact raw_pack cd hoff hg hkk (by omega)
    have hR0 : zR W = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g)) := by simpa using hR 0 (by omega)
    have hR1 : zR (W / 1048576) = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + 1)) := by
      simpa using hR 1 (by omega)
    have hR2 : zR (W / 1099511627776) = pack4 (fun k => rawZ cd (4 * G + k) (4 * u + 3 * g + 2)) := by
      simpa using hR 2 (by omega)
    obtain ⟨hlt, hiff⟩ := hA
    refine ⟨Nat.or_lt_two_pow hlt (Nat.or_lt_two_pow (zf_zR_lt _)
      (Nat.or_lt_two_pow (zf_zR_lt _) (zf_zR_lt _))), fun j hj => ?_⟩
    rw [hR0, hR1, hR2, or_and_eq_zero, or_and_eq_zero, or_and_eq_zero, hiff j hj, zf_raw _ _ _ hj,
      zf_raw _ _ _ hj, zf_raw _ _ _ hj]
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

theorem z_chunk (hs : Ctx s) (htl : tail.length ≤ 960) {G : Nat} (hG : G < 2)
    {m₀ M : ByteArray} {u T acc dp off e : Nat} (hu : 4 * u + 12 ≤ 256) (hT : 4 * u ≤ T)
    (hdp : dp = ZH + 0x2000 * G + 128 * u) (hoff : off = Z0 + 2560 * G + 10 * u)
    (hM : ZInvM s.executionEnv.calldata G m₀ M T) (hA : ZInvA s.executionEnv.calldata G acc T) :
    ∃ M' acc', ZInvM s.executionEnv.calldata G m₀ M' (max T (4 * u + 12)) ∧
      ZInvA s.executionEnv.calldata G acc' (max T (4 * u + 12)) ∧
      Reach (callState s 10221 (wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s 10929 (wd (dp + 384) :: wd 240 :: wd (leNat s.executionEnv.calldata (1920 + off) 32) ::
          wd (leNat s.executionEnv.calldata (1280 + off) 32) ::
          wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd (leNat s.executionEnv.calldata off 32) ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') 1986 := by
  have hoff64 : off < 2 ^ 64 := by simp only [Z0] at hoff; omega
  have l0 := z_load0 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e) hoff64
  have l1 := z_load1 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) hoff64
  have l2 := z_load2 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (640 + off) 32) hoff64
  have l3 := z_load3 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (640 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + off) 32) hoff64
  obtain ⟨M1, a1, hM1, hA1, r1⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hG (g := 0)
    (gp := dp) (gs := 0) (by omega) hu hdp hoff (by omega) rfl
    (by rwa [show max T (4 * u + 3 * 0) = T by omega]) (by rwa [show max T (4 * u + 3 * 0) = T by omega])
  have n1 := z_gnext (ret := ret) (tail := tail) hs htl M1 (gp := 96 + dp) (gs := 60 + 0)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (640 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + off) 32) (V3 := leNat s.executionEnv.calldata (1920 + off) 32)
    (dp := dp) (off := off) (acc := a1) (e := e) (by omega)
  obtain ⟨M2, a2, hM2, hA2, r2⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hG (g := 1)
    (gp := 96 + dp) (gs := 60 + 0) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega]) (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega])
  have n2 := z_gnext (ret := ret) (tail := tail) hs htl M2 (gp := 96 + (96 + dp)) (gs := 60 + (60 + 0))
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (640 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + off) 32) (V3 := leNat s.executionEnv.calldata (1920 + off) 32)
    (dp := dp) (off := off) (acc := a2) (e := e) (by omega)
  obtain ⟨M3, a3, hM3, hA3, r3⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hG (g := 2)
    (gp := 96 + (96 + dp)) (gs := 60 + (60 + 0)) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega]) (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega])
  have n3 := z_gnext (ret := ret) (tail := tail) hs htl M3 (gp := 96 + (96 + (96 + dp)))
    (gs := 60 + (60 + (60 + 0)))
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (640 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + off) 32) (V3 := leNat s.executionEnv.calldata (1920 + off) 32)
    (dp := dp) (off := off) (acc := a3) (e := e) (by omega)
  obtain ⟨M4, a4, hM4, hA4, r4⟩ := z_gstep (ret := ret) (tail := tail) (e := e) hs htl hG (g := 3)
    (gp := 96 + (96 + (96 + dp))) (gs := 60 + (60 + (60 + 0))) (by omega) hu hdp hoff (by omega) (by omega)
    (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega]) (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega])
  refine ⟨M4, a4, by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega],
    by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega], ?_⟩
  have h := l0.trans (l1.trans (l2.trans (l3.trans (r1.trans (n1.trans (r2.trans (n2.trans
    (r3.trans (n3.trans r4)))))))))
  refine (h.mono (by norm_num)).of_eq rfl ?_
  rw [show 96 + (96 + (96 + (96 + dp))) = dp + 384 by omega,
    show 60 + (60 + (60 + (60 + 0))) = 240 by norm_num]

/-! ## The chunk loop and the whole subroutine -/

theorem z_chunks (hs : Ctx s) (htl : tail.length ≤ 960) {G : Nat} (hG : G < 2)
    (m : ByteArray) : ∀ j, j ≤ 20 → ∃ M acc, ZInvM s.executionEnv.calldata G m M (12 * j) ∧
      ZInvA s.executionEnv.calldata G acc (12 * j) ∧
      Reach (callState s 10221 (wd (ZH + 0x2000 * G) :: wd (Z0 + 2560 * G) :: wd 0 :: wd MBL ::
          wd (7808 + (ZH + 0x2000 * G)) :: wd ret :: tail) m)
        (callState s 10221 (wd (ZH + 0x2000 * G + 384 * j) :: wd (Z0 + 2560 * G + 30 * j) :: wd acc ::
          wd MBL :: wd (7808 + (ZH + 0x2000 * G)) :: wd ret :: tail) M) (2097 * j)
  | 0, _ => ⟨m, 0, ⟨FrameExcept.refl _ _, fun t ht => absurd ht (by omega)⟩,
      ⟨by norm_num, fun j _ => by simp⟩, (Reach.refl _).of_eq rfl (by simp)⟩
  | j + 1, hj => by
    obtain ⟨M, acc, hM, hA, r⟩ := z_chunks hs htl hG m j (by omega)
    obtain ⟨M', acc', hM', hA', c⟩ := z_chunk (ret := ret) (tail := tail) (e := 7808 + (ZH + 0x2000 * G))
      hs htl hG (u := 3 * j) (dp := ZH + 0x2000 * G + 384 * j) (off := Z0 + 2560 * G + 30 * j)
      (by omega) (by omega) (by omega) (by omega) hM hA
    have x := z_nc (ret := ret) (tail := tail) hs htl M' (gp := ZH + 0x2000 * G + 384 * j + 384)
      (V0 := leNat s.executionEnv.calldata (Z0 + 2560 * G + 30 * j) 32)
      (V1 := leNat s.executionEnv.calldata (640 + (Z0 + 2560 * G + 30 * j)) 32)
      (V2 := leNat s.executionEnv.calldata (1280 + (Z0 + 2560 * G + 30 * j)) 32)
      (V3 := leNat s.executionEnv.calldata (1920 + (Z0 + 2560 * G + 30 * j)) 32)
      (dp := ZH + 0x2000 * G + 384 * j) (off := Z0 + 2560 * G + 30 * j) (acc := acc')
      (e := 7808 + (ZH + 0x2000 * G)) (by omega) (by simp only [ZH]; omega)
    refine ⟨M', acc', by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega],
      by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega], ?_⟩
    refine ((r.trans (c.trans x)).mono (by omega)).of_eq rfl ?_
    rw [show 384 + (ZH + 0x2000 * G + 384 * j) = ZH + 0x2000 * G + 384 * (j + 1) by omega,
      show 30 + (Z0 + 2560 * G + 30 * j) = Z0 + 2560 * G + 30 * (j + 1) by omega]

theorem clamp_off (G : Nat) : 30 + (Z0 + 2560 * G + 30 * 20) - 20 = Z0 + 2560 * G + 10 * 61 := by
  omega

theorem dz_main (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (m : ByteArray) {G : Nat} (hG : G < 2) :
    ∃ m', ∃ f, f < 2 ^ 256 ∧
      (∀ j, j < 4 → ((f &&& zFlagBit j = 0) ↔ zNormOk s.executionEnv.calldata (4 * G + j))) ∧
      (∀ t, t < 256 → word m' (ZH + 0x2000 * G + 32 * t) =
        pack4 fun j => zLane s.executionEnv.calldata (4 * G + j) t) ∧
      FrameExcept m m' [(ZH + 0x2000 * G, ZH + 0x2000 * G + 8192)] ∧
      Call s Entry.dz [wd (ZH + 0x2000 * G), wd (Z0 + 2560 * G)] ret tail m [wd f] m' Gas.dz := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.dz, Stack.leaf] at this; omega
  have en := z_entry (ret := ret) (tail := tail) hs htl m (dp := ZH + 0x2000 * G) (off := Z0 + 2560 * G)
  obtain ⟨M, acc, hM, hA, r⟩ := z_chunks (ret := ret) hs htl hG m 20 le_rfl
  obtain ⟨M', acc', hM', hA', c⟩ := z_chunk (ret := ret) (tail := tail) (e := 7808 + (ZH + 0x2000 * G))
    hs htl hG (u := 60) (dp := ZH + 0x2000 * G + 384 * 20) (off := Z0 + 2560 * G + 30 * 20)
    (by omega) (by omega) (by omega) (by omega) hM hA
  have x := z_clamp (ret := ret) (tail := tail) hs htl M' (gp := ZH + 0x2000 * G + 384 * 20 + 384)
    (V0 := leNat s.executionEnv.calldata (Z0 + 2560 * G + 30 * 20) 32)
    (V1 := leNat s.executionEnv.calldata (640 + (Z0 + 2560 * G + 30 * 20)) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + (Z0 + 2560 * G + 30 * 20)) 32)
    (V3 := leNat s.executionEnv.calldata (1920 + (Z0 + 2560 * G + 30 * 20)) 32)
    (dp := ZH + 0x2000 * G + 384 * 20) (off := Z0 + 2560 * G + 30 * 20) (acc := acc')
    (e := 7808 + (ZH + 0x2000 * G))
    (by omega) (by omega) (by simp only [ZH]; omega) (by simp only [Z0]; omega)
  have hx : 384 + (ZH + 0x2000 * G + 384 * 20) - 256 = 7808 + (ZH + 0x2000 * G) := by omega
  have hy : 30 + (Z0 + 2560 * G + 30 * 20) - 20 = Z0 + 2560 * G + 10 * 61 := clamp_off G
  rw [hx, hy] at x
  obtain ⟨M'', f, hM'', hA'', c'⟩ := z_chunk (ret := ret) (tail := tail) (e := 7808 + (ZH + 0x2000 * G))
    hs htl hG (u := 61) (dp := 7808 + (ZH + 0x2000 * G)) (off := Z0 + 2560 * G + 10 * 61)
    (by omega) (by omega) (by omega) rfl hM' hA'
  have ex := z_exit (ret := ret) (tail := tail) hs hr htl M'' (gp := 7808 + (ZH + 0x2000 * G) + 384)
    (V0 := leNat s.executionEnv.calldata (Z0 + 2560 * G + 10 * 61) 32)
    (V1 := leNat s.executionEnv.calldata (640 + (Z0 + 2560 * G + 10 * 61)) 32)
    (V2 := leNat s.executionEnv.calldata (1280 + (Z0 + 2560 * G + 10 * 61)) 32)
    (V3 := leNat s.executionEnv.calldata (1920 + (Z0 + 2560 * G + 10 * 61)) 32)
    (dp := 7808 + (ZH + 0x2000 * G)) (off := Z0 + 2560 * G + 10 * 61) (acc := f)
  have hcov : max (max (12 * 20) (4 * 60 + 12)) (4 * 61 + 12) = 256 := by norm_num
  rw [hcov] at hM'' hA''
  obtain ⟨hfr, hw⟩ := hM''
  obtain ⟨hlt, hiff⟩ := hA''
  refine ⟨M'', f, hlt, fun j hj => ?_, hw, hfr, ?_⟩
  · rw [hiff j hj]
    unfold zNormOk lok
    rfl
  · rw [call_iff, Entry.dz, Gas.dz]
    exact ((en.trans (r.trans (c.trans (x.trans (c'.trans ex))))).mono (by norm_num)).of_eq
      (by simp) (by simp)

end

end MlDsaOpt87.Proofs.DecodeZ
