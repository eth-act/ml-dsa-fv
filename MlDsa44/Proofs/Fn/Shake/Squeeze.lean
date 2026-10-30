import MlDsa44.Proofs.Fn.Shake.Blocks
import MlDsa44.Proofs.Fn.Keccak
import MlDsa44.Proofs.Fn.Lanes
import MlDsa44.Proofs.Math.Shake.Bytes
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The squeeze phase of `shake` (instructions 1803‥1874)

`lanes_loop`: the lane-store loop writes the first `rate` bytes of the lanes
at `o` (plus a 24-byte overhang). `squeeze_phase`: the block loop writes
`Fips202.squeeze rate S blocks` at `out` and returns.
-/

namespace MlDsa44.Proofs.Shake

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto

theorem stack_shake : Stack.shake = 256 := by decide

theorem rate_div8 {rate : Nat} (hrate : rate = 136 ∨ rate = 168) : rate / 8 * 8 = rate := by
  rcases hrate with rfl | rfl <;> rfl

/-- The lane-store loop of one output block at `o`. -/
theorem lanes_loop {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {rate ptr len out blocks last rem full b o : Nat}
    (hrate : rate = 136 ∨ rate = 168) {M : ByteArray} {L : Array UInt64}
    (hL : LanesAt M ST L) (hrc : RCTable M) (ho : ZETA ≤ o)
    (homem : o + rate + 32 ≤ 32 * s.activeWords.toNat) :
    ∃ M', LanesAt M' ST L ∧ RCTable M' ∧ FrameExcept M M' [(o, o + rate + 24)] ∧
      (∀ i, i < rate → byteAt M' (o + i) = lb L[i / 8]! (i % 8)) ∧
      Infra.Reach
        (callState s 2886 (wd 0 :: wd o :: wd b :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (callState s 2856 (wd (b + 1) :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M')
        (rate / 8 * (99 + Gas.storeLE64) + 62) := by
  have htail : tail.length ≤ 768 := by have := hr.depth; rw [stack_shake] at this; omega
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hr8 := rate_div8 hrate
  have hrb : 0 < rate ∧ rate < 256 := by omega
  simp only [ZETA] at ho
  have hloop : ∀ j, j ≤ rate / 8 → ∃ M', LanesAt M' ST L ∧ RCTable M' ∧
      FrameExcept M M' [(o, o + 8 * j + 24)] ∧
      (∀ i, i < 8 * j → byteAt M' (o + i) = lb L[i / 8]! (i % 8)) ∧
      Infra.Reach
        (callState s 2886 (wd 0 :: wd o :: wd b :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (callState s 2886 (wd j :: wd o :: wd b :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M')
        (j * (99 + Gas.storeLE64)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨M, hL, hrc, Infra.FrameExcept.refl _ _, fun i hi => absurd hi (by omega),
        by simpa using Infra.Reach.refl _⟩
    | succ j ih =>
      intro hj
      obtain ⟨M1, hL1, hrc1, hF1, hB1, hR1⟩ := ih (by omega)
      have hw : word M1 (j * 32) = (L[j]!).toNat := by
        have := hL1.2 j (by omega)
        rwa [show ST + 32 * j = j * 32 by simp only [ST]; omega] at this
      have hx : word M1 (j * 32) < 2 ^ 64 := by rw [hw]; exact (L[j]!).toNat_lt
      have h1 := b_lane1 hs htail hfw haw hrb (ptr := ptr) (len := len) (out := out)
        (blocks := blocks) (ret := ret) M1 last rem full b o j (by omega)
      obtain ⟨M2, hB2, hF2, hC2⟩ := storeLE64_call hs
        (hr.callee (B' := Stack.storeLE64) (ret' := 2916)
          (extra := [wd j, wd o, wd b, wd last, wd rem, wd full, wd rate, wd ptr, wd len, wd out,
            wd blocks, wd ret])
          (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) M1 hx
        (by omega : o + j * 8 + 32 ≤ 32 * s.activeWords.toNat)
      have h3 := b_lane2 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
        (blocks := blocks) (ret := ret) M2 last rem full b o j
      have hc := Infra.call_iff.mp hC2
      refine ⟨M2, ?_, ?_, ?_, ?_, ?_⟩
      · exact Infra.LanesAt.frame hL1 hF2 (by
          simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, ST]; omega)
      · exact Infra.RCTable.frame hrc1 hF2 (by
          simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC]; omega)
      · exact frame_cover (Infra.FrameExcept.trans hF1 hF2) (by frame_omega)
      · intro i hi
        by_cases hij : i < 8 * j
        · rw [Infra.FrameExcept.byteAt hF2
            (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega)]
          exact hB1 i hij
        · have hsz : (Keccak.writeLE64 .empty (UInt64.ofNat (word M1 (j * 32))) ++
              ByteArray.mk (Array.replicate 24 0)).size = 32 := by
            rw [ByteArray.size_append, writeLE64_size, ByteArray.size_empty]; rfl
          have := hB2 (i - 8 * j) (by rw [hsz]; omega)
          rw [← byteAt_eq_getElem!, byteAt_append, writeLE64_size, ByteArray.size_empty,
            if_pos (by omega), byteAt_writeLE64, ByteArray.size_empty, if_neg (by omega),
            if_pos (by omega), hw, UInt64.ofNat_toNat, Nat.sub_zero] at this
          rw [show o + i = o + j * 8 + (i - 8 * j) by omega, this,
            show i / 8 = j by omega, show i % 8 = i - 8 * j by omega]
      · exact ((hR1.trans h1).trans ((hc.of_eq (by simp [Entry.storeLE64]) (by simp)).trans
          h3)).mono (Nat.le_of_eq (by ring))
  obtain ⟨M1, hL1, hrc1, hF1, hB1, hR1⟩ := hloop (rate / 8) le_rfl
  have hx := b_laneExit hs htail hrb (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret) M1 last rem full b o
  refine ⟨M1, hL1, hrc1, ?_, fun i hi => hB1 i (by omega), hR1.trans hx⟩
  rwa [show 8 * (rate / 8) = rate by omega] at hF1

/-- Output block `b`: the lane loop at `out + b * rate` appends `stateBytes` of
the current lanes to the bytes already written. -/
theorem squeeze_block {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {rate ptr len out blocks last rem full b : Nat}
    (hrate : rate = 136 ∨ rate = 168) (hb : b < blocks) (hout : ZETA ≤ out)
    (hmem : out + blocks * rate + 32 ≤ 32 * s.activeWords.toNat)
    {S : Fips202.SpongeState} {M : ByteArray}
    (hL : LanesAt M ST (Keccak.permute^[b] S)) (hrc : RCTable M)
    (hB : ∀ i, i < b * rate → byteAt M (out + i) = byteAt (Fips202.squeeze rate S b) i) :
    ∃ M', LanesAt M' ST (Keccak.permute^[b] S) ∧ RCTable M' ∧
      FrameExcept M M' [(out + b * rate, out + b * rate + rate + 24)] ∧
      (∀ i, i < (b + 1) * rate →
        byteAt M' (out + i) = byteAt (Fips202.squeeze rate S (b + 1)) i) ∧
      Infra.Reach
        (callState s 2886 (wd 0 :: wd (out + b * rate) :: wd b :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (callState s 2856 (wd (b + 1) :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M')
        (rate / 8 * (99 + Gas.storeLE64) + 62) := by
  have hr8 := rate_div8 hrate
  have hbr : (b + 1) * rate ≤ blocks * rate := Nat.mul_le_mul_right _ hb
  have hsucc : (b + 1) * rate = b * rate + rate := Nat.succ_mul b rate
  simp only [ZETA] at hout
  obtain ⟨M', hL', hrc', hF, hB', hR⟩ := lanes_loop hs hr (ptr := ptr) (len := len)
    (out := out) (blocks := blocks) (last := last) (rem := rem) (full := full) (b := b)
    (o := out + b * rate) hrate hL hrc (by simp only [ZETA]; omega) (by omega)
  refine ⟨M', hL', hrc', hF, fun i hi => ?_, hR⟩
  rw [squeeze_succ, byteAt_append, Math.squeeze_size_of_rate _ _ _ hrate]
  by_cases h : i < b * rate
  · rw [if_pos h, Infra.FrameExcept.byteAt hF
      (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true]; omega)]
    exact hB i h
  · rw [if_neg h, byteAt_stateBytes, if_pos (by omega),
      show out + i = out + b * rate + (i - b * rate) by omega]
    exact hB' _ (by omega)

/-- The squeeze loop (from `b = 0` at pc 2856) and the return. -/
theorem squeeze_phase {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {rate ptr len out blocks last rem full : Nat}
    (hrate : rate = 136 ∨ rate = 168) (hblocks : 1 ≤ blocks ∧ blocks ≤ 6) (hout : ZETA ≤ out)
    (hmem : out + blocks * rate + 32 ≤ 32 * s.activeWords.toNat)
    {S : Fips202.SpongeState} {M0 : ByteArray} (hL : LanesAt M0 ST S) (hrc : RCTable M0) :
    ∃ M', BytesAt M' out (Fips202.squeeze rate S blocks) ∧
      FrameExcept M0 M' [(ST, RC), (out, out + blocks * rate + 24)] ∧
      Infra.Reach
        (callState s 2856 (wd 0 :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M0)
        (callState s ret tail M')
        (65 + (blocks - 1) * (80 + Gas.keccakF) +
          blocks * (rate / 8 * (99 + Gas.storeLE64) + 62) + 53) := by
  have htail : tail.length ≤ 768 := by have := hr.depth; rw [stack_shake] at this; omega
  have hblk : blocks ≤ 6 := hblocks.2
  have hP : ∀ c, c + 1 ≤ blocks → ∃ M, LanesAt M ST (Keccak.permute^[c] S) ∧ RCTable M ∧
      FrameExcept M0 M [(ST, RC), (out, out + (c + 1) * rate + 24)] ∧
      (∀ i, i < (c + 1) * rate →
        byteAt M (out + i) = byteAt (Fips202.squeeze rate S (c + 1)) i) ∧
      Infra.Reach
        (callState s 2856 (wd 0 :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M0)
        (callState s 2856 (wd (c + 1) :: wd last :: wd rem :: wd full ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (65 + c * (80 + Gas.keccakF) + (c + 1) * (rate / 8 * (99 + Gas.storeLE64) + 62)) := by
    intro c
    induction c with
    | zero =>
      intro hc
      have h0 := b_sq0 hs htail hblk (rate := rate) (ptr := ptr) (len := len) (out := out)
        (ret := ret) M0 last rem full (by omega)
      obtain ⟨M, hL', hrc', hF, hB, hR⟩ := squeeze_block hs hr (ptr := ptr) (len := len)
        (last := last) (rem := rem) (full := full) (b := 0) hrate (by omega) hout hmem
        (S := S) hL hrc (fun i hi => by simp at hi)
      refine ⟨M, hL', hrc', frame_cover hF (by frame_omega), hB, ?_⟩
      exact (h0.trans (hR.of_eq (by simp) rfl)).mono (Nat.le_of_eq (by ring))
    | succ c ih =>
      intro hc
      obtain ⟨M, hL1, hrc1, hF1, hB1, hR1⟩ := ih (by omega)
      have h1 := b_sq1 hs htail hblk (rate := rate) (ptr := ptr) (len := len) (out := out)
        (ret := ret) M last rem full (c + 1) (by omega) (by omega)
      obtain ⟨M1, hL2, hF2, hC2⟩ := keccakF_call hs
        (hr.callee (B' := Stack.keccakF) (ret' := 2878)
          (extra := [wd (c + 1), wd last, wd rem, wd full, wd rate, wd ptr, wd len, wd out,
            wd blocks, wd ret])
          (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) hL1 hrc1
      have hrc2 : RCTable M1 := Infra.RCTable.frame hrc1 hF2 (by
        simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)
      have h2 := b_sq2 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
        (blocks := blocks) (ret := ret) M1 last rem full (c + 1)
      have hzo : ZETA ≤ out := hout
      simp only [ZETA] at hzo
      rw [← Function.iterate_succ_apply' Keccak.permute c S] at hL2
      obtain ⟨M2, hL3, hrc3, hF3, hB3, hR3⟩ := squeeze_block hs hr (ptr := ptr) (len := len)
        (last := last) (rem := rem) (full := full) (b := c + 1) hrate (by omega) hout hmem
        (S := S) hL2 hrc2 (fun i hi => by
          rw [Infra.FrameExcept.byteAt hF2
            (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)]
          exact hB1 i hi)
      have hm1 : (c + 1 + 1) * rate = (c + 1) * rate + rate := Nat.succ_mul _ rate
      refine ⟨M2, hL3, hrc3, ?_, hB3, ?_⟩
      · exact frame_cover (Infra.FrameExcept.trans (Infra.FrameExcept.trans hF1 hF2) hF3)
          (by frame_omega)
      · have hc2 := (Infra.call_iff.mp hC2).of_eq (s' := callState s 4 (wd 2878 :: wd (c + 1) ::
            wd last :: wd rem :: wd full :: wd rate :: wd ptr :: wd len :: wd out ::
            wd blocks :: wd ret :: tail) M)
          (t' := callState s 2878 (wd (c + 1) :: wd last :: wd rem :: wd full :: wd rate ::
            wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M1)
          (by simp [Entry.keccakF]) (by simp)
        exact ((hR1.trans h1).trans ((hc2.trans h2).trans hR3)).mono (Nat.le_of_eq (by ring))
  obtain ⟨c, rfl⟩ : ∃ c, blocks = c + 1 := ⟨blocks - 1, by omega⟩
  obtain ⟨M, -, -, hF, hB, hR⟩ := hP c le_rfl
  have hx := b_exit hs htail hblk (rate := rate) (ptr := ptr) (len := len) (out := out)
    M last rem full hr
  refine ⟨M, fun i hi => ?_, hF, (hR.trans hx).mono (Nat.le_of_eq (by simp))⟩
  rw [Math.squeeze_size_of_rate _ _ _ hrate] at hi
  rw [hB i hi, byteAt_eq_getElem!]

end MlDsa44.Proofs.Shake
