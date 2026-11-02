import MlDsaOpt87.Fn.Fix.Top
import MlDsaOpt87.Fn.Fix.GBlocks
import MlDsaOpt44.Fn.Fix.Defs
import MlDsaOpt87.Layout
import MlDsaOpt87.Budget
/- Ported from `MlDsaOpt44/Fn/Fix.lean` by `scripts/proofgen_port.py 87` --sub 65280=90880 --sub 66080=91680; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
-- port: pcs in `gst`/`G`/`cst`/`(pc := _)`/`(ret := _)`/`(rT := _)`/`(rF := _)` and the `reach_mcopy` index relocated by hand (`proofgen_port.maps 87`)
set_option linter.unusedSimpArgs false
/-!
# RejNTTPoly fix-ups: `fix`, `gfix` (WP5)

After the five squeezes of a SIMD group, `ABUF` holds (lane = slot) the first
256 positional candidates of every slot and `FL` one rejection-flag word per 8
candidates (blocks 0 … 3, and the head of block 4 by `blkh`). `gfix` ORs the
first 32 flag words; before the first fix-up of the group it makes the tail
of block 4 (`blkt`: candidates 256 … 279, flag words 32 … 34) from the kf4
state, so every slot to be fixed is `Pending`. A slot with a rejection among
its first 256 candidates is compacted in place by `fix` (branch-free flagged
groups, masked word copies for clean ones); the sixth squeeze is made on
demand, saving and restoring the kf4 state through `BK` (`MCOPY`), and
recorded in `HAVE6`.

Notation: slot `s` of the group started from the absorbed state `I s`
(before the first permutation); its block `b` is `permN (b + 1) (I s)`, its
candidate `t < 336` is `candI (I s) t`, and its RejNTTPoly result over the
1008-byte stream is `aI (I s)` (`= rejNTTPoly seed` when `I s` is the padded
seed, `Math/Sponge.lean`).
-/

namespace MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

namespace FixAux

open MlDsaOpt44.Proofs  -- port: the 44 `FixAux` namespace is not imported

/-! ## Proof of `fix_call` -/

theorem SlotBlocks.transport {m m' : ByteArray} {s : Nat} {I : Fips202.SpongeState} {nb : Nat}
    (hl : ∀ t, t < 56 * nb → lane (word m' (ABUF + 32 * t)) s = lane (word m (ABUF + 32 * t)) s)
    (hf : ∀ g, g < 7 * nb → word m' (FL + 32 * g) = word m (FL + 32 * g))
    (h : SlotBlocks m s I nb) : SlotBlocks m' s I nb :=
  ⟨fun t ht => (hl t ht).trans (h.1 t ht), fun g hg => by rw [hf g hg]; exact h.2 g hg⟩

theorem SlotBlocks.mono {m : ByteArray} {s : Nat} {I : Fips202.SpongeState} {nb nb' : Nat}
    (hn : nb ≤ nb') (h : SlotBlocks m s I nb') : SlotBlocks m s I nb :=
  ⟨fun t ht => h.1 t (by omega), fun g hg => h.2 g (by omega)⟩

theorem permN_six (I : Fips202.SpongeState) :
    permN 6 I = EvmSemantics.Crypto.Keccak.permute (permN 5 I) := by
  unfold permN; rw [Function.iterate_succ_apply']

theorem candI_hi (I : Fips202.SpongeState) {t : Nat} (h1 : 280 ≤ t) (h2 : t < 336) :
    candI I t = cand (EvmSemantics.Crypto.Keccak.permute (permN 5 I)) (t - 280) := by
  unfold candI; rw [show t / 56 + 1 = 6 by omega, show t % 56 = t - 280 by omega, permN_six]

/-- The squeezed flag words of a slot, as `SlotBlocks` states them. -/
theorem flag_hi (S : Nat → Fips202.SpongeState) {k : Nat} (hk : k < 4) (I : Fips202.SpongeState)
    (hSk : S k = permN 5 I) {g : Nat} (h1 : 35 ≤ g) (h2 : g < 42) :
    flagBit (flagWord (fun k => EvmSemantics.Crypto.Keccak.permute (S k)) (g - 35)) k =
      if ((List.range 8).any fun i => decide (Fips204.q ≤ candI I (8 * g + i))) then 1 else 0 := by
  unfold flagBit
  rw [Fix.flagWord_bit _ _ hk, hSk,
    Fix.any_range_congr (g := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) (fun i hi => by
      rw [candI_hi I (by omega) (by omega), show 8 * g + i - 280 = 8 * (g - 35) + i by omega])]

theorem lane_hi (S : Nat → Fips202.SpongeState) {k : Nat} (hk : k < 4) (I : Fips202.SpongeState)
    (hSk : S k = permN 5 I) {t : Nat} (h1 : 280 ≤ t) (h2 : t < 336) :
    lane (pack4 fun k => cand (EvmSemantics.Crypto.Keccak.permute (S k)) (t - 280)) k = candI I t := by
  rw [Fix.lane_pack4_cand _ _ hk, hSk, candI_hi I h1 h2]

/-- The frame of `fix`. -/
abbrev fixRegions : List (Nat × Nat) :=
  [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)]

/-- Post-state facts other than the result, without the sixth squeeze. -/
theorem post_nosq {m m' : ByteArray} {sl : Nat} (hL : Fix.LaneFrame m m' sl 336)
    {S : Nat → Fips202.SpongeState} (hks : KS4 m S) :
    (∀ sl' I', sl' < 4 → sl' ≠ sl → Pending m S sl' I' → Pending m' S sl' I') ∧
      (∀ sl', sl' < 4 → sl' ≠ sl → ∀ t, t < 280 →
        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      KS4 m' S ∧ word m' HAVE6 = word m HAVE6 ∧ FrameExcept m m' fixRegions := by
  have hFL : ∀ g, word m' (FL + 32 * g) = word m (FL + 32 * g) := fun g =>
    hL.1.word (by simp only [avoids_cons, avoids_nil, and_true, FL]; omega)
  have hH : word m' HAVE6 = word m HAVE6 :=
    hL.1.word (by simp only [avoids_cons, avoids_nil, and_true, HAVE6]; omega)
  have hl : ∀ sl', sl' < 4 → sl' ≠ sl → ∀ t,
      lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl' :=
    fun sl' h1 h2 t => hL.2 t sl' h1 h2
  refine ⟨fun sl' I' h1 h2 hp => ⟨?_, fun h0 => hp.2.1 (hH ▸ h0), fun h0 => ?_⟩,
    fun sl' h1 h2 t _ => hl sl' h1 h2 t, Fix.ks4_frame hks hL.1 (by fx_av), hH, hL.1.mono ?_⟩
  · exact SlotBlocks.transport (fun t _ => hl sl' h1 h2 t) (fun g _ => hFL g) hp.1
  · exact SlotBlocks.transport (fun t _ => hl sl' h1 h2 t) (fun g _ => hFL g) (hp.2.2 (hH ▸ h0))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩

/-- Post-state facts other than the result, with the sixth squeeze. -/
theorem post_sq {m M1 M5 m' : ByteArray} {sl : Nat} (hL1 : Fix.LaneFrame m M1 sl 280)
    (hfr : FrameExcept M1 M5 Fix.sqRegions) (h65 : word M5 4064 = 1)
    {S : Nat → Fips202.SpongeState} (hks : KS4 m S)
    (hW : (∀ i, i < 56 → word M5 (29440 + 32 * i) =
          pack4 fun k => cand (EvmSemantics.Crypto.Keccak.permute (S k)) i) ∧
        (∀ g, g < 7 → word M5 (32352 + 32 * g) =
          flagWord (fun k => EvmSemantics.Crypto.Keccak.permute (S k)) g))
    (hL2 : Fix.LaneFrame M5 m' sl 336) (h6 : word m HAVE6 = 0) :
    (∀ sl' I', sl' < 4 → sl' ≠ sl → Pending m S sl' I' → Pending m' S sl' I') ∧
      (∀ sl', sl' < 4 → sl' ≠ sl → ∀ t, t < 280 →
        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      KS4 m' S ∧ word m' HAVE6 = 1 ∧ FrameExcept m m' fixRegions := by
  have hH : word m' HAVE6 = 1 := by
    rw [hL2.1.word (by simp only [avoids_cons, avoids_nil, and_true, HAVE6]; omega)]; exact h65
  have hlo : ∀ sl', sl' < 4 → sl' ≠ sl → ∀ t, t < 280 →
      lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl' := by
    intro sl' h1 h2 t ht
    show lane (word m' (20480 + 32 * t)) sl' = lane (word m (20480 + 32 * t)) sl'
    rw [hL2.2 t sl' h1 h2,
      hfr.word (by simp only [Fix.sqRegions, avoids_cons, avoids_nil, and_true]; omega)]
    exact hL1.2 t sl' h1 h2
  have hFL : ∀ g, g < 35 → word m' (FL + 32 * g) = word m (FL + 32 * g) := by
    intro g hg
    rw [hL2.1.word (by simp only [avoids_cons, avoids_nil, and_true, FL]; omega),
      hfr.word (by simp only [Fix.sqRegions, avoids_cons, avoids_nil, and_true, FL]; omega),
      hL1.1.word (by simp only [avoids_cons, avoids_nil, and_true, FL]; omega)]
  refine ⟨fun sl' I' h1 h2 hp => ?_, hlo, ?_, hH, ?_⟩
  · have hSk : S sl' = permN 5 I' := hp.2.1 h6
    have h6' : SlotBlocks m' sl' I' 6 := by
      refine ⟨fun t ht => ?_, fun g hg => ?_⟩
      · by_cases hlt : t < 280
        · rw [hlo sl' h1 h2 t hlt]; exact hp.1.1 t (by omega)
        · show lane (word m' (20480 + 32 * t)) sl' = _
          rw [hL2.2 t sl' h1 h2, show 20480 + 32 * t = 29440 + 32 * (t - 280) by omega,
            hW.1 (t - 280) (by omega)]
          exact lane_hi S h1 I' hSk (by omega) (by omega)
      · by_cases hlt : g < 35
        · rw [hFL g hlt]; exact hp.1.2 g (by omega)
        · rw [hL2.1.word (by simp only [avoids_cons, avoids_nil, and_true, FL]; omega),
            show FL + 32 * g = 32352 + 32 * (g - 35) by simp only [FL]; omega, hW.2 (g - 35) (by omega)]
          exact flag_hi S h1 I' hSk (by omega) (by omega)
    exact ⟨SlotBlocks.mono (by omega) h6', fun h0 => absurd (hH ▸ h0) (by decide), fun _ => h6'⟩
  · exact Fix.ks4_frame (Fix.ks4_frame (Fix.ks4_frame hks hL1.1 (by fx_av)) hfr (by fx_av)) hL2.1
      (by fx_av)
  · refine ((hL1.1.trans hfr).trans hL2.1).mono ?_
    intro r hr
    simp only [Fix.sqRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩
    · exact ⟨(HAVE6, HAVE6 + 32), by simp, by simp [HAVE6], by simp [HAVE6]⟩
    · exact ⟨(KB, KB + 800), by simp, by simp [KB], by simp [KB]⟩
    · exact ⟨(BK, BK + 800), by simp, by simp [BK], by simp [BK]⟩
    · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩
    · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩
    · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩

/-- The spec result read off the accepted list. -/
theorem aI_accL (I : Fips202.SpongeState) :
    ((aI I).isSome = decide (256 ≤ (Fix.accL (candI I) 336).length)) ∧
      ∀ a, aI I = some a → ∀ t, t < 256 → (a[t]!).toNat = (Fix.accL (candI I) 336)[t]! :=
  Fix.rejNTTPolyOf_accL _ (candI I) (fun t ht => by rw [Fix.rejZv_squeeze I ht]; rfl)

theorem done_result {I : Fips202.SpongeState} {m' : ByteArray} {sl lim : Nat} (hlim : 8 * lim ≤ 336)
    (h256 : 256 ≤ (Fix.accL (candI I) (8 * lim)).length)
    (hl : ∀ i, i < 256 → lane (word m' (20480 + 32 * i)) sl = (Fix.accL (candI I) (8 * lim))[i]!) :
    (∀ a, aI I = some a → ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat) ∧
      flag (aI I).isSome = wd 1 := by
  have hlen := le_trans h256 (Fix.accL_mono_length (candI I) hlim)
  refine ⟨fun a ha t ht => ?_, ?_⟩
  · rw [(aI_accL I).2 a ha t ht, Fix.accL_prefix _ hlim (by omega)]; exact hl t ht
  · rw [(aI_accL I).1, decide_eq_true hlen]; rfl

theorem fail_result {I : Fips202.SpongeState} (h : (Fix.accL (candI I) (8 * 42)).length < 256) :
    flag (aI I).isSome = wd 0 := by
  rw [show 8 * 42 = 336 from rfl] at h
  rw [(aI_accL I).1, decide_eq_false (by omega)]; rfl

end FixAux

open FixAux  -- port: own `FixAux` only

/-- **fix**: `[64 s, ret] ↦ [ok]`. Compacts lane `s` of `ABUF` to the slot's
RejNTTPoly result; other pending slots stay pending; the `KS` state is
restored. The caller has seen a flag of slot `s` among the first 32 groups.
The cost is `Gas.fixSq` if this call made the sixth squeeze, else
`Gas.fixNo`. -/
theorem fix_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.fix ret tail) (m : ByteArray) (hrc : RC4Table m)
    {sl : Nat} (hsl : sl < 4) (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hks : KS4 m S)
    (I : Fips202.SpongeState) (hp : Pending m S sl I)
    (hflag : ∃ g, g < 32 ∧ flagBit (word m (FL + 32 * g)) sl = 1) :
    ∃ m', (∀ a, aI I = some a → ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat) ∧
      (∀ sl' I', sl' < 4 → sl' ≠ sl → Pending m S sl' I' → Pending m' S sl' I') ∧
      (∀ sl', sl' < 4 → sl' ≠ sl → ∀ t, t < 280 →
        lane (word m' (ABUF + 32 * t)) sl' = lane (word m (ABUF + 32 * t)) sl') ∧
      KS4 m' S ∧ (word m HAVE6 ≠ 0 → word m' HAVE6 ≠ 0) ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.fix [wd (64 * sl)] ret tail m [flag (aI I).isSome] m'
        (if word m HAVE6 = 0 ∧ word m' HAVE6 ≠ 0 then Gas.fixSq else Gas.fixNo) := by
  classical
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.fix, Stack.kf4, Stack.blk, Stack.leaf] at this; omega
  have hsz : 2897 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hret : ret < 65536 := by have := hr.small; omega
  have hsh : 64 * sl ≤ 192 := by omega
  obtain ⟨hB5, hp0, hp6⟩ := hp
  have hF5 : ∀ g, g < 35 → word m (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = Fix.F (candI I) g := by
    intro g hg
    have := hB5.2 g (by omega)
    unfold flagBit at this
    rw [Nat.add_comm 23]; exact this
  -- first flagged group
  obtain ⟨g0, ⟨hg0, hf0⟩, hmin⟩ : ∃ g0, (g0 < 32 ∧ flagBit (word m (FL + 32 * g0)) sl = 1) ∧
      ∀ g, g < g0 → ¬ (g < 32 ∧ flagBit (word m (FL + 32 * g)) sl = 1) :=
    ⟨Nat.find hflag, Nat.find_spec hflag, fun g hg => Nat.find_min hflag hg⟩
  have h0 : ∀ g, g < g0 → word m (31232 + 32 * g) / 2 ^ (23 + 64 * sl) % 2 = 0 := by
    intro g hg
    have := hmin g hg
    simp only [flagBit, FL, not_and] at this
    have := this (by omega)
    rw [Nat.add_comm 23]; omega
  have he := Fix.fx_entry (ret := ret) hs htail hsz m (64 * sl) hsh
  have hsc := Fix.scan_reach (ret := ret) (sl := sl) hs htail hsz m g0 hg0 h0 g0 0 (by omega)
  have hsc' := hsc
  rw [Nat.mul_zero, Nat.add_zero] at hsc'
  have hhit := Fix.fx_scan_hit (ret := ret) hs htail hsz m (64 * sl) (Fix.lmask sl) (Fix.nmask sl)
    (Fix.qsv sl) (Fix.fmv sl) (20480 + 256 * g0) (by omega) (by
      rw [Fix.flag_addr]; intro h
      have := hf0; simp only [flagBit, FL] at this
      rw [Nat.add_comm (64 * sl), (Fix.fmv_and sl _).mp h] at this; exact absurd this (by decide))
  have hpre : Reach (callState s Entry.fix ([wd (64 * sl)] ++ wd ret :: tail) m)
      (Fix.G s ret tail sl 14727 (20480 + 256 * 35) (20480 + 256 * g0) (20480 + 32 * (8 * g0)) m)
      (40 + g0 * 55 + 42) :=
    ((he.trans hsc').trans hhit).of_eq rfl (by
      rw [show 20480 + 32 * (8 * g0) = 20480 + 256 * g0 by omega])
  -- phase 1
  have hacc0 : Fix.AccAt m sl (candI I) (8 * g0) (8 * g0) := by
    have hq : ∀ t, t < 8 * g0 → candI I t < Fips204.q := fun t ht => by
      have hz : Fix.F (candI I) (t / 8) = 0 := by
        rw [← hF5 (t / 8) (by omega)]; exact h0 (t / 8) (by omega)
      have := Fix.F_zero hz (t % 8) (Nat.mod_lt _ (by omega))
      rwa [Nat.div_add_mod] at this
    obtain ⟨hlen, hget⟩ := Fix.accL_all (candI I) (8 * g0) hq
    exact ⟨hlen.symm, fun i hi => by rw [hget i hi]; exact hB5.1 i (by omega)⟩
  obtain ⟨M1, hL1, hres1⟩ := Fix.phase hs htail hsz hr.jumpdest hret hsl (candI I) 35 (by norm_num)
    (35 - g0) g0 (8 * g0) m (by omega) (by omega) hacc0 (by omega)
    (fun t _ h2 => hB5.1 t (by omega)) (fun g' _ h2 => hF5 g' h2)
  rcases hres1 with ⟨h256, hlanes, hrch⟩ | ⟨hA1, hlt1, hrch⟩
  · -- done in phase 1
    obtain ⟨hval, hfl⟩ := done_result (sl := sl) (by norm_num) h256 hlanes
    obtain ⟨hpend, hlo, hks', hH, hfr⟩ := post_nosq (hL1.mono (by norm_num)) hks
    refine ⟨M1, hval, hpend, hlo, hks', fun h => by rwa [hH], hfr, ?_⟩
    rw [call_iff, if_neg (by rw [hH]; tauto), hfl]
    exact (hpre.trans hrch).mono (by unfold Gas.fixNo; omega)
  · have hH1 : word M1 4064 = word m 4064 :=
      hL1.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega)
    have hlt1' : (Fix.accL (candI I) (8 * 35)).length < 256 := hlt1
    have hw1 := Fix.accL_length_le (candI I) (8 * 35)
    by_cases h6 : word m HAVE6 = 0
    · -- sixth squeeze
      obtain ⟨M5, hsq, hfr5, h65, hW⟩ := Fix.squeeze_reach hs hr htail hsz sl M1
        (Fix.rc4_frame hrc hL1.1 (by fx_av)) (by rw [hH1]; exact h6)
        (20480 + 256 * 35) (20480 + 32 * (Fix.accL (candI I) (8 * 35)).length)
      have hW' := hW S hS (Fix.ks4_frame hks hL1.1 (by fx_av))
      have hS5 : S sl = permN 5 I := hp0 h6
      have hacc5 : Fix.AccAt M5 sl (candI I) (8 * 35) (Fix.accL (candI I) (8 * 35)).length :=
        ⟨hA1.1, fun i hi => by
          rw [hfr5.word (by simp only [Fix.sqRegions, avoids_cons, avoids_nil, and_true]; omega)]
          exact hA1.2 i hi⟩
      obtain ⟨M2, hL2, hres2⟩ := Fix.phase hs htail hsz hr.jumpdest hret hsl (candI I) 42 (by norm_num)
        7 35 _ M5 (by norm_num) (by norm_num) hacc5 hlt1'
        (fun t h1 h2 => by
          rw [show 20480 + 32 * t = 29440 + 32 * (t - 280) by omega, hW'.1 (t - 280) (by omega)]
          exact lane_hi S hsl I hS5 (by omega) (by omega))
        (fun g' h1 h2 => by
          rw [show 31232 + 32 * g' = 32352 + 32 * (g' - 35) by omega, hW'.2 (g' - 35) (by omega),
            Nat.add_comm 23]
          exact flag_hi S hsl I hS5 h1 h2)
      obtain ⟨hpend, hlo, hks', hH, hfr⟩ := post_sq hL1 hfr5 h65 hks hW' hL2 h6
      have hgas : (if word m HAVE6 = 0 ∧ word M2 HAVE6 ≠ 0 then Gas.fixSq else Gas.fixNo) = Gas.fixSq :=
        if_pos ⟨h6, by rw [hH]; decide⟩
      rcases hres2 with ⟨h256, hlanes, hrch2⟩ | ⟨_, hlt2, hrch2⟩
      · obtain ⟨hval, hfl⟩ := done_result (sl := sl) (by norm_num) h256 hlanes
        refine ⟨M2, hval, hpend, hlo, hks', fun _ => by rw [hH]; decide, hfr, ?_⟩
        rw [call_iff, hgas, hfl]
        exact (((hpre.trans hrch).trans hsq).trans hrch2).mono (by unfold Gas.fixSq; omega)
      · have hfail := Fix.fx_fail (ret := ret) hs htail hsz M2 (64 * sl) (Fix.lmask sl) (Fix.nmask sl)
          (Fix.qsv sl) (Fix.fmv sl) (20480 + 256 * 42)
          (20480 + 32 * (Fix.accL (candI I) (8 * 42)).length) hr.jumpdest hret
        have hlt2' : (Fix.accL (candI I) 336).length < 256 := hlt2
        refine ⟨M2, fun a ha => absurd ((aI_accL I).1 ▸ (show (aI I).isSome = true by rw [ha]; rfl))
          (by simp only [decide_eq_true_eq]; omega), hpend, hlo, hks', fun _ => by rw [hH]; decide,
          hfr, ?_⟩
        rw [call_iff, hgas, fail_result hlt2]
        exact ((((hpre.trans hrch).trans hsq).trans hrch2).trans hfail).mono
          (by unfold Gas.fixSq; omega)
    · -- sixth block already present
      have hB6 := hp6 h6
      have hc := Fix.fx_ext_cont (ret := ret) hs htail hsz M1 (64 * sl) (Fix.lmask sl) (Fix.nmask sl)
        (Fix.qsv sl) (Fix.fmv sl) (20480 + 256 * 35) (20480 + 256 * 35)
        (20480 + 32 * (Fix.accL (candI I) (8 * 35)).length) (by norm_num) (by norm_num)
        (by rw [hH1]; exact h6)
      have hc2 := Fix.fx_cont (ret := ret) hs htail hsz M1 (64 * sl) (Fix.lmask sl) (Fix.nmask sl)
        (Fix.qsv sl) (Fix.fmv sl) (20480 + 256 * 35) (20480 + 256 * 35)
        (20480 + 32 * (Fix.accL (candI I) (8 * 35)).length)
      obtain ⟨M2, hL2, hres2⟩ := Fix.phase hs htail hsz hr.jumpdest hret hsl (candI I) 42 (by norm_num)
        7 35 _ M1 (by norm_num) (by norm_num) hA1 hlt1'
        (fun t h1 h2 => by rw [hL1.word_hi (by omega)]; exact hB6.1 t (by omega))
        (fun g' h1 h2 => by
          rw [hL1.1.word (by simp only [avoids_cons, avoids_nil, and_true]; omega), Nat.add_comm 23]
          exact hB6.2 g' (by omega))
      obtain ⟨hpend, hlo, hks', hH, hfr⟩ := post_nosq ((hL1.mono (by norm_num)).trans hL2 (le_refl _)) hks
      have hgas : (if word m HAVE6 = 0 ∧ word M2 HAVE6 ≠ 0 then Gas.fixSq else Gas.fixNo) = Gas.fixNo :=
        if_neg (fun h => h6 h.1)
      rcases hres2 with ⟨h256, hlanes, hrch2⟩ | ⟨_, hlt2, hrch2⟩
      · obtain ⟨hval, hfl⟩ := done_result (sl := sl) (by norm_num) h256 hlanes
        refine ⟨M2, hval, hpend, hlo, hks', fun h => by rwa [hH], hfr, ?_⟩
        rw [call_iff, hgas, hfl]
        exact ((((hpre.trans hrch).trans hc).trans hc2).trans hrch2).mono (by unfold Gas.fixNo; omega)
      · have hfail := Fix.fx_fail (ret := ret) hs htail hsz M2 (64 * sl) (Fix.lmask sl) (Fix.nmask sl)
          (Fix.qsv sl) (Fix.fmv sl) (20480 + 256 * 42)
          (20480 + 32 * (Fix.accL (candI I) (8 * 42)).length) hr.jumpdest hret
        have hlt2' : (Fix.accL (candI I) 336).length < 256 := hlt2
        refine ⟨M2, fun a ha => absurd ((aI_accL I).1 ▸ (show (aI I).isSome = true by rw [ha]; rfl))
          (by simp only [decide_eq_true_eq]; omega), hpend, hlo, hks', fun h => by rwa [hH], hfr, ?_⟩
        rw [call_iff, hgas, fail_result hlt2]
        exact (((((hpre.trans hrch).trans hc).trans hc2).trans hrch2).trans hfail).mono
          (by unfold Gas.fixNo; omega)

namespace FixAux

open MlDsaOpt44.Proofs  -- port: the 44 `FixAux` namespace is not imported

/-! ## Proof of `gfix_call` -/

/-- OR of the flag words `0 … n`. -/
def gor (M : ByteArray) : Nat → Nat
  | 0 => word M 31232
  | n + 1 => word M (31232 + 32 * (n + 1)) ||| gor M n

theorem gor_bit (M : ByteArray) (j : Nat) : ∀ n, (gor M n).testBit j = true ↔
    ∃ g, g ≤ n ∧ (word M (31232 + 32 * g)).testBit j = true
  | 0 => by simp [gor]
  | n + 1 => by
    rw [gor, Nat.testBit_or, Bool.or_eq_true, gor_bit M j n]
    constructor
    · rintro (h | ⟨g, hg, h⟩)
      · exact ⟨n + 1, le_refl _, h⟩
      · exact ⟨g, by omega, h⟩
    · rintro ⟨g, hg, h⟩
      by_cases hgn : g = n + 1
      · subst hgn; exact Or.inl h
      · exact Or.inr ⟨g, by omega, h⟩

theorem gflags_gor (M : ByteArray) :
    Fix.gflags M = 52656145834278593351813509227247135921718862144084218434291761152 &&& gor M 31 := rfl

theorem gflags_bit (M : ByteArray) {k : Nat} (hk : k < 4) :
    (Fix.gflags M).testBit (64 * k + 23) = true ↔
      ∃ g, g < 32 ∧ flagBit (word M (FL + 32 * g)) k = 1 := by
  have hm : ∀ k, k < 4 →
      (52656145834278593351813509227247135921718862144084218434291761152 : Nat).testBit (64 * k + 23) =
        true := by decide +kernel
  rw [gflags_gor, Nat.testBit_and, hm k hk, Bool.true_and, gor_bit]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, by omega, ?_⟩
    unfold flagBit; rw [← Nat.toNat_testBit, show FL + 32 * g = 31232 + 32 * g from rfl, h]; rfl
  · rintro ⟨g, hg, h⟩
    refine ⟨g, by omega, ?_⟩
    unfold flagBit at h; rw [← Nat.toNat_testBit] at h
    cases hb : (word M (31232 + 32 * g)).testBit (64 * k + 23)
    · rw [show FL + 32 * g = 31232 + 32 * g from rfl, hb] at h; exact absurd h (by decide)
    · rfl

theorem cond_eq (x y k p : Nat) :
    (x / 2 ^ k &&& y / 2 ^ p) % 2 = if (x.testBit k && y.testBit p) then 1 else 0 := by
  have := Nat.toNat_testBit (x / 2 ^ k &&& y / 2 ^ p) 0
  rw [pow_zero, Nat.div_one] at this
  rw [← this, Nat.testBit_and, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.zero_add,
    Nat.zero_add]
  cases x.testBit k <;> cases y.testBit p <;> rfl

theorem gflags_mod2 (M : ByteArray) : Fix.gflags M % 2 = 0 := by
  have h := Nat.toNat_testBit (Fix.gflags M) 0
  rw [pow_zero, Nat.div_one] at h
  rw [← h, gflags_gor, Nat.testBit_and]
  have : (52656145834278593351813509227247135921718862144084218434291761152 : Nat).testBit 0 = false := by
    decide +kernel
  rw [this]; rfl

/-- The flags word of `gfix` on the stack: bit 0 records that `blkt` has run. -/
def fv (m : ByteArray) (t : Nat) : Nat := Fix.gflags m ||| t

theorem fv_lt (m : ByteArray) {t : Nat} (ht : t < 2) : fv m t < 2 ^ 256 :=
  Nat.or_lt_two_pow (Fix.gflags_lt m) (by omega)

theorem fv_mod2 (m : ByteArray) {t : Nat} (ht : t < 2) : fv m t % 2 = t := by
  have h := Nat.toNat_testBit (fv m t) 0
  rw [pow_zero, Nat.div_one] at h
  rw [← h, fv, Nat.testBit_or]
  have h0 := Nat.toNat_testBit (Fix.gflags m) 0
  rw [pow_zero, Nat.div_one, gflags_mod2] at h0
  have h1 := Nat.toNat_testBit t 0
  rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt ht] at h1
  cases hb : (Fix.gflags m).testBit 0
  · rw [Bool.false_or, h1]
  · rw [hb] at h0; exact absurd h0 (by decide)

theorem fv_bit (m : ByteArray) {t : Nat} (ht : t < 2) (k : Nat) :
    (fv m t).testBit (64 * k + 23) = (Fix.gflags m).testBit (64 * k + 23) := by
  have h2 : 2 ^ 1 ≤ 2 ^ (64 * k + 23) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [fv, Nat.testBit_or, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ht (by simpa using h2)),
    Bool.or_false]

theorem fv_one (m : ByteArray) : (1 ||| fv m 0) = fv m 1 := by
  unfold fv; rw [Nat.or_zero, Nat.or_comm]

theorem fv_zero (m : ByteArray) : fv m 0 = Fix.gflags m := Nat.or_zero _

/-- A slot without a flag among its first 32 groups: its first 256 candidates are accepted. -/
theorem noflag_result {m M : ByteArray} {k : Nat} {I : Fips202.SpongeState}
    (h5 : SlotHead m k I) (hl : ∀ t, t < 256 → lane (word M (ABUF + 32 * t)) k = candI I t)
    (hnf : ∀ g, g < 32 → flagBit (word m (FL + 32 * g)) k ≠ 1) :
    (aI I).isSome = true ∧
      ∀ a, aI I = some a → ∀ t, t < 256 → lane (word M (ABUF + 32 * t)) k = (a[t]!).toNat := by
  have hq : ∀ t, t < 256 → candI I t < Fips204.q := by
    intro t ht
    have hf := h5.2 (t / 8) (by omega)
    have h0 : flagBit (word m (FL + 32 * (t / 8))) k = 0 := by
      have := hnf (t / 8) (by omega); unfold flagBit at this ⊢; omega
    rw [h0] at hf
    have := Fix.F_zero (c := candI I) (g := t / 8) hf.symm (t % 8) (Nat.mod_lt _ (by omega))
    rwa [Nat.div_add_mod] at this
  obtain ⟨hlen, hget⟩ := Fix.accL_all (candI I) 256 hq
  have hmono := Fix.accL_mono_length (candI I) (show 256 ≤ 336 by omega)
  refine ⟨by rw [(aI_accL I).1]; exact decide_eq_true (by omega), fun a ha t ht => ?_⟩
  rw [(aI_accL I).2 a ha t ht, Fix.accL_prefix _ (show 256 ≤ 336 by omega) (by omega), hget t ht]
  exact hl t ht

theorem candI_b4 (I : Fips202.SpongeState) {t : Nat} (h1 : 224 ≤ t) (h2 : t < 280) :
    candI I t = cand (permN 5 I) (t - 224) := by
  unfold candI; rw [show t / 56 + 1 = 5 by omega, show t % 56 = t - 224 by omega]

/-- After `blkt`, every slot with its head in place is pending. -/
theorem pend_blkt {m MT : ByteArray} {S : Nat → Fips202.SpongeState} (hS : Sized4 S) (hks : KS4 m S)
    (h6 : word m HAVE6 = 0)
    (hfr : FrameExcept m MT [(ABUF + 1792 * 4 + 1024, ABUF + 1792 * 5), (FL + 224 * 4 + 128, FL + 224 * 5)])
    (hpost : ∀ S, Sized4 S → KS4 m S →
        (∀ i, 32 ≤ i → i < 56 → word MT (ABUF + 1792 * 4 + 32 * i) = pack4 fun k => cand (S k) i) ∧
        (∀ g, 4 ≤ g → g < 7 → word MT (FL + 224 * 4 + 32 * g) = flagWord S g))
    {j : Nat} (hj : j < 4) {I : Fips202.SpongeState} (hH : SlotHead m j I) (hSj : S j = permN 5 I) :
    Pending MT S j I := by
  obtain ⟨hc, hf⟩ := hpost S hS hks
  have hH6 : word MT HAVE6 = 0 := by
    rw [hfr.word (by simp only [avoids_cons, avoids_nil, and_true, HAVE6, ABUF, FL]; omega)]; exact h6
  refine ⟨⟨fun t ht => ?_, fun g hg => ?_⟩, fun _ => hSj, fun h => absurd hH6 h⟩
  · by_cases hlt : t < 256
    · rw [hfr.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
      exact hH.1 t hlt
    · rw [show ABUF + 32 * t = ABUF + 1792 * 4 + 32 * (t - 224) by simp only [ABUF]; omega,
        hc (t - 224) (by omega) (by omega), Fix.lane_pack4_cand _ _ hj, hSj, candI_b4 I (by omega) ht]
  · by_cases hlt : g < 32
    · rw [hfr.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
      exact hH.2 g hlt
    · rw [show FL + 32 * g = FL + 224 * 4 + 32 * (g - 28) by simp only [FL]; omega,
        hf (g - 28) (by omega) (by omega)]
      unfold flagBit
      rw [Fix.flagWord_bit _ _ hj, hSj,
        Fix.any_range_congr (g := fun i => decide (Fips204.q ≤ candI I (8 * g + i))) (fun i hi => by
          rw [candI_b4 I (by omega) (by omega), show 8 * g + i - 224 = 8 * (g - 28) + i by omega])]

def okb (amask : Nat) (I : Nat → Fips202.SpongeState) (k : Nat) : Bool :=
  (List.range k).all fun sl => !amask.testBit sl || (aI (I sl)).isSome

theorem okb_succ (amask : Nat) (I : Nat → Fips202.SpongeState) (k : Nat) :
    okb amask I (k + 1) = (okb amask I k && (!amask.testBit k || (aI (I k)).isSome)) := by
  simp [okb, List.range_succ, List.all_append]

def cntA (amask k : Nat) : Nat := (List.range k).countP (amask.testBit ·)

theorem cntA_succ (amask k : Nat) :
    cntA amask (k + 1) = cntA amask k + if amask.testBit k then 1 else 0 := by
  simp [cntA, List.range_succ, List.countP_append]

/-- Remaining gas allowance after the slots `< k`; `t = 1` once `blkt` has run. -/
def gbud (amask k : Nat) (M : ByteArray) (t : Nat) : Nat :=
  cntA amask k * Gas.fixNo + (if word M HAVE6 = 0 then 0 else Gas.fixSq - Gas.fixNo) + t * Gas.blkt

structure GInv (m M : ByteArray) (S I : Nat → Fips202.SpongeState) (amask k t : Nat) : Prop where
  t2 : t < 2
  rc : RC4Table M
  ks : KS4 M S
  fr : FrameExcept m M fixRegions
  head : t = 0 → M = m
  pend : t = 1 → ∀ j, k ≤ j → j < 4 → amask.testBit j → Pending M S j (I j)
  done : ∀ j, j < k → amask.testBit j → ∀ a, aI (I j) = some a → ∀ t', t' < 256 →
    lane (word M (ABUF + 32 * t')) j = (a[t']!).toNat

/-- Slot-check state of `gfix`. -/
abbrev cst (s : State) (ret : Nat) (tail : List UInt256) (pc f ok amask : Nat) (M : ByteArray) :
    State :=
  callState s pc (wd f :: wd ok :: wd amask :: wd ret :: tail) M

/-- The running `ok` value after the slots `< k`. -/
abbrev okv (amask : Nat) (I : Nat → Fips202.SpongeState) (k : Nat) : Nat :=
  if okb amask I k then 1 else 0

theorem fixRegions_trans {m M M' : ByteArray} (h1 : FrameExcept m M fixRegions)
    (h2 : FrameExcept M M' fixRegions) : FrameExcept m M' fixRegions :=
  (h1.trans h2).mono fun r hr => ⟨r, List.mem_append.mp hr |>.elim id id, le_refl _, le_refl _⟩

theorem okv_succ_and (amask : Nat) (I : Nat → Fips202.SpongeState) {k : Nat}
    (hact : amask.testBit k = true) :
    (okv amask I k &&& (if (aI (I k)).isSome then 1 else 0)) = okv amask I (k + 1) := by
  unfold okv; rw [okb_succ, hact]
  cases okb amask I k <;> cases (aI (I k)).isSome <;> rfl

/-- One slot of `gfix`: skip it, or (`blkt` first, if not yet made) call `fix`. -/
theorem gstep {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.gfix ret tail) (m : ByteArray) {amask : Nat}
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (I : Nat → Fips202.SpongeState)
    (hH : ∀ j, j < 4 → amask.testBit j → SlotHead m j (I j) ∧ S j = permN 5 (I j))
    (h6 : word m HAVE6 = 0)
    {k : Nat} (hk : k < 4) {pc pc' rT rF : Nat}
    (hjT : Decode.isValidJumpDest optBytecode rT = true) (hrT : rT < 2 ^ 16)
    (hjF : Decode.isValidJumpDest optBytecode rF = true) (hrF : rF < 2 ^ 16)
    {B sk cT tr cF rk : Nat} (hB1 : sk ≤ B) (hB2 : cT + tr + rk ≤ B) (hB3 : cF + rk ≤ B)
    (M : ByteArray) {t : Nat} (hI : GInv m M S I amask k t)
    (hskip : (amask / 2 ^ k &&& fv m t / 2 ^ (64 * k + 23)) % 2 = 0 →
      Reach (cst s ret tail pc (fv m t) (okv amask I k) amask M)
        (cst s ret tail pc' (fv m t) (okv amask I k) amask M) sk)
    (hcallT : (amask / 2 ^ k &&& fv m 0 / 2 ^ (64 * k + 23)) % 2 = 1 →
      Reach (cst s ret tail pc (fv m 0) (okv amask I k) amask M)
        (callState s 12179 (wd rT :: wd (fv m 0) :: wd (okv amask I k) :: wd amask :: wd ret :: tail) M) cT)
    (htret : ∀ M', Reach (callState s rT (wd (fv m 0) :: wd (okv amask I k) :: wd amask :: wd ret :: tail) M')
      (callState s 14669 (wd (64 * k) :: wd rF :: wd (fv m 1) :: wd (okv amask I k) :: wd amask ::
        wd ret :: tail) M') tr)
    (hcallF : (amask / 2 ^ k &&& fv m 1 / 2 ^ (64 * k + 23)) % 2 = 1 →
      Reach (cst s ret tail pc (fv m 1) (okv amask I k) amask M)
        (callState s 14669 (wd (64 * k) :: wd rF :: wd (fv m 1) :: wd (okv amask I k) :: wd amask ::
          wd ret :: tail) M) cF)
    (hret : ∀ (M' : ByteArray) (r : Nat), r < 2 →
      Reach (callState s rF (wd r :: wd (fv m 1) :: wd (okv amask I k) :: wd amask :: wd ret :: tail) M')
        (cst s ret tail pc' (fv m 1) (okv amask I k &&& r) amask M') rk) :
    ∃ M' t', GInv m M' S I amask (k + 1) t' ∧ ∃ c,
      Reach (cst s ret tail pc (fv m t) (okv amask I k) amask M)
        (cst s ret tail pc' (fv m t') (okv amask I (k + 1)) amask M') c ∧
      c + gbud amask k M t ≤ B + gbud amask (k + 1) M' t' := by
  have ht2 := hI.t2
  have hcond : ∀ t, t < 2 → (amask / 2 ^ k &&& fv m t / 2 ^ (64 * k + 23)) % 2 =
      if (amask.testBit k && (Fix.gflags m).testBit (64 * k + 23)) then 1 else 0 := by
    intro t ht; rw [cond_eq, fv_bit m ht]
  have hfixGas : Gas.fixNo ≤ Gas.fixSq := by unfold Gas.fixNo Gas.fixSq; omega
  by_cases hc : (amask.testBit k && (Fix.gflags m).testBit (64 * k + 23)) = true
  · simp only [Bool.and_eq_true] at hc
    obtain ⟨hact, hfb⟩ := hc
    obtain ⟨g, hg, hfg⟩ := (gflags_bit m hk).mp hfb
    obtain ⟨hHk, hSk⟩ := hH k hk hact
    have hc1 : ∀ t, t < 2 → (amask / 2 ^ k &&& fv m t / 2 ^ (64 * k + 23)) % 2 = 1 := fun t ht => by
      rw [hcond t ht, hact, hfb]; rfl
    have hrF' : RetOK Stack.fix rF ([wd (fv m 1), wd (okv amask I k), wd amask, wd ret] ++ tail) :=
      hr.callee (by simp [Stack.gfix, Stack.blk, Stack.fix, Stack.kf4, Stack.leaf]) hjF hrF
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · -- `blkt`, then `fix`
      have hM := hI.head rfl
      subst hM
      have hrT' : RetOK Stack.blk rT ([wd (fv M 0), wd (okv amask I k), wd amask, wd ret] ++ tail) :=
        hr.callee (by simp [Stack.gfix, Stack.blk, Stack.fix, Stack.kf4, Stack.leaf]) hjT hrT
      obtain ⟨MT, hpostT, hfrT, hcT⟩ := blkt_call hs hrT' M
      rw [call_iff] at hcT
      simp only [List.nil_append, List.cons_append] at hcT
      have hpT : ∀ j, j < 4 → amask.testBit j → Pending MT S j (I j) := fun j hj ha =>
        pend_blkt hS hI.ks h6 hfrT hpostT hj (hH j hj ha).1 (hH j hj ha).2
      have hfrT' : FrameExcept M MT fixRegions := hfrT.mono (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF], by simp [ABUF, FL]⟩
        · exact ⟨(ABUF, FL + 1344), by simp, by simp [ABUF, FL], by simp [ABUF, FL]⟩)
      have hH6T : word MT HAVE6 = 0 := by
        rw [hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, HAVE6, ABUF, FL]; omega)]
        exact h6
      have hflag : ∃ g, g < 32 ∧ flagBit (word MT (FL + 32 * g)) k = 1 :=
        ⟨g, hg, by
          rw [hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
          exact hfg⟩
      obtain ⟨M', hval, hpend', hlanes', hks', hmono, hfr', hcl⟩ := fix_call hs hrF' MT
        (Fix.rc4_frame hI.rc hfrT (by fx_av)) hk S hS (Fix.ks4_frame hI.ks hfrT (by fx_av)) (I k)
        (hpT k hk hact) hflag
      rw [call_iff] at hcl
      have hr2 := hret M' (if (aI (I k)).isSome then 1 else 0) (by split <;> omega)
      refine ⟨M', 1, ⟨by omega, Fix.rc4_frame hI.rc (fixRegions_trans hfrT' hfr') (by fx_av), hks',
        fixRegions_trans hfrT' hfr', fun h => absurd h (by omega),
        fun _ j h1 h2 h3 => hpend' j (I j) h2 (by omega) (hpT j h2 h3),
        fun j h1 h2 a ha t' ht' => ?_⟩, _, ((((hcallT (hc1 0 (by omega))).trans hcT).trans
          (htret MT)).trans hcl).trans (hr2.of_eq rfl (by rw [okv_succ_and amask I hact])), ?_⟩
      · by_cases hjk : j = k
        · subst hjk; exact hval a ha t' ht'
        · rw [hlanes' j (by omega) hjk t' (by omega),
            hfrT.word (by simp only [avoids_cons, avoids_nil, and_true, ABUF, FL]; omega)]
          exact hI.done j (by omega) h2 a ha t' ht'
      · unfold gbud
        rw [cntA_succ, if_pos hact, if_pos h6, hH6T]
        by_cases h1 : word M' HAVE6 = 0
        · rw [if_neg (fun h => h.2 h1), if_pos h1]; rw [Nat.add_mul]; omega
        · rw [if_pos ⟨rfl, h1⟩, if_neg h1]; rw [Nat.add_mul]; omega
    · -- `fix` only
      have hPk := hI.pend rfl k (le_refl _) hk hact
      have hflag : ∃ g, g < 32 ∧ flagBit (word M (FL + 32 * g)) k = 1 :=
        ⟨g, hg, by rw [hPk.1.2 g (by omega), ← hHk.2 g hg]; exact hfg⟩
      obtain ⟨M', hval, hpend', hlanes', hks', hmono, hfr', hcl⟩ := fix_call hs hrF' M hI.rc hk S hS
        hI.ks (I k) hPk hflag
      rw [call_iff] at hcl
      have hr2 := hret M' (if (aI (I k)).isSome then 1 else 0) (by split <;> omega)
      refine ⟨M', 1, ⟨by omega, Fix.rc4_frame hI.rc hfr' (by fx_av), hks', fixRegions_trans hI.fr hfr',
        fun h => absurd h (by omega),
        fun _ j h1 h2 h3 => hpend' j (I j) h2 (by omega) (hI.pend rfl j (by omega) h2 h3),
        fun j h1 h2 a ha t' ht' => ?_⟩, _, ((hcallF (hc1 1 (by omega))).trans hcl).trans
          (hr2.of_eq rfl (by rw [okv_succ_and amask I hact])), ?_⟩
      · by_cases hjk : j = k
        · subst hjk; exact hval a ha t' ht'
        · rw [hlanes' j (by omega) hjk t' (by omega)]; exact hI.done j (by omega) h2 a ha t' ht'
      · unfold gbud
        rw [cntA_succ, if_pos hact]
        by_cases h0 : word M HAVE6 = 0
        · by_cases h1 : word M' HAVE6 = 0
          · rw [if_neg (fun h => h.2 h1), if_pos h0, if_pos h1]; rw [Nat.add_mul]; omega
          · rw [if_pos ⟨h0, h1⟩, if_pos h0, if_neg h1]; rw [Nat.add_mul]; omega
        · have h1 := hmono h0
          rw [if_neg (fun h => h0 h.1), if_neg h0, if_neg h1]; rw [Nat.add_mul]; omega
  · have hc0 : (amask / 2 ^ k &&& fv m t / 2 ^ (64 * k + 23)) % 2 = 0 := by
      rw [hcond t ht2, if_neg hc]
    have hres : amask.testBit k = true → (aI (I k)).isSome = true ∧ ∀ a, aI (I k) = some a →
        ∀ t', t' < 256 → lane (word M (ABUF + 32 * t')) k = (a[t']!).toNat := fun hact =>
      noflag_result (hH k hk hact).1 (fun t' ht' => by
          rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
          · rw [hI.head rfl]; exact (hH k hk hact).1.1 t' ht'
          · exact (hI.pend rfl k (le_refl _) hk hact).1.1 t' (by omega))
        (fun g hg h1 => hc (by rw [hact, (gflags_bit m hk).mpr ⟨g, hg, h1⟩]; rfl))
    refine ⟨M, t, ⟨ht2, hI.rc, hI.ks, hI.fr, hI.head, fun h j h1 h2 h3 => hI.pend h j (by omega) h2 h3,
      fun j h1 h2 a ha t' ht' => ?_⟩, sk, ?_, ?_⟩
    · by_cases hjk : j = k
      · subst hjk; exact (hres h2).2 a ha t' ht'
      · exact hI.done j (by omega) h2 a ha t' ht'
    · have : okv amask I (k + 1) = okv amask I k := by
        unfold okv
        rw [okb_succ]
        cases hact : amask.testBit k
        · simp
        · simp [(hres hact).1]
      rw [this]; exact hskip hc0
    · unfold gbud; rw [cntA_succ]
      have : cntA amask k * Gas.fixNo ≤ (cntA amask k + if amask.testBit k = true then 1 else 0) *
          Gas.fixNo := Nat.mul_le_mul_right _ (by omega)
      omega

end FixAux

open FixAux  -- port: own `FixAux` only

/-- **gfix**: `[amask, ret] ↦ [ok]`. Every active slot (bit `s` of `amask`)
ends with its RejNTTPoly result in lane `s` of `ABUF[0, 256)`; `ok` iff all
active slots succeeded. At most `popcnt amask ≤ n` slots call `fix`. On entry
the active slots' first 256 candidates are in place and their kf4 states are
five permutations past their absorbed states. -/
theorem gfix_call {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.gfix ret tail) (m : ByteArray) (hrc : RC4Table m)
    {amask : Nat} (hamask : amask < 16) (n : Nat) (hn : popcnt amask ≤ n)
    (S : Nat → Fips202.SpongeState) (hS : Sized4 S) (hks : KS4 m S)
    (I : Nat → Fips202.SpongeState) (h6 : word m HAVE6 = 0)
    (hp : ∀ sl, sl < 4 → amask.testBit sl → SlotHead m sl (I sl) ∧ S sl = permN 5 (I sl)) :
    ∃ m', (∀ sl, sl < 4 → amask.testBit sl → ∀ a, aI (I sl) = some a →
        ∀ t, t < 256 → lane (word m' (ABUF + 32 * t)) sl = (a[t]!).toNat) ∧
      KS4 m' S ∧
      FrameExcept m m' [(ABUF, FL + 1344), (HAVE6, HAVE6 + 32), (KB, KB + 800), (BK, BK + 800)] ∧
      Call s Entry.gfix [wd amask] ret tail m
        [flag ((List.range 4).all fun sl => !amask.testBit sl || (aI (I sl)).isSome)] m'
        (Gas.gfix n) := by
  have htail : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.gfix, Stack.fix, Stack.kf4, Stack.blk, Stack.leaf] at this; omega
  have hsz : 2897 ≤ s.activeWords.toNat := by have := hs.sized; simpa [memWords] using this
  have hret : ret < 65536 := by have := hr.small; omega
  have hgas : 806 + Gas.blkt + popcnt amask * Gas.fixNo + (Gas.fixSq - Gas.fixNo) ≤ Gas.gfix n := by
    unfold Gas.gfix Gas.gfix0
    have := Nat.mul_le_mul_right Gas.fixNo hn
    omega
  by_cases hf0 : Fix.gflags m = 0
  · -- no slot flagged
    have hall : ∀ sl, sl < 4 → amask.testBit sl → (aI (I sl)).isSome = true ∧ ∀ a, aI (I sl) = some a →
        ∀ t, t < 256 → lane (word m (ABUF + 32 * t)) sl = (a[t]!).toNat := fun sl hsl hact =>
      noflag_result (hp sl hsl hact).1 (hp sl hsl hact).1.1 (fun g hg h1 => by
        have := (gflags_bit m hsl).mpr ⟨g, hg, h1⟩
        rw [hf0] at this; exact absurd this (by simp))
    have hok : ((List.range 4).all fun sl => !amask.testBit sl || (aI (I sl)).isSome) = true := by
      simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true]
      intro sl hsl
      cases hact : amask.testBit sl
      · exact Or.inl rfl
      · exact Or.inr (hall sl hsl hact).1
    refine ⟨m, fun sl hsl hact => (hall sl hsl hact).2, hks, FrameExcept.refl _ _, ?_⟩
    rw [call_iff, hok]
    exact (Fix.gx_fast (ret := ret) hs htail hsz m amask hf0 hr.jumpdest hret).mono (by
      unfold Gas.gfix Gas.gfix0 Gas.fixNo Gas.fixSq Gas.blkt; omega)
  · have hpre := Fix.gx_pre (ret := ret) hs htail hsz m amask hf0
    have hpre' : Reach (callState s 12966 (wd amask :: wd ret :: tail) m)
        (cst s ret tail 13164 (fv m 0) (okv amask I 0) amask m) 317 :=
      hpre.of_eq rfl (by rw [fv_zero]; rfl)
    have hI0 : GInv m m S I amask 0 0 :=
      ⟨by omega, hrc, hks, FrameExcept.refl _ _, fun _ => rfl, fun h => absurd h (by omega),
        fun j hj => absurd hj (by omega)⟩
    have hH := hp
    obtain ⟨M1, t1, hI1, c0, hr0, hb0⟩ := gstep hs hr m S hS I hH h6 (k := 0) (by omega) (pc := 13164)
      (pc' := 13213) (rT := 13195) (rF := 13208) (by simp only [Infra.isValidJumpDest_lit])
      (by norm_num) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
      (B := 115) (by norm_num) (by norm_num) (by norm_num) m hI0
      (fun h => Fix.gx_skip0 (ret := ret) hs htail hsz m amask _ _ hamask (fv_lt m (by omega)) h)
      (fun h => Fix.gx_callT0 (ret := ret) hs htail hsz m amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' => (Fix.gx_tret0 (ret := ret) hs htail hsz M' amask (fv m 0) _ (fv_lt m (by omega))).of_eq
        rfl (by rw [fv_one]))
      (fun h => Fix.gx_callF0 (ret := ret) hs htail hsz m amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' r hr' => Fix.gx_ret0 (ret := ret) hs htail hsz M' amask _ _ r (by unfold okv; split <;> omega) hr')
    obtain ⟨M2, t2, hI2, c1, hr1, hb1⟩ := gstep hs hr m S hS I hH h6 (k := 1) (by omega) (pc := 13213)
      (pc' := 13265) (rT := 13246) (rF := 13260) (by simp only [Infra.isValidJumpDest_lit])
      (by norm_num) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
      (B := 118) (by norm_num) (by norm_num) (by norm_num) M1 hI1
      (fun h => Fix.gx_skip1 (ret := ret) hs htail hsz M1 amask _ _ hamask (fv_lt m hI1.t2) h)
      (fun h => Fix.gx_callT1 (ret := ret) hs htail hsz M1 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' => (Fix.gx_tret1 (ret := ret) hs htail hsz M' amask (fv m 0) _ (fv_lt m (by omega))).of_eq
        rfl (by rw [fv_one]))
      (fun h => Fix.gx_callF1 (ret := ret) hs htail hsz M1 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' r hr' => Fix.gx_ret1 (ret := ret) hs htail hsz M' amask _ _ r (by unfold okv; split <;> omega) hr')
    obtain ⟨M3, t3, hI3, c2, hr2, hb2⟩ := gstep hs hr m S hS I hH h6 (k := 2) (by omega) (pc := 13265)
      (pc' := 13317) (rT := 13298) (rF := 13312) (by simp only [Infra.isValidJumpDest_lit])
      (by norm_num) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
      (B := 118) (by norm_num) (by norm_num) (by norm_num) M2 hI2
      (fun h => Fix.gx_skip2 (ret := ret) hs htail hsz M2 amask _ _ hamask (fv_lt m hI2.t2) h)
      (fun h => Fix.gx_callT2 (ret := ret) hs htail hsz M2 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' => (Fix.gx_tret2 (ret := ret) hs htail hsz M' amask (fv m 0) _ (fv_lt m (by omega))).of_eq
        rfl (by rw [fv_one]))
      (fun h => Fix.gx_callF2 (ret := ret) hs htail hsz M2 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' r hr' => Fix.gx_ret2 (ret := ret) hs htail hsz M' amask _ _ r (by unfold okv; split <;> omega) hr')
    obtain ⟨M4, t4, hI4, c3, hr3, hb3⟩ := gstep hs hr m S hS I hH h6 (k := 3) (by omega) (pc := 13317)
      (pc' := 13369) (rT := 13350) (rF := 13364) (by simp only [Infra.isValidJumpDest_lit])
      (by norm_num) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)
      (B := 118) (by norm_num) (by norm_num) (by norm_num) M3 hI3
      (fun h => Fix.gx_skip3 (ret := ret) hs htail hsz M3 amask _ _ hamask (fv_lt m hI3.t2) h)
      (fun h => Fix.gx_callT3 (ret := ret) hs htail hsz M3 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' => (Fix.gx_tret3 (ret := ret) hs htail hsz M' amask (fv m 0) _ (fv_lt m (by omega))).of_eq
        rfl (by rw [fv_one]))
      (fun h => Fix.gx_callF3 (ret := ret) hs htail hsz M3 amask _ _ hamask (fv_lt m (by omega)) h
        (fv_mod2 m (by omega)))
      (fun M' r hr' => Fix.gx_ret3 (ret := ret) hs htail hsz M' amask _ _ r (by unfold okv; split <;> omega) hr')
    have hex := Fix.gx_exit (ret := ret) hs htail hsz M4 amask (fv m t4) (okv amask I 4) hr.jumpdest hret
    refine ⟨M4, fun sl hsl hact => hI4.done sl hsl hact, hI4.ks, hI4.fr, ?_⟩
    rw [call_iff]
    have hb4 : gbud amask 4 M4 t4 ≤ popcnt amask * Gas.fixNo + (Gas.fixSq - Gas.fixNo) + Gas.blkt := by
      have := hI4.t2
      have hc4 : cntA amask 4 = popcnt amask := rfl
      unfold gbud
      rw [hc4]
      have : t4 * Gas.blkt ≤ Gas.blkt := by
        rcases (by omega : t4 = 0 ∨ t4 = 1) with rfl | rfl <;> simp
      split <;> omega
    have hb00 : gbud amask 0 m 0 = 0 := by simp [gbud, cntA, h6]
    exact ((((hpre'.trans hr0).trans hr1).trans hr2).trans hr3 |>.trans hex).mono (by
      simp only [Nat.zero_add, Nat.reduceAdd, hb00] at hb0 hb1 hb2 hb3
      omega)

end MlDsaOpt87.Proofs
