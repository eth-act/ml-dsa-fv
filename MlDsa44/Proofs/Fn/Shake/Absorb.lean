import MlDsa44.Proofs.Fn.Shake.Squeeze
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# The absorb phase of `shake` (instructions 1680‥1802)

`absorb_phase`: zero the lanes and absorb the `len / rate` full blocks read
directly from memory at `ptr`. `pad_phase`: build the padded final block at
`PADB`, absorb it, and arrive at the squeeze loop.
-/

namespace MlDsa44.Proofs.Shake

open EvmSemantics
open EvmSemantics.EVM
open EvmSemantics.Crypto

theorem frame_write1 (m : ByteArray) (x : UInt8) (a : Nat) :
    FrameExcept m (MachineState.writeBytes m (ByteArray.mk #[x]) a) [(a, a + 1)] :=
  Infra.FrameExcept.writeBytes m _ a

theorem frame_copy (m m' : ByteArray) (src n a : Nat) :
    FrameExcept m (MachineState.writeBytes m (MachineState.readPadded m' src n) a)
      [(a, a + n)] := by
  have := Infra.FrameExcept.writeBytes m (MachineState.readPadded m' src n) a
  rwa [EvmProof.Memory.readPadded_size] at this

theorem absorb_phase {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {m : ByteArray} (hrc : RCTable m)
    {rate ptr len out blocks : Nat} (hrate : rate = 136 ∨ rate = 168) (hin : ZETA ≤ ptr)
    (hmem : ptr + len + 32 ≤ 32 * s.activeWords.toNat) {padded : ByteArray}
    (hpad : ∀ i, i < len / rate * rate → byteAt padded i = byteAt m (ptr + i)) :
    ∃ M, LanesAt M ST (absorbPre rate padded (len / rate)) ∧ RCTable M ∧
      FrameExcept m M [(ST, RC)] ∧
      Infra.Reach
        (callState s 2680 (wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) m)
        (callState s 2714 (wd (len / rate) :: wd (len / rate) ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (1670 + len / rate * (101 + Gas.xorBlock rate + Gas.keccakF)) := by
  have htail : tail.length ≤ 768 := by have := hr.depth; rw [stack_shake] at this; omega
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hrb : 0 < rate ∧ rate < 256 := by omega
  have hlen : len < 2 ^ 128 := by omega
  have hr8 := rate_div8 hrate
  simp only [ZETA] at hin
  -- zero the 25 lanes
  have h0 := b_entry hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret) m
  have hz := Infra.Reach.loop
    (I := fun i => callState s 2682
      (wd i :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
      (Infra.storeWords m 0 (fun _ => 0) i)) 25
    (fun i hi => b_zero hs htail hfw haw m i hi)
  have hze := b_zeroExit hs htail hrb hlen (ptr := ptr) (out := out) (blocks := blocks)
    (ret := ret) (Infra.storeWords m 0 (fun _ => 0) 25)
  have hstart := (h0.trans (hz.of_eq (by simp) rfl)).trans hze
  -- the zeroed lanes
  have hF0 := Infra.FrameExcept.storeWords m 0 (fun _ => 0) 25
  have hL0 : LanesAt (Infra.storeWords m 0 (fun _ => 0) 25) ST Fips202.emptyState := by
    refine ⟨by simp [Fips202.emptyState], fun i hi => ?_⟩
    rw [show ST + 32 * i = 0 + 32 * i by rfl, Infra.word_storeWords (by norm_num) 25 hi]
    simp [Fips202.emptyState, hi]
  have hrc0 : RCTable (Infra.storeWords m 0 (fun _ => 0) 25) := Infra.RCTable.frame hrc hF0 (by
    simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC]; omega)
  -- the full blocks
  have hloop : ∀ b, b ≤ len / rate → ∃ M, LanesAt M ST (absorbPre rate padded b) ∧ RCTable M ∧
      FrameExcept m M [(ST, RC)] ∧
      Infra.Reach
        (callState s 2680 (wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) m)
        (callState s 2714 (wd b :: wd (len / rate) ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (1670 + b * (101 + Gas.xorBlock rate + Gas.keccakF)) := by
    intro b
    induction b with
    | zero =>
      intro _
      exact ⟨_, hL0, hrc0, frame_cover hF0 (by frame_omega),
        hstart.mono (Nat.le_of_eq (by ring))⟩
    | succ b ih =>
      intro hb
      obtain ⟨M, hL, hrcM, hF, hR⟩ := ih (by omega)
      have hdl : len / rate * rate ≤ len := Nat.div_mul_le_self len rate
      have hbr : (b + 1) * rate ≤ len / rate * rate := Nat.mul_le_mul_right _ hb
      have hsucc : (b + 1) * rate = b * rate + rate := Nat.succ_mul b rate
      have hdiv : len / rate ≤ len := Nat.div_le_self len rate
      have h1 := b_absorb1 hs htail hlen (rate := rate) (ptr := ptr) (out := out) (blocks := blocks)
        (ret := ret) M (b := b) (full := len / rate) (by omega) hdiv
      obtain ⟨M1, hL1, hF1, hC1⟩ := xorBlock_call hs (p := ptr + b * rate)
        (hr.callee (B' := Stack.xorBlock) (ret' := 2736)
          (extra := [wd b, wd (len / rate), wd rate, wd ptr, wd len, wd out, wd blocks, wd ret])
          (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
        hrate hL (by simp only [RC]; omega) (by omega)
      have hrc1 : RCTable M1 := Infra.RCTable.frame hrcM hF1 (by
        simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)
      have h2 := b_absorb2 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
        (blocks := blocks) (ret := ret) M1 b (len / rate)
      obtain ⟨M2, hL2, hF2, hC2⟩ := keccakF_call hs
        (hr.callee (B' := Stack.keccakF) (ret' := 2744)
          (extra := [wd b, wd (len / rate), wd rate, wd ptr, wd len, wd out, wd blocks, wd ret])
          (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
        hL1 hrc1
      have hrc2 : RCTable M2 := Infra.RCTable.frame hrc1 hF2 (by
        simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)
      have h3 := b_absorb3 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
        (blocks := blocks) (ret := ret) M2 b (len / rate)
      have hxor : Fips202.xorBlock rate M (ptr + b * rate) (absorbPre rate padded b) =
          Fips202.xorBlock rate padded (b * rate) (absorbPre rate padded b) := by
        apply xorBlock_congr
        intro i hi
        rw [Infra.FrameExcept.byteAt hF
          (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega),
          hpad _ (by omega), Nat.add_assoc]
      rw [hxor, ← absorbPre_succ] at hL2
      refine ⟨M2, hL2, hrc2, frame_cover (Infra.FrameExcept.trans
        (Infra.FrameExcept.trans hF hF1) hF2) (by frame_omega), ?_⟩
      have hc1 := (Infra.call_iff.mp hC1).of_eq
        (s' := callState s 2621 (wd rate :: wd (ptr + b * rate) :: wd 2736 :: wd b ::
          wd (len / rate) :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret ::
          tail) M)
        (t' := callState s 2736 (wd b :: wd (len / rate) :: wd rate :: wd ptr :: wd len ::
          wd out :: wd blocks :: wd ret :: tail) M1)
        (by simp [Entry.xorBlock]) (by simp)
      have hc2 := (Infra.call_iff.mp hC2).of_eq
        (s' := callState s 4 (wd 2744 :: wd b :: wd (len / rate) :: wd rate :: wd ptr ::
          wd len :: wd out :: wd blocks :: wd ret :: tail) M1)
        (t' := callState s 2744 (wd b :: wd (len / rate) :: wd rate :: wd ptr :: wd len ::
          wd out :: wd blocks :: wd ret :: tail) M2)
        (by simp [Entry.keccakF]) (by simp)
      exact (hR.trans (h1.trans (hc1.trans (h2.trans (hc2.trans h3))))).mono
        (Nat.le_of_eq (by ring))
  exact hloop (len / rate) le_rfl

/-- Bytes of the padded block built at `PADB`. -/
theorem padBlock_bytes {m M : ByteArray} {rate ptr len : Nat} (hrate : rate = 136 ∨ rate = 168)
    (hin : ZETA ≤ ptr) (hinPad : ptr + len ≤ PADB ∨ PADB + 192 ≤ ptr)
    (hF : FrameExcept m M [(ST, RC)]) (i : Nat) (hi : i < rate) :
    byteAt (padMem4 (MachineState.writeBytes (Infra.storeWords M 78464 (fun _ => 0) 6)
        (MachineState.readPadded (Infra.storeWords M 78464 (fun _ => 0) 6)
          (ptr + len / rate * rate) (len - len / rate * rate)) 78464)
        (len - len / rate * rate) rate) (78464 + i) =
      byteAt (Fips202.pad rate 0x1F (MachineState.readPadded m ptr len)) (len / rate * rate + i) := by
  have hrp : 0 < rate := by omega
  have hmd := Nat.mod_add_div len rate
  have hml := Nat.mod_lt len hrp
  have hc : rate * (len / rate) = len / rate * rate := Nat.mul_comm _ _
  have hsz := EvmProof.Memory.readPadded_size m ptr len
  have hspec := byteAt_pad_last rate (MachineState.readPadded m ptr len) hrp i hi
  rw [hsz] at hspec
  rw [hspec]
  simp only [ZETA, PADB] at hin hinPad
  -- the zeroed / copied block
  have hM2 : ∀ k, k < 192 → byteAt (MachineState.writeBytes
      (Infra.storeWords M 78464 (fun _ => 0) 6)
      (MachineState.readPadded (Infra.storeWords M 78464 (fun _ => 0) 6)
        (ptr + len / rate * rate) (len - len / rate * rate)) 78464) (78464 + k) =
      if k < len % rate then byteAt m (ptr + (len / rate * rate + k)) else 0 := by
    intro k hk
    rw [Infra.byteAt_writeBytes, EvmProof.Memory.readPadded_size]
    by_cases hkr : k < len % rate
    · rw [if_pos (by omega), if_pos hkr, show 78464 + k - 78464 = k by omega, byteAt_readPadded,
        if_pos (by omega), byteAt_storeWords_zero, if_neg (by omega),
        Infra.FrameExcept.byteAt hF
          (by simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega),
        Nat.add_assoc]
    · rw [if_neg (by omega), if_neg hkr, byteAt_storeWords_zero, if_pos (by omega)]
  have hrem : len - len / rate * rate = len % rate := by omega
  unfold padMem4 padMem3
  rw [byteAt_write1, byteAt_write1, byteAt_write1, hM2 _ (by omega), hM2 _ (by omega),
    byteAt_readPadded, hrem]
  simp only [UInt8.toNat_ofNat', Nat.mod_mod]
  split_ifs <;> first | rfl | omega

theorem pad_phase {s : State} (hs : Ctx s) {ret : Nat} {tail : List UInt256}
    (hr : RetOK Stack.shake ret tail) {m M : ByteArray} {rate ptr len out blocks : Nat}
    (hrate : rate = 136 ∨ rate = 168) (hin : ZETA ≤ ptr)
    (hinPad : ptr + len ≤ PADB ∨ PADB + 192 ≤ ptr)
    (hmem : ptr + len + 32 ≤ 32 * s.activeWords.toNat) {A : Fips202.SpongeState}
    (hL : LanesAt M ST A) (hrc : RCTable M) (hF : FrameExcept m M [(ST, RC)]) :
    ∃ M', LanesAt M' ST (Keccak.permute (Fips202.xorBlock rate
        (Fips202.pad rate 0x1F (MachineState.readPadded m ptr len)) (len / rate * rate) A)) ∧
      RCTable M' ∧ FrameExcept M M' [(PADB, PADB + 192), (ST, RC)] ∧
      Infra.Reach
        (callState s 2714 (wd (len / rate) :: wd (len / rate) ::
          wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail) M)
        (callState s 2856 (wd 0 :: wd (78464 + (rate - 1)) :: wd (len - len / rate * rate) ::
          wd (len / rate) :: wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret ::
          tail) M')
        (48 + 6 * 71 + 52 + (3 + 3 * ((len % rate + 31) / 32)) + 73 + Gas.xorBlock rate + 15 +
          Gas.keccakF + 3) := by
  have htail : tail.length ≤ 768 := by have := hr.depth; rw [stack_shake] at this; omega
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hrb : 0 < rate ∧ rate < 256 := by omega
  have hlen : len < 2 ^ 128 := by omega
  have hrp : 0 < rate := by omega
  have hmd := Nat.mod_add_div len rate
  have hml := Nat.mod_lt len hrp
  have hc : rate * (len / rate) = len / rate * rate := Nat.mul_comm _ _
  have hrem : len - len / rate * rate = len % rate := by omega
  have hdiv : len / rate ≤ len := Nat.div_le_self len rate
  have hzp : ZETA ≤ ptr := hin
  simp only [ZETA] at hzp
  -- absorb exit and the six zero words at PADB
  have h1 := b_absorbExit hs htail hlen (rate := rate) (ptr := ptr) (out := out)
    (blocks := blocks) (ret := ret) M (full := len / rate) (by omega) hdiv
  have hz := Infra.Reach.loop
    (I := fun i => callState s 2763 (wd i :: wd (len - len / rate * rate) :: wd (len / rate) ::
      wd rate :: wd ptr :: wd len :: wd out :: wd blocks :: wd ret :: tail)
      (Infra.storeWords M 78464 (fun _ => 0) i)) 6
    (fun i hi => b_padZero hs htail hfw haw M (len - len / rate * rate) (len / rate) i hi)
  have h2 := b_padExit hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret) (Infra.storeWords M 78464 (fun _ => 0) 6)
    (len - len / rate * rate) (len / rate)
  have h3 := reach_mcopy hs (dst := 78464) (src := ptr + len / rate * rate)
    (sz := len - len / rate * rate)
    (rest := wd (len - len / rate * rate) :: wd (len / rate) :: wd rate :: wd ptr :: wd len ::
      wd out :: wd blocks :: wd ret :: tail) (m := Infra.storeWords M 78464 (fun _ => 0) 6)
    (by simp; omega) (by omega) (by omega)
  have h4 := b_padBytes hs htail hfw haw hrb (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret)
    (MachineState.writeBytes (Infra.storeWords M 78464 (fun _ => 0) 6)
      (MachineState.readPadded (Infra.storeWords M 78464 (fun _ => 0) 6)
        (ptr + len / rate * rate) (len - len / rate * rate)) 78464)
    (len - len / rate * rate) (len / rate) (by omega)
  -- memory frames of the padding
  have hFp : FrameExcept M (padMem4 (MachineState.writeBytes
      (Infra.storeWords M 78464 (fun _ => 0) 6)
      (MachineState.readPadded (Infra.storeWords M 78464 (fun _ => 0) 6)
        (ptr + len / rate * rate) (len - len / rate * rate)) 78464)
      (len - len / rate * rate) rate) [(PADB, PADB + 192)] := by
    unfold padMem4 padMem3
    exact frame_cover (Infra.FrameExcept.trans (Infra.FrameExcept.trans (Infra.FrameExcept.trans
      (Infra.FrameExcept.storeWords M 78464 (fun _ => 0) 6) (frame_copy _ _ _ _ _))
      (frame_write1 _ _ _)) (frame_write1 _ _ _)) (by frame_omega)
  have hLp := Infra.LanesAt.frame hL hFp (by
    simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, PADB, ST]; omega)
  have hrcp := Infra.RCTable.frame hrc hFp (by
    simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, PADB, RC]; omega)
  obtain ⟨M5, hL5, hF5, hC5⟩ := xorBlock_call hs (p := 78464)
    (hr.callee (B' := Stack.xorBlock) (ret' := 2846)
      (extra := [wd (78464 + (rate - 1)), wd (len - len / rate * rate), wd (len / rate), wd rate,
        wd ptr, wd len, wd out, wd blocks, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    hrate hLp (by simp only [RC]; omega) (by omega)
  have hrc5 : RCTable M5 := Infra.RCTable.frame hrcp hF5 (by
    simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)
  have h5 := b_pad2 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret) M5 (78464 + (rate - 1)) (len - len / rate * rate) (len / rate)
  obtain ⟨M6, hL6, hF6, hC6⟩ := keccakF_call hs
    (hr.callee (B' := Stack.keccakF) (ret' := 2854)
      (extra := [wd (78464 + (rate - 1)), wd (len - len / rate * rate), wd (len / rate), wd rate,
        wd ptr, wd len, wd out, wd blocks, wd ret])
      (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num))
    hL5 hrc5
  have h6 := b_pad3 hs htail (rate := rate) (ptr := ptr) (len := len) (out := out)
    (blocks := blocks) (ret := ret) M6 (78464 + (rate - 1)) (len - len / rate * rate) (len / rate)
  have hxor : Fips202.xorBlock rate (padMem4 (MachineState.writeBytes
      (Infra.storeWords M 78464 (fun _ => 0) 6)
      (MachineState.readPadded (Infra.storeWords M 78464 (fun _ => 0) 6)
        (ptr + len / rate * rate) (len - len / rate * rate)) 78464)
      (len - len / rate * rate) rate) 78464 A =
      Fips202.xorBlock rate (Fips202.pad rate 0x1F (MachineState.readPadded m ptr len))
        (len / rate * rate) A := by
    apply xorBlock_congr
    intro i hi
    exact padBlock_bytes hrate hin hinPad hF i (by omega)
  rw [hxor] at hL5
  have hrc6 : RCTable M6 := Infra.RCTable.frame hrc5 hF6 (by
    simp only [Infra.avoids_cons, Infra.avoids_nil, and_true, RC, ST]; omega)
  rw [hxor] at hL6
  refine ⟨M6, hL6, hrc6, frame_cover (Infra.FrameExcept.trans
    (Infra.FrameExcept.trans hFp hF5) hF6) (by frame_omega), ?_⟩
  have hc5 := Infra.call_iff.mp hC5
  have hc6 := Infra.call_iff.mp hC6
  exact (h1.trans ((hz.of_eq (by simp) rfl).trans (h2.trans (h3.trans (h4.trans
    ((hc5.of_eq (by simp [Entry.xorBlock]) (by simp)).trans
    (h5.trans ((hc6.of_eq (by simp [Entry.keccakF]) (by simp)).trans h6)))))))).mono
    (Nat.le_of_eq (by rw [hrem]; ring))

end MlDsa44.Proofs.Shake
