import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Bswap
import MlDsaOpt44.Math.SpongeBits
import MlDsaOpt44.Fn.Sponge
set_option warningAsError true
/-! # Segment `3078 … 3439`: `RHO1` (spread ρ and c̃ lanes, eight `spr` calls).

The byte-swapped calldata word `Y = bswapNet (word cd a)` (`a = 0`, then
`CTOFF`) stays on the stack; its lanes, top first, are spread by `spr` and
stored at `RHO1 + 32 i`: memory after `k` stores is `storeWords m RHO1 (rhoW cd) k`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The mask / multiplier words below `Y`. -/
def rhoK (b : Bool) : List UInt256 :=
  [wd 6277101735386680764176071790128604879584176795969512275969, wd 18446744073709551615, wd 26959946660873538060741835960174461801791452538186943042387869433855, wd 1766820105243087041267848467410591083712559083657179364930612997358944255, wd 450552876409790643671482431940419874915447411150352389258589821042463539455, flag b]

/-- The eight `RHO1` words. -/
def rhoW (cd : ByteArray) (i : Nat) : Nat :=
  if i < 4 then spread (le64 cd (8 * i)) else spread (le64 cd (CTOFF + 8 * (i - 4)))

theorem rhoW_lt (cd : ByteArray) (i : Nat) : rhoW cd i < 2 ^ 256 := by
  unfold rhoW; split <;> exact spread_lt _

theorem lane3_eq {Y : Nat} (h : Y < 2 ^ 256) : Y / 2 ^ 192 = lane Y 3 := by
  unfold lane; omega

theorem laneK_eq (Y k : Nat) : 18446744073709551615 &&& Y / 2 ^ (64 * k) = lane Y k := by
  unfold lane
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]


theorem rho_b0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 3078 [flag b] M)
      (callState s 3247 (wd (bswapNet (word s.executionEnv.calldata 0)) :: rhoK b) M) 120 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008] with [rhoK, bswapNet, bsw8, bsw16, bsw32]

theorem rho_b1 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray) :
    Reach (callState s 3247 (wd Y :: rhoK b) M)
      (callState s 12392 (wd (Y / 2 ^ 192) :: wd 3259 :: wd Y :: rhoK b) M) 26 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1009, 1010, 1011, 1012, 1013, 1014, 1015] with [rhoK]

theorem rho_b6 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (M : ByteArray) :
    Reach (callState s 3362 (wd Y :: rhoK b) M)
      (callState s 12392 (wd (Y / 2 ^ 192) :: wd 3374 :: wd Y :: rhoK b) M) 26 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1089, 1090, 1091, 1092, 1093, 1094, 1095] with [rhoK]

theorem rho_b2 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 0 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3259 (wd (w 0) :: wd Y :: rhoK b) (storeWords m RHO1 w 0))
      (callState s 12392 (wd (18446744073709551615 &&& Y / 2 ^ (64 * 2)) :: wd 3278 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 1)) 39 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027] with [rhoK]
  rfl

theorem rho_b3 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3278 (wd (w 1) :: wd Y :: rhoK b) (storeWords m RHO1 w 1))
      (callState s 12392 (wd (18446744073709551615 &&& Y / 2 ^ (64 * 1)) :: wd 3297 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 2)) 39 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] with [rhoK]
  rfl

theorem rho_b4 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (_hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 2 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3297 (wd (w 2) :: wd Y :: rhoK b) (storeWords m RHO1 w 2))
      (callState s 12392 (wd (18446744073709551615 &&& Y) :: wd 3313 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 3)) 33 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049] with [rhoK]
  rfl

theorem rho_b7 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 4 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3374 (wd (w 4) :: wd Y :: rhoK b) (storeWords m RHO1 w 4))
      (callState s 12392 (wd (18446744073709551615 &&& Y / 2 ^ (64 * 2)) :: wd 3393 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 5)) 39 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107] with [rhoK]
  rfl

theorem rho_b8 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 5 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3393 (wd (w 5) :: wd Y :: rhoK b) (storeWords m RHO1 w 5))
      (callState s 12392 (wd (18446744073709551615 &&& Y / 2 ^ (64 * 1)) :: wd 3412 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 6)) 39 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119] with [rhoK]
  rfl

theorem rho_b9 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (_hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936) (m : ByteArray)
    (w : Nat → Nat) (hw : w 6 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3412 (wd (w 6) :: wd Y :: rhoK b) (storeWords m RHO1 w 6))
      (callState s 12392 (wd (18446744073709551615 &&& Y) :: wd 3428 :: wd Y :: rhoK b)
        (storeWords m RHO1 w 7)) 33 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129] with [rhoK]
  rfl

theorem rho_b5 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (m : ByteArray)
    (w : Nat → Nat) (hw : w 3 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3313 (wd (w 3) :: wd Y :: rhoK b) (storeWords m RHO1 w 3))
      (callState s 3362 (wd (bswapNet (word s.executionEnv.calldata 1312)) :: rhoK b)
        (storeWords m RHO1 w 4)) 114 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088] with [rhoK, bswapNet, bsw8, bsw16, bsw32]
  rfl

theorem rho_b10 {s : State} (hs : Ctx s) (b : Bool) (Y : Nat) (m : ByteArray)
    (w : Nat → Nat) (hw : w 7 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3428 (wd (w 7) :: wd Y :: rhoK b) (storeWords m RHO1 w 7))
      (callState s 3439 [flag b] (storeWords m RHO1 w 8)) 19 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138] with [rhoK]
  rfl

theorem lane0_eq (Y : Nat) : 18446744073709551615 &&& Y = lane Y 0 := by
  have := laneK_eq Y 0; simpa using this

theorem rhoW_lo (cd : ByteArray) {k : Nat} (hk : k < 4) : rhoW cd k = spread (le64 cd (8 * k)) := by
  unfold rhoW; rw [if_pos hk]

theorem rhoW_hi (cd : ByteArray) {k : Nat} (hk : k < 4) :
    rhoW cd (4 + k) = spread (le64 cd (CTOFF + 8 * k)) := by
  unfold rhoW; rw [if_neg (by omega), show 4 + k - 4 = k by omega]

theorem seg_rho_proof {s : State} (hs : Ctx s) {m : ByteArray}
    (hI : Inv3 s.executionEnv.calldata m) (b : Bool) :
    ∃ m', Inv4 s.executionEnv.calldata m' ∧
      Reach (callState s 3078 [flag b] m) (callState s 3439 [flag b] m') Gas.pRho := by
  generalize hcd : s.executionEnv.calldata = cd at hI
  have hY0 := bswapNet_lt (word cd 0)
  have hY1 := bswapNet_lt (word cd 1312)
  have hW : ∀ k, rhoW cd k < 2 ^ 256 := rhoW_lt cd
  have hr : ∀ (r : Nat) (Y : Nat), Decode.isValidJumpDest MlDsaOpt44.optBytecode r = true →
      r < 2 ^ 16 → RetOK Stack.spr r (wd Y :: rhoK b) := fun r Y hj hl =>
    retOK_main (by decide) (by simp [rhoK]) hj hl
  -- lanes of the two byte-swapped words
  have l0 : ∀ k, k < 4 → lane (bswapNet (word cd 0)) (3 - k) = le64 cd (8 * k) := fun k hk => by
    rw [lane_bswapNet cd 0 (by omega)]; congr 1; omega
  have l1 : ∀ k, k < 4 → lane (bswapNet (word cd 1312)) (3 - k) = le64 cd (CTOFF + 8 * k) :=
    fun k hk => by rw [lane_bswapNet cd 1312 (by omega)]; unfold CTOFF; congr 1; omega
  have e0 : spread (bswapNet (word cd 0) / 2 ^ 192) = rhoW cd 0 := by
    rw [lane3_eq hY0, rhoW_lo cd (by omega), ← l0 0 (by omega)]
  have e1 : spread (18446744073709551615 &&& bswapNet (word cd 0) / 2 ^ (64 * 2)) = rhoW cd 1 := by
    rw [laneK_eq, rhoW_lo cd (by omega), ← l0 1 (by omega)]
  have e2 : spread (18446744073709551615 &&& bswapNet (word cd 0) / 2 ^ (64 * 1)) = rhoW cd 2 := by
    rw [laneK_eq, rhoW_lo cd (by omega), ← l0 2 (by omega)]
  have e3 : spread (18446744073709551615 &&& bswapNet (word cd 0)) = rhoW cd 3 := by
    rw [lane0_eq, rhoW_lo cd (by omega), ← l0 3 (by omega)]
  have e4 : spread (bswapNet (word cd 1312) / 2 ^ 192) = rhoW cd 4 := by
    rw [lane3_eq hY1, rhoW_hi cd (k := 0) (by omega), ← l1 0 (by omega)]
  have e5 : spread (18446744073709551615 &&& bswapNet (word cd 1312) / 2 ^ (64 * 2)) = rhoW cd 5 := by
    rw [laneK_eq, rhoW_hi cd (k := 1) (by omega), ← l1 1 (by omega)]
  have e6 : spread (18446744073709551615 &&& bswapNet (word cd 1312) / 2 ^ (64 * 1)) = rhoW cd 6 := by
    rw [laneK_eq, rhoW_hi cd (k := 2) (by omega), ← l1 2 (by omega)]
  have e7 : spread (18446744073709551615 &&& bswapNet (word cd 1312)) = rhoW cd 7 := by
    rw [lane0_eq, rhoW_hi cd (k := 3) (by omega), ← l1 3 (by omega)]
  subst hcd
  let Y0 := bswapNet (word s.executionEnv.calldata 0)
  let Y1 := bswapNet (word s.executionEnv.calldata 1312)
  let W := rhoW s.executionEnv.calldata
  have c0 := spr_call hs (hr 3259 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 0) (v := Y0 / 2 ^ 192) (by omega)
  have c1 := spr_call hs (hr 3278 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 1) (v := 18446744073709551615 &&& Y0 / 2 ^ (64 * 2)) (by rw [laneK_eq]; unfold lane; omega)
  have c2 := spr_call hs (hr 3297 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 2) (v := 18446744073709551615 &&& Y0 / 2 ^ (64 * 1)) (by rw [laneK_eq]; unfold lane; omega)
  have c3 := spr_call hs (hr 3313 Y0 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 3) (v := 18446744073709551615 &&& Y0) (by rw [lane0_eq]; unfold lane; omega)
  have c4 := spr_call hs (hr 3374 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 4) (v := Y1 / 2 ^ 192) (by omega)
  have c5 := spr_call hs (hr 3393 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 5) (v := 18446744073709551615 &&& Y1 / 2 ^ (64 * 2)) (by rw [laneK_eq]; unfold lane; omega)
  have c6 := spr_call hs (hr 3412 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 6) (v := 18446744073709551615 &&& Y1 / 2 ^ (64 * 1)) (by rw [laneK_eq]; unfold lane; omega)
  have c7 := spr_call hs (hr 3428 Y1 (by simp only [isValidJumpDest_lit]) (by norm_num))
    (storeWords m RHO1 W 7) (v := 18446744073709551615 &&& Y1) (by rw [lane0_eq]; unfold lane; omega)
  rw [call_iff, e0] at c0
  rw [call_iff, e1] at c1
  rw [call_iff, e2] at c2
  rw [call_iff, e3] at c3
  rw [call_iff, e4] at c4
  rw [call_iff, e5] at c5
  rw [call_iff, e6] at c6
  rw [call_iff, e7] at c7
  have h := (rho_b0 hs b m).trans ((rho_b1 hs b Y0 hY0 _).trans (c0.trans
    ((rho_b2 hs b Y0 hY0 m W (hW 0)).trans (c1.trans
    ((rho_b3 hs b Y0 hY0 m W (hW 1)).trans (c2.trans
    ((rho_b4 hs b Y0 hY0 m W (hW 2)).trans (c3.trans
    ((rho_b5 hs b Y0 m W (hW 3)).trans ((rho_b6 hs b Y1 hY1 _).trans (c4.trans
    ((rho_b7 hs b Y1 hY1 m W (hW 4)).trans (c5.trans
    ((rho_b8 hs b Y1 hY1 m W (hW 5)).trans (c6.trans
    ((rho_b9 hs b Y1 hY1 m W (hW 6)).trans (c7.trans
    (rho_b10 hs b Y1 m W (hW 7)))))))))))))))))))
  have hfr : FrameExcept m (storeWords m RHO1 W 8) [(RHO1, RHO1 + 256)] :=
    FrameExcept.storeWords m RHO1 W 8
  refine ⟨storeWords m RHO1 W 8,
    ⟨⟨hI.rc4.frame hfr (by avoids_tac), hI.rc1.frame hfr (by avoids_tac),
      hI.tbl.frame hfr (by avoids_tac), hI.zhat.frame hfr (by avoids_tac),
      hI.hp.frame hfr (by avoids_tac), hI.zMisc.frame hfr (by avoids_tac),
      hI.zCw.frame hfr (by avoids_tac), hI.zHigh.frame hfr (by avoids_tac)⟩,
      fun x hx => ⟨?_, ?_⟩⟩, h.mono (by unfold Gas.pRho; omega)⟩
  · rw [word_storeWords (hW x) 8 (by omega), rhoW_lo _ hx]
  · rw [word_storeWords (hW (4 + x)) 8 (by omega), rhoW_hi _ hx]

end MlDsaOpt44.Proofs
