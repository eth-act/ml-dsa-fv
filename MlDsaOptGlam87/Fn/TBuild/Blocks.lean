import MlDsaOpt44.Fn.Ct.TBuildMath
import MlDsaOptGlam87.Budget
import MlDsaOptGlam87.Layout
/- Ported from `MlDsaOpt87/Fn/TBuild/Blocks.lean` by `scripts/proofgen_port.py --glam 87`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
/- Ported from `MlDsaOpt44/Fn/Ct/TBuildBlocks.lean` by `scripts/proofgen_port.py 87`, generalised as the 65 file; hand adjustments are marked `-- port:`. -/
set_option maxHeartbeats 0  -- port: re-elaboration headroom
set_option warningAsError true
set_option linter.unusedSimpArgs false
/-!
# `tbuild`: straight-line blocks, generalised to the table pointer `T` (port)

-- port: the 44 lemmas fix `TT = 20480`, `end = 22688` and the clamp offsets; here the table
pointer `T`, the end `E = T + 2208` and the calldata offset `off` are free (65/87 call
`tbuild` with `(0x5000, 32)` and `(0x6800, 0x520)`). The shapes `tgW … tbN`, `st3` are the
44 definitions (`MlDsaOpt44.Proofs.TB`).

Loop heads: `20626` (chunk loop, stack `pa, T, off, E, ret`) and `21017` (word loop,
stack `sh, V3, V2, V1, V0, pa, …`).
-/

namespace MlDsaOptGlam87.Proofs.TB

open MlDsaOpt87.Proofs

open MlDsaOpt44.Proofs.TB
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK SP TOP TRL Z0 aD aOf azRow cD cOf cStream ctOf finBytes hintD hintOf memWords mlenOf msgOf muOf okA okC okH okZ optAccepts pkOf rawZ rhoOf sigOf spOff t1Of t1v trOf w1Of wRow zHat zHi zLane zLo zPolys

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

section
variable {s : State} {ret : Nat} {tail : List UInt256} {T E : Nat}

theorem tb_pro (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {off : Nat} :
    Reach (callState s 20613 (wd T :: wd off :: wd ret :: tail) M)
      (callState s 20626 (wd (T + 4064) :: wd T :: wd off :: wd (T + 2208) :: wd ret :: tail) M) 25 := by
  glam87_rreach [8938, 8939, 8940, 8941, 8942, 8943, 8944, 8945, 8946] with [Nat.add_comm _ T]  -- port: symbolic `T`

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 20626 (wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 20807 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 172 := by
  glam87_rreach [8947, 8948, 8949, 8950, 8951, 8952, 8953, 8954, 8955, 8956, 8957, 8958, 8959, 8960, 8961, 8962, 8963, 8964, 8965, 8966, 8967, 8968, 8969, 8970, 8971, 8972, 8973, 8974, 8975, 8976, 8977, 8978, 8979, 8980, 8981, 8982, 8983, 8984, 8985, 8986, 8987, 8988, 8989, 8990, 8991, 8992, 8993, 8994, 8995, 8996, 8997, 8998, 8999, 9000, 9001, 9002, 9003, 9004] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 20807 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 20874 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  glam87_rreach [9005, 9006, 9007, 9008, 9009, 9010, 9011, 9012, 9013, 9014, 9015, 9016, 9017, 9018, 9019, 9020, 9021, 9022, 9023, 9024, 9025, 9026, 9027, 9028, 9029, 9030, 9031, 9032, 9033, 9034, 9035, 9036, 9037, 9038, 9039, 9040, 9041, 9042, 9043, 9044, 9045, 9046, 9047, 9048, 9049, 9050, 9051, 9052, 9053, 9054, 9055, 9056, 9057, 9058, 9059] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 20874 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 20941 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  glam87_rreach [9060, 9061, 9062, 9063, 9064, 9065, 9066, 9067, 9068, 9069, 9070, 9071, 9072, 9073, 9074, 9075, 9076, 9077, 9078, 9079, 9080, 9081, 9082, 9083, 9084, 9085, 9086, 9087, 9088, 9089, 9090, 9091, 9092, 9093, 9094, 9095, 9096, 9097, 9098, 9099, 9100, 9101, 9102, 9103, 9104, 9105, 9106, 9107, 9108, 9109, 9110, 9111, 9112, 9113, 9114] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 20941 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 21017 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 187 := by
  glam87_rreach [9115, 9116, 9117, 9118, 9119, 9120, 9121, 9122, 9123, 9124, 9125, 9126, 9127, 9128, 9129, 9130, 9131, 9132, 9133, 9134, 9135, 9136, 9137, 9138, 9139, 9140, 9141, 9142, 9143, 9144, 9145, 9146, 9147, 9148, 9149, 9150, 9151, 9152, 9153, 9154, 9155, 9156, 9157, 9158, 9159, 9160, 9161, 9162, 9163, 9164, 9165, 9166, 9167, 9168, 9169, 9170, 9171, 9172, 9173, 9174, 9175, 9176, 9177, 9178] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 21017 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 21275 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 214 := by
  glam87_rreach [9179, 9180, 9181, 9182, 9183, 9184, 9185, 9186, 9187, 9188, 9189, 9190, 9191, 9192, 9193, 9194, 9195, 9196, 9197, 9198, 9199, 9200, 9201, 9202, 9203, 9204, 9205, 9206, 9207, 9208, 9209, 9210, 9211, 9212, 9213, 9214, 9215, 9216, 9217, 9218, 9219, 9220, 9221, 9222, 9223, 9224, 9225, 9226, 9227, 9228, 9229, 9230, 9231, 9232, 9233, 9234, 9235, 9236, 9237, 9238, 9239, 9240, 9241, 9242, 9243, 9244, 9245, 9246, 9247, 9248, 9249, 9250] with [tbW, tdsw, ts2, ts1, tgW]

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 91680) :
    Reach (callState s 21275 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 21017 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [9251, 9252, 9253, 9254, 9255, 9256, 9257, 9258, 9259, 9260, 9261, 9262, 9263, 9264, 9265, 9266, 9267, 9268, 9269, 9270, 9271, 9272, 9273, 9274, 9275, 9276, 9277] with [TB.st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 91680) :
    Reach (callState s 21275 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 21343 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  glam87_rreach [9251, 9252, 9253, 9254, 9255, 9256, 9257, 9258, 9259, 9260, 9261, 9262, 9263, 9264, 9265, 9266, 9267, 9268, 9269, 9270, 9271, 9272, 9273, 9274, 9275, 9276, 9277] with [TB.st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ E - 192) (hle : E ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) (hE : 192 ≤ E) :
    Reach (callState s 21343 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 20626 (wd pa :: wd T :: wd (30 + off) :: wd E :: wd ret :: tail) M) 90 := by
  glam87_rreach [9278, 9279, 9280, 9281, 9282, 9283, 9284, 9285, 9286, 9287, 9288, 9289, 9290, 9291, 9292, 9293, 9294, 9295, 9296, 9297, 9298, 9299, 9300, 9307, 9308, 9309]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 off : Nat}
    (hE : 192 ≤ E) (hE2 : E < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 21343 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 64) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 20626 (wd E :: wd T :: wd (20 + off) :: wd E :: wd ret :: tail) M) 107 := by
  glam87_rreach [9278, 9279, 9280, 9281, 9282, 9283, 9284, 9285, 9286, 9287, 9288, 9289, 9290, 9291, 9292, 9293, 9294, 9295, 9296, 9297, 9298, 9299, 9300, 9301, 9302, 9303, 9304, 9305, 9306, 9307, 9308, 9309]
  exact ofNat_eq_ofNat_iff.mpr (by omega)  -- port: symbolic `off`

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOptGlam87.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 off : Nat} (hE : 192 ≤ E) (hE2 : E < 2 ^ 64)
    (_hoff : off < 2 ^ 64) :
    Reach (callState s 21343 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 192) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  glam87_rreach [9278, 9279, 9280, 9281, 9282, 9283, 9284, 9285, 9286, 9287, 9288, 9289, 9290, 9310, 9311, 9312, 9313, 9314, 9315] with [hj]

end

end MlDsaOptGlam87.Proofs.TB
