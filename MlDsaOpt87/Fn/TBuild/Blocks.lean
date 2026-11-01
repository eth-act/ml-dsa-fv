import MlDsaOpt44.Fn.Ct.TBuildMath
import MlDsaOpt87.Budget
import MlDsaOpt87.Layout
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

Loop heads: `15377` (chunk loop, stack `pa, T, off, E, ret`) and `15768` (word loop,
stack `sh, V3, V2, V1, V0, pa, …`).
-/

namespace MlDsaOpt87.Proofs.TB

open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.TB

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsaOpt44.Proofs.DecodeZ

section
variable {s : State} {ret : Nat} {tail : List UInt256} {T E : Nat}

theorem tb_pro (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {off : Nat} :
    Reach (callState s 15364 (wd T :: wd off :: wd ret :: tail) M)
      (callState s 15377 (wd (T + 4064) :: wd T :: wd off :: wd (T + 2208) :: wd ret :: tail) M) 25 := by
  opt87_reach [6828, 6829, 6830, 6831, 6832, 6833, 6834, 6835, 6836]
  exact ⟨by rw [Nat.add_comm], by rw [Nat.add_comm]⟩  -- port: symbolic `T`

theorem tb_l0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15377 (wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15558 (wd (leNat s.executionEnv.calldata off 32) ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 172 := by
  opt87_reach [6837, 6838, 6839, 6840, 6841, 6842, 6843, 6844, 6845, 6846, 6847, 6848, 6849, 6850, 6851, 6852, 6853, 6854, 6855, 6856, 6857, 6858, 6859, 6860, 6861, 6862, 6863, 6864, 6865, 6866, 6867, 6868, 6869, 6870, 6871, 6872, 6873, 6874, 6875, 6876, 6877, 6878, 6879, 6880, 6881, 6882, 6883, 6884, 6885, 6886, 6887, 6888, 6889, 6890, 6891, 6892, 6893, 6894] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15558 (wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15625 (wd (leNat s.executionEnv.calldata (320 + off) 32) :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt87_reach [6895, 6896, 6897, 6898, 6899, 6900, 6901, 6902, 6903, 6904, 6905, 6906, 6907, 6908, 6909, 6910, 6911, 6912, 6913, 6914, 6915, 6916, 6917, 6918, 6919, 6920, 6921, 6922, 6923, 6924, 6925, 6926, 6927, 6928, 6929, 6930, 6931, 6932, 6933, 6934, 6935, 6936, 6937, 6938, 6939, 6940, 6941, 6942, 6943, 6944, 6945, 6946, 6947, 6948, 6949] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15625 (wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15692 (wd (leNat s.executionEnv.calldata (640 + off) 32) :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 165 := by
  opt87_reach [6950, 6951, 6952, 6953, 6954, 6955, 6956, 6957, 6958, 6959, 6960, 6961, 6962, 6963, 6964, 6965, 6966, 6967, 6968, 6969, 6970, 6971, 6972, 6973, 6974, 6975, 6976, 6977, 6978, 6979, 6980, 6981, 6982, 6983, 6984, 6985, 6986, 6987, 6988, 6989, 6990, 6991, 6992, 6993, 6994, 6995, 6996, 6997, 6998, 6999, 7000, 7001, 7002, 7003, 7004] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_l3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {pa off V0 V1 V2 : Nat}
    (hoff : off < 2 ^ 64) :
    Reach (callState s 15692 (wd V2 :: wd V1 :: wd V0 ::
        wd 6277101735386680763495507056286727952657427581105975853055 ::
        wd 26959946660873538060741835960174461801791452538186943042387869433855 ::
        wd 1766820105243087041267848467410591083712559083657179364930612997358944255 ::
        wd 450552876409790643671482431940419874915447411150352389258589821042463539455 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15768 (wd 0 :: wd (leNat s.executionEnv.calldata (960 + off) 32) :: wd V2 :: wd V1 :: wd V0 ::
        wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 187 := by
  opt87_reach [7005, 7006, 7007, 7008, 7009, 7010, 7011, 7012, 7013, 7014, 7015, 7016, 7017, 7018, 7019, 7020, 7021, 7022, 7023, 7024, 7025, 7026, 7027, 7028, 7029, 7030, 7031, 7032, 7033, 7034, 7035, 7036, 7037, 7038, 7039, 7040, 7041, 7042, 7043, 7044, 7045, 7046, 7047, 7048, 7049, 7050, 7051, 7052, 7053, 7054, 7055, 7056, 7057, 7058, 7059, 7060, 7061, 7062, 7063, 7064, 7065, 7066, 7067, 7068] with [st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]

theorem tb_A (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {sh V0 V1 V2 V3 pa off : Nat}
    (hsh : sh ≤ 200) (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s 15768 (wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 16026 (wd (tbW sh V0 V1 V2 V3) :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M) 214 := by
  opt87_reach [7069, 7070, 7071, 7072, 7073, 7074, 7075, 7076, 7077, 7078, 7079, 7080, 7081, 7082, 7083, 7084, 7085, 7086, 7087, 7088, 7089, 7090, 7091, 7092, 7093, 7094, 7095, 7096, 7097, 7098, 7099, 7100, 7101, 7102, 7103, 7104, 7105, 7106, 7107, 7108, 7109, 7110, 7111, 7112, 7113, 7114, 7115, 7116, 7117, 7118, 7119, 7120, 7121, 7122, 7123, 7124, 7125, 7126, 7127, 7128, 7129, 7130, 7131, 7132, 7133, 7134, 7135, 7136, 7137, 7138, 7139, 7140] with [tbW, tdsw, ts2, ts1, tgW]

theorem tb_B (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X sh V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hsh : sh + 40 < 240) (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 91680) :
    Reach (callState s 16026 (wd X :: wd sh :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15768 (wd (40 + sh) :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7141, 7142, 7143, 7144, 7145, 7146, 7147, 7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7164, 7165, 7166, 7167] with [TB.st3, tbN]

theorem tb_Bx (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {X V0 V1 V2 V3 pa off : Nat}
    (hX : X < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hpa : 2048 ≤ pa) (hpa2 : pa + 2080 ≤ 91680) :
    Reach (callState s 16026 (wd X :: wd 200 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 16094 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (pa - 32) :: wd T :: wd off :: wd E :: wd ret :: tail)
        (TB.st3 M pa X)) 88 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz := hs.sized
  simp only [memWords] at hsz
  opt87_reach [7141, 7142, 7143, 7144, 7145, 7146, 7147, 7148, 7149, 7150, 7151, 7152, 7153, 7154, 7155, 7156, 7157, 7158, 7159, 7160, 7161, 7162, 7163, 7164, 7165, 7166, 7167] with [TB.st3, tbN]

theorem tb_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 pa off : Nat}
    (_hne : pa ≠ E - 192) (hle : E ≤ pa) (hpa : pa < 2 ^ 64) (_hoff : off < 2 ^ 64) (hE : 192 ≤ E) :
    Reach (callState s 16094 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd pa :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15377 (wd pa :: wd T :: wd (30 + off) :: wd E :: wd ret :: tail) M) 90 := by
  opt87_reach [7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181, 7182, 7183, 7184, 7185, 7186, 7187, 7188, 7189, 7190, 7197, 7198, 7199]

theorem tb_cl (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {V0 V1 V2 V3 off : Nat}
    (hE : 192 ≤ E) (hE2 : E < 2 ^ 64) (_hoff : off < 2 ^ 64) :
    Reach (callState s 16094 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 64) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s 15377 (wd E :: wd T :: wd (20 + off) :: wd E :: wd ret :: tail) M) 107 := by
  opt87_reach [7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7181, 7182, 7183, 7184, 7185, 7186, 7187, 7188, 7189, 7190, 7191, 7192, 7193, 7194, 7195, 7196, 7197, 7198, 7199]
  exact ofNat_eq_ofNat_iff.mpr (by omega)  -- port: symbolic `off`

set_option maxRecDepth 100000 in
theorem tb_exit (hs : Ctx s) (htl : tail.length ≤ 960) (hj : Decode.isValidJumpDest MlDsaOpt87.optBytecode ret = true)
    (hret : ret < 2 ^ 16) (M : ByteArray) {V0 V1 V2 V3 off : Nat} (hE : 192 ≤ E) (hE2 : E < 2 ^ 64)
    (_hoff : off < 2 ^ 64) :
    Reach (callState s 16094 (wd 240 :: wd V3 :: wd V2 :: wd V1 :: wd V0 :: wd (E - 192) :: wd T :: wd off :: wd E :: wd ret :: tail) M)
      (callState s ret tail M) 58 := by
  opt87_reach [7168, 7169, 7170, 7171, 7172, 7173, 7174, 7175, 7176, 7177, 7178, 7179, 7180, 7200, 7201, 7202, 7203, 7204, 7205] with [hj]

end

end MlDsaOpt87.Proofs.TB
