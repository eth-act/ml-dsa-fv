import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Bswap
set_option warningAsError true
/-! # Segment `0 … 992`: size check, memory sizing, the `RC4`/`RC1` iota tables (straight line). -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The `RC4` words as pushed by the code. -/
def rc4v (i : Nat) : Nat := [15, 17293822573129236720, 108555083659983933209597798445644913612440610624038028787008778829991688335600, 108555083659983933209597798445644913612759625343026408596505692524454944440320, 17293822573129298175, 319014718988379809496913694467282698255, 108555083659983933209597798445644913612759625343026408596505692524458970972175, 108555083659983933209597798445644913612440610624038028787008778829987661803535, 4026593520, 4026593280, 319014718988379809514207517036385464335, 319014718988379809496913694467282759920, 319014718988379809514207517040411996415, 108555083659983933209597798445644913612440610624038028786991485007422585630975, 108555083659983933209597798445644913612440610624038028787008778829991688335375, 108555083659983933209597798445644913612440610624038028787008778829987661742335, 108555083659983933209597798445644913612440610624038028787008778829987661742320, 108555083659983933209597798445644913612440610624038028786991485007422585569280, 17293822569102766320, 108555083659983933209597798445644913612759625343026408596488398701885841797360, 108555083659983933209597798445644913612759625343026408596505692524458970972175, 108555083659983933209597798445644913612440610624038028787008778829991688273920, 319014718988379809496913694467282698255, 108555083659983933209597798445644913612759625343026408596505692524454944501760].getD i 0

/-- The `RC1` words (`RC[i] · REP`, folded). -/
def rc1v (i : Nat) : Nat := [6277101735386680764176071790128604879584176795969512275969, 206504092890751023779864409751650843328560248233805014854828162, 57896044618658304269233748006154520286541354199756752056442528574712273993866, 57896044632138276736569028420856833192418713957969307382711690650098270765056, 206560586806369503906741994397762000772476505824968740465311883, 13479973339852421633450939126351338586088633588469736715148203130881, 57896044632138277546315152285738651771131974884559336849070497330165354365057, 57896044618658303459487624141272701707828093273166722590083721894645190393865, 866240039483361945456297907037747473382616397843792694083722, 853685836012588583927945763457490263623448044251853669531784, 13480179078138900667299665761280331841242166839448401411882560290825, 13479973396346337251931066003935984697246077504727327878873813614602, 13480179894162126267568165104169664557960801185391384887919156166795, 57896044618658098587441184590785920529197007055760662721721455041703527317643, 57896044618658304262956646270767839522365282409628147176858351778742761717897, 57896044618658303421825013728952617122771662532395093312578661118828116738051, 57896044618658303415547911993565936358595590742266488432994484322858604462082, 57896044618658098518393065501532432123260217364346009046295510286038892281984, 205750840682504622088163281136835410743010147018288673381711882, 57896044632138071111270380623968360312659012925130661964248208280815134572554, 57896044632138277546315152285738651771131974884559336849070497330165354365057, 57896044618658304206462730652287712644780636298470703260600760615017151234176, 13479973339852421633450939126351338586088633588469736715148203130881, 57896044632138276786785842303950279305827288278998146419385105017854368972808].getD i 0

theorem rc4v_eq : ∀ i, i < 24 →
    rc4v i = il fun _ => (EvmSemantics.Crypto.Keccak.RC[i]!).toNat := by decide +kernel

theorem rc1v_eq : ∀ i, i < 24 → rc1v i = rep (EvmSemantics.Crypto.Keccak.RC[i]!).toNat := by
  decide +kernel

theorem rcv_lt : ∀ i, i < 24 → rc4v i < 2 ^ 256 ∧ rc1v i < 2 ^ 256 := by decide +kernel

/-- Memory after the sizing store. -/
@[irreducible] def initM0 : ByteArray := MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 67072

/-- Memory at `992`. -/
@[irreducible] def initMem : ByteArray := storeWords (storeWords initM0 RC4 rc4v 24) RC1 rc1v 24

theorem init_run {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : 3732 ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    EvmProof.Stepper.runLocatedBlock (Artifact.locatedPath [0, 1, 2, 3, 4, 5, 6, 7]) (callState s 0 [] .empty) =
      some (callState (sized s) 15 [] initM0) := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  simp only [sized, memWords, initM0]
  opt44_block [Ctx0.code, Ctx0.running, haw, MachineState.activeWordsAfter]
  rfl

theorem init_rc4 {s : State} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s 15 [] M) (callState s 664 [] (storeWords M RC4 rc4v 24)) 216 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
  rfl

theorem init_rc1a {s : State} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s 664 [] M) (callState s 825 [wd 6277101735386680764176071790128604879584176795969512275969] (storeWords M RC1 rc1v 12)) 207 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
  rfl

theorem init_rc1b {s : State} (hs : Ctx s) (M : ByteArray) :
    Reach (callState s 825 [wd 6277101735386680764176071790128604879584176795969512275969] (storeWords M RC1 rc1v 12))
      (callState s 992 [] (storeWords M RC1 rc1v 24)) 206 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]
  rfl

theorem initMem_frame : FrameExcept initM0 initMem [(RC4, RC4 + 768), (RC1, RC1 + 768)] := by
  unfold initMem
  exact (FrameExcept.storeWords initM0 RC4 rc4v 24).trans (FrameExcept.storeWords _ RC1 rc1v 24)

theorem sized_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState (sized s) pc stk m).activeWords.toNat = memWords := sized_activeWords s

theorem callState_aw (s : State) (pc : Nat) (stk : List UInt256) (m : ByteArray) :
    (callState s pc stk m).activeWords = s.activeWords := rfl

theorem byteAt_ntb0 {k : Nat} (hk : k < 32) : byteAt (Data.Bytes.natToBytesPadded 0 32) k = 0 := by
  have hw := word_mstore ByteArray.empty 0 0 (by norm_num)
  have hb := byteN_word (MachineState.writeBytes ByteArray.empty (Data.Bytes.natToBytesPadded 0 32) 0) 0
    (q := 31 - k) (by omega)
  rw [hw, byteAt_writeBytes, natToBytesPadded_size, if_pos (by omega),
    show 0 + (31 - (31 - k)) - 0 = k by omega] at hb
  rw [← hb]; unfold byteN; simp

theorem initM0_zero : ZeroOn initM0 MISC TOP := by
  intro a h1 h2
  unfold initM0
  rw [byteAt_writeBytes, natToBytesPadded_size]
  split
  · exact byteAt_ntb0 (by omega)
  · unfold byteAt; rw [dif_neg (by simp)]

theorem inv0_initMem : Inv0 initMem where
  rc4 := fun i hi => by
    unfold initMem
    rw [FrameExcept.word (FrameExcept.storeWords _ RC1 rc1v 24) (by avoids_tac),
      word_storeWords (rcv_lt i hi).1 24 hi, rc4v_eq i hi]
  rc1 := fun i hi => by
    unfold initMem
    rw [word_storeWords (rcv_lt i hi).2 24 hi, rc1v_eq i hi]
  zero := initM0_zero.frame initMem_frame (by avoids_tac)

/-- `0 … 992` from the frame entry (memory empty, not yet sized). -/
theorem seg_init_proof {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hcd : HDR ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    ∃ m, Inv0 m ∧
      Reach (callState s 0 [] .empty) (callState (sized s) 992 [] m)
        (Gas.pInit + MachineState.memCost memWords) := by
  have hs : Ctx (sized s) := sized_ctx h0 hfit
  have hA := reach_block_pot (h0.callState 0 [] .empty) [0, 1, 2, 3, 4, 5, 6, 7] (cost := 29)
    (by decide +kernel) (init_run h0 haw hcd hfit)
  have hm1 := sized_aw s 15 [] initM0
  have hm0 := (congrArg UInt256.toNat (callState_aw s 0 [] .empty)).trans haw
  rw [hm1, hm0] at hA
  refine ⟨initMem, inv0_initMem, ?_⟩
  rw [show initMem = storeWords (storeWords initM0 RC4 rc4v 24) RC1 rc1v 24 by unfold initMem; rfl]
  have h := ((hA.trans (init_rc4 hs _)).trans (init_rc1a hs _)).trans (init_rc1b hs _)
  refine h.mono ?_
  have : MachineState.memCost 0 = 0 := rfl
  unfold Gas.pInit
  omega

end MlDsaOpt44.Proofs
