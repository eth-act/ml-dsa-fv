import MlDsa.Spec.Interface
import MlDsa44.Spec
set_option warningAsError true
/-!
# The parametric spec at ML-DSA-44 is the audited ML-DSA-44 spec

Not part of the trusted surface: it anchors `MlDsa.Fips204` and
`MlDsa.Interface` to the independently audited `MlDsa44.Fips204` and
`MlDsa44.Spec` (docs/spec-review.md). For `Params.mldsa44` and address
`0x8212`, every verification function and every statement is equal to the
ML-DSA-44 one.
-/

namespace MlDsa.Bridge44

open EvmSemantics

/-! ## Shared constants and parameters -/

theorem q_eq : Fips204.q = MlDsa44.Fips204.q := rfl
theorem zeta_eq : Fips204.zeta = MlDsa44.Fips204.zeta := rfl
theorem d_eq : Fips204.d = MlDsa44.Fips204.d := rfl
theorem bitlen_eq : Fips204.bitlen = MlDsa44.Fips204.bitlen := rfl
theorem rej_eq : Fips204.rejNTTPolyLimit = MlDsa44.Fips204.rejNTTPolyLimit := rfl
theorem sib_eq : Fips204.sampleInBallLimit = MlDsa44.Fips204.sampleInBallLimit := rfl
theorem k_eq : Params.mldsa44.k = MlDsa44.Fips204.k := rfl
theorem l_eq : Params.mldsa44.l = MlDsa44.Fips204.l := rfl
theorem tau_eq : Params.mldsa44.tau = MlDsa44.Fips204.tau := rfl
theorem lambda_eq : Params.mldsa44.lambda = MlDsa44.Fips204.lambda := rfl
theorem gamma1_eq : Params.mldsa44.gamma1 = MlDsa44.Fips204.gamma1 := rfl
theorem gamma2_eq : Params.mldsa44.gamma2 = MlDsa44.Fips204.gamma2 := rfl
theorem omega_eq : Params.mldsa44.omega = MlDsa44.Fips204.omega := rfl
theorem beta_eq : Params.mldsa44.beta = MlDsa44.Fips204.beta := rfl
theorem zeroPoly_eq : Fips204.zeroPoly = MlDsa44.Fips204.zeroPoly := rfl
theorem H_eq : Fips204.H = MlDsa44.Fips204.H := rfl
theorem G_eq : Fips204.G = MlDsa44.Fips204.G := rfl
theorem bit_eq : Fips204.bit = MlDsa44.Fips204.bit := rfl

/-! The `match` auxiliaries of the two transcriptions are distinct constants
with equal bodies. -/

theorem rejNTTPolyOf_match :
    @Fips204.rejNTTPolyOf.match_1 = @MlDsa44.Fips204.rejNTTPolyOf.match_1 := rfl
theorem sampleInBallOf_match :
    @Fips204.sampleInBallOf.match_1 = @MlDsa44.Fips204.sampleInBallOf.match_1 := rfl
theorem useHint_match : @Fips204.useHint.match_1 = @MlDsa44.Fips204.useHint.match_1 := rfl
theorem verifyInternal_match_1 :
    @Fips204.verifyInternal.match_1 = @MlDsa44.Fips204.verifyInternal.match_1 := rfl
theorem verifyInternal_match_4 :
    @Fips204.verifyInternal.match_4 = @MlDsa44.Fips204.verifyInternal.match_4 := rfl
theorem verifyInternal_match_6 :
    @Fips204.verifyInternal.match_6 = @MlDsa44.Fips204.verifyInternal.match_6 := rfl

/-- After unfolding both sides, rewrite every constant of the parametric
transcription to its ML-DSA-44 twin (`rw` also reaches instance arguments,
which `simp` does not visit), then close by reducible `rfl`. Plain `rfl` on
the unfolded terms is not used: a first-order mismatch makes the unifier
evaluate the bounded XOF loops. -/
syntax "bridge" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| bridge) => `(tactic| ((repeat (first
      | rw [verifyInternal_match_1] | rw [verifyInternal_match_4] | rw [verifyInternal_match_6]
      | rw [rejNTTPolyOf_match] | rw [sampleInBallOf_match] | rw [useHint_match]
      | rw [hintBitUnpack_eq] | rw [pkDecode_eq] | rw [sigDecode_eq] | rw [w1Encode_eq]
      | rw [sampleIndex_eq] | rw [sampleInBall_eq] | rw [rejNTTPoly_eq] | rw [expandA_eq]
      | rw [decompose_eq] | rw [useHint_eq] | rw [matrixVectorNTT_eq]
      | rw [bitsToInteger_eq] | rw [coeff_eq] | rw [simpleBitPack_eq] | rw [simpleBitUnpack_eq]
      | rw [bitUnpack_eq] | rw [modPm_eq] | rw [zetas_eq] | rw [ntt_eq] | rw [nttInv_eq]
      | rw [addNTT_eq] | rw [multiplyNTT_eq] | rw [normBelow_eq]
      | rw [zeroPoly_eq] | rw [H_eq] | rw [G_eq] | rw [bit_eq]
      | rw [q_eq] | rw [zeta_eq] | rw [d_eq] | rw [bitlen_eq] | rw [rej_eq] | rw [sib_eq]
      | rw [k_eq] | rw [l_eq] | rw [tau_eq] | rw [lambda_eq] | rw [gamma1_eq] | rw [gamma2_eq]
      | rw [omega_eq] | rw [beta_eq])) <;> with_reducible rfl))

/-! ## Algorithms -/

theorem bitsToInteger_eq : Fips204.bitsToInteger = MlDsa44.Fips204.bitsToInteger := by
  delta Fips204.bitsToInteger MlDsa44.Fips204.bitsToInteger; bridge
theorem coeff_eq : Fips204.coeffFromThreeBytes = MlDsa44.Fips204.coeffFromThreeBytes := by
  delta Fips204.coeffFromThreeBytes MlDsa44.Fips204.coeffFromThreeBytes; bridge
theorem simpleBitPack_eq : Fips204.simpleBitPack = MlDsa44.Fips204.simpleBitPack := by
  delta Fips204.simpleBitPack MlDsa44.Fips204.simpleBitPack; bridge
theorem simpleBitUnpack_eq : Fips204.simpleBitUnpack = MlDsa44.Fips204.simpleBitUnpack := by
  delta Fips204.simpleBitUnpack MlDsa44.Fips204.simpleBitUnpack; bridge
theorem bitUnpack_eq : Fips204.bitUnpack = MlDsa44.Fips204.bitUnpack := by
  delta Fips204.bitUnpack MlDsa44.Fips204.bitUnpack; bridge
theorem hintBitUnpack_eq : Fips204.hintBitUnpack .mldsa44 = MlDsa44.Fips204.hintBitUnpack := by
  delta Fips204.hintBitUnpack MlDsa44.Fips204.hintBitUnpack; bridge
theorem pkDecode_eq : Fips204.pkDecode .mldsa44 = MlDsa44.Fips204.pkDecode := by
  delta Fips204.pkDecode MlDsa44.Fips204.pkDecode; bridge
theorem sigDecode_eq : Fips204.sigDecode .mldsa44 = MlDsa44.Fips204.sigDecode := by
  delta Fips204.sigDecode MlDsa44.Fips204.sigDecode; bridge
theorem w1Encode_eq : Fips204.w1Encode .mldsa44 = MlDsa44.Fips204.w1Encode := by
  delta Fips204.w1Encode MlDsa44.Fips204.w1Encode; bridge

theorem sampleIndex_eq : Fips204.sampleIndex = MlDsa44.Fips204.sampleIndex := by
  funext s i pos
  induction pos using Fips204.sampleIndex.induct s i with
  | case1 pos hlt hle =>
    rw [Fips204.sampleIndex, MlDsa44.Fips204.sampleIndex]
    simp only [sib_eq] at hlt ⊢; simp [hlt, hle]
  | case2 pos hlt hle ih =>
    rw [Fips204.sampleIndex, MlDsa44.Fips204.sampleIndex]
    simp only [sib_eq] at hlt ⊢; simp [hlt, hle, ih]
  | case3 pos hlt =>
    rw [Fips204.sampleIndex, MlDsa44.Fips204.sampleIndex]
    simp only [sib_eq] at hlt ⊢; simp [hlt]

theorem sampleInBall_eq : Fips204.sampleInBall .mldsa44 = MlDsa44.Fips204.sampleInBall := by
  delta Fips204.sampleInBall MlDsa44.Fips204.sampleInBall Fips204.sampleInBallOf
    MlDsa44.Fips204.sampleInBallOf; bridge
theorem rejNTTPoly_eq : Fips204.rejNTTPoly = MlDsa44.Fips204.rejNTTPoly := by
  delta Fips204.rejNTTPoly MlDsa44.Fips204.rejNTTPoly Fips204.rejNTTPolyOf
    MlDsa44.Fips204.rejNTTPolyOf; bridge
theorem expandA_eq : Fips204.expandA .mldsa44 = MlDsa44.Fips204.expandA := by
  delta Fips204.expandA MlDsa44.Fips204.expandA; bridge
theorem modPm_eq : Fips204.modPm = MlDsa44.Fips204.modPm := by
  delta Fips204.modPm MlDsa44.Fips204.modPm; bridge
theorem decompose_eq : Fips204.decompose .mldsa44 = MlDsa44.Fips204.decompose := by
  delta Fips204.decompose MlDsa44.Fips204.decompose; bridge
theorem useHint_eq : Fips204.useHint .mldsa44 = MlDsa44.Fips204.useHint := by
  delta Fips204.useHint MlDsa44.Fips204.useHint; bridge
theorem zetas_eq : Fips204.zetas = MlDsa44.Fips204.zetas := by
  delta Fips204.zetas MlDsa44.Fips204.zetas Fips204.bitRev8 MlDsa44.Fips204.bitRev8; bridge
theorem ntt_eq : Fips204.ntt = MlDsa44.Fips204.ntt := by
  delta Fips204.ntt MlDsa44.Fips204.ntt; bridge
theorem nttInv_eq : Fips204.nttInv = MlDsa44.Fips204.nttInv := by
  delta Fips204.nttInv MlDsa44.Fips204.nttInv; bridge
theorem addNTT_eq : Fips204.addNTT = MlDsa44.Fips204.addNTT := by
  delta Fips204.addNTT MlDsa44.Fips204.addNTT; bridge
theorem multiplyNTT_eq : Fips204.multiplyNTT = MlDsa44.Fips204.multiplyNTT := by
  delta Fips204.multiplyNTT MlDsa44.Fips204.multiplyNTT; bridge
theorem matrixVectorNTT_eq :
    Fips204.matrixVectorNTT .mldsa44 = MlDsa44.Fips204.matrixVectorNTT := by
  delta Fips204.matrixVectorNTT MlDsa44.Fips204.matrixVectorNTT; bridge
theorem normBelow_eq : Fips204.normBelow = MlDsa44.Fips204.normBelow := by
  delta Fips204.normBelow MlDsa44.Fips204.normBelow; bridge
theorem verifyInternal_fun_eq :
    Fips204.verifyInternal .mldsa44 = MlDsa44.Fips204.verifyInternal := by
  delta Fips204.verifyInternal MlDsa44.Fips204.verifyInternal; bridge

/-! ## Verification and statements -/

theorem verifyInternal_eq (pk M' sig : ByteArray) :
    Fips204.verifyInternal .mldsa44 pk M' sig = MlDsa44.Fips204.verifyInternal pk M' sig := by
  rw [verifyInternal_fun_eq]

theorem pkLen_eq : Fips204.pkLen .mldsa44 = MlDsa44.Fips204.pkLen := by
  simp only [Fips204.pkLen, MlDsa44.Fips204.pkLen, k_eq, q_eq, d_eq, bitlen_eq]
theorem sigLen_eq : Fips204.sigLen .mldsa44 = MlDsa44.Fips204.sigLen := by
  simp only [Fips204.sigLen, MlDsa44.Fips204.sigLen, k_eq, l_eq, lambda_eq, gamma1_eq, omega_eq,
    bitlen_eq]

theorem verify_eq (pk msg sig : ByteArray) :
    Fips204.verify .mldsa44 pk msg sig = MlDsa44.Fips204.verify pk msg sig := by
  simp only [Fips204.verify, MlDsa44.Fips204.verify, verifyInternal_eq, pkLen_eq, sigLen_eq]

theorem accepts_eq (input : ByteArray) :
    Interface.accepts .mldsa44 input = MlDsa44.accepts input := by
  delta Interface.accepts MlDsa44.accepts MlDsa44.pkLen MlDsa44.sigLen
  rw [pkLen_eq, sigLen_eq]
  simp only [verify_eq]

theorem spec_eq (input : ByteArray) :
    Interface.spec .mldsa44 input = MlDsa44.spec input := by
  simp only [Interface.spec, MlDsa44.spec, accepts_eq]

theorem initialState_eq (code calldata : ByteArray) (gas : Nat) :
    Interface.initialState MlDsa44.deployAddress code calldata gas =
      MlDsa44.initialState code calldata gas := rfl

theorem calldataFits_eq : Interface.CalldataFits = MlDsa44.CalldataFits := rfl

theorem frameEntry_iff (code : ByteArray) (s : EVM.State) :
    Interface.FrameEntry code s ↔ MlDsa44.FrameEntry code s :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩,
   fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩⟩

theorem frameEntry_eq : @Interface.FrameEntry = @MlDsa44.FrameEntry := by
  funext code s; exact propext (frameEntry_iff code s)

theorem spec_fun_eq : Interface.spec .mldsa44 = MlDsa44.spec := funext spec_eq

theorem correct_iff (code : ByteArray) :
    Interface.Correct .mldsa44 MlDsa44.deployAddress code ↔ MlDsa44.Correct code := by
  simp only [Interface.Correct, MlDsa44.Correct, spec_fun_eq, initialState_eq,
    calldataFits_eq]

theorem correctWithSchedule_iff (code : ByteArray) (schedule : Nat → Nat) :
    Interface.CorrectWithSchedule .mldsa44 MlDsa44.deployAddress code schedule ↔
      MlDsa44.CorrectWithSchedule code schedule := by
  simp only [Interface.CorrectWithSchedule, MlDsa44.CorrectWithSchedule, spec_fun_eq,
    initialState_eq, calldataFits_eq]

theorem correctInAnyContextWithSchedule_iff (code : ByteArray) (schedule : Nat → Nat) :
    Interface.CorrectInAnyContextWithSchedule .mldsa44 code schedule ↔
      MlDsa44.CorrectInAnyContextWithSchedule code schedule := by
  simp only [Interface.CorrectInAnyContextWithSchedule,
    MlDsa44.CorrectInAnyContextWithSchedule, spec_fun_eq, frameEntry_eq]

theorem correctInAnyContext_iff (code : ByteArray) :
    Interface.CorrectInAnyContext .mldsa44 code ↔ MlDsa44.CorrectInAnyContext code := by
  simp only [Interface.CorrectInAnyContext, MlDsa44.CorrectInAnyContext, spec_fun_eq,
    frameEntry_eq]

end MlDsa.Bridge44
