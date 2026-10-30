import MlDsa44.Proofs.Main.Block
set_option warningAsError true
/-!
# From the initial state to the sized frame

The program starts at pc 0, hops over every function definition (56
trampoline instructions) to the body, and branches on the calldata size:

* short calldata: `mstore(0, 0); return(0, 32)`;
* otherwise: `mlen := calldatasize − 3732; mstore(MSGIN + mlen + 256, 0)`,
  which sizes memory once to `ceil((MSGIN + mlen + 288) / 32)` words.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact
open MlDsa44.Proofs.Infra

theorem initial_ctx0 (cd : ByteArray) : Ctx0 (initialState referenceBytecode cd 0) :=
  ⟨rfl, rfl, by simp [initialState]; decide, rfl⟩

theorem initial_eq (cd : ByteArray) :
    callState (initialState referenceBytecode cd 0) 0 [] .empty = initialState referenceBytecode cd 0 :=
  rfl

theorem activeWordsAfter_zero (off : Nat) :
    MachineState.activeWordsAfter 0 off 32 = (off + 31) / 32 + 1 := by
  simp [MachineState.activeWordsAfter]

theorem short_block {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hlen : s.executionEnv.calldata.size < 3732) :
    runLocatedBlock (locatedPath [0, 1, 1553, 1554, 1555, 1597, 1598, 1599, 1615, 1616, 1617, 1632, 1633, 1634, 1677, 1678, 1679, 1875, 1876, 1877, 1912, 1913, 1914, 1954, 1955, 1956, 1984, 1985, 1986, 2094, 2095, 2096, 2236, 2237, 2238, 2291, 2292, 2293, 2374, 2375, 2376, 2477, 2478, 2479, 2639, 2640, 2641, 2730, 2731, 2732, 2818, 2819, 2820, 2934, 2935, 2936, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146])
      (callState s 0 [] .empty) =
    some { callState s 4747 [] (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) with
      halt := .Returned
      hReturn := MachineState.readPadded
        (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32) 0) 0 32
      activeWords := UInt256.ofNat 1 } := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  evm_block [Ctx0.code, Ctx0.running, activeWordsAfter_zero, haw]

/-- The sized frame: `activeWords` after the sizing store. -/
def sizedWords (mlen : Nat) : Nat := (MSGIN + mlen + 319) / 32

def sized (s : State) (mlen : Nat) : State :=
  { s with activeWords := UInt256.ofNat (sizedWords mlen) }

set_option maxRecDepth 20000 in
theorem size_block {s : State} (h0 : Ctx0 s) (haw : s.activeWords.toNat = 0)
    (hlen : 3732 ≤ s.executionEnv.calldata.size) (hfit : s.executionEnv.calldata.size < 2 ^ 64) :
    runLocatedBlock (locatedPath [0, 1, 1553, 1554, 1555, 1597, 1598, 1599, 1615, 1616, 1617, 1632, 1633, 1634, 1677, 1678, 1679, 1875, 1876, 1877, 1912, 1913, 1914, 1954, 1955, 1956, 1984, 1985, 1986, 2094, 2095, 2096, 2236, 2237, 2238, 2291, 2292, 2293, 2374, 2375, 2376, 2477, 2478, 2479, 2639, 2640, 2641, 2730, 2731, 2732, 2818, 2819, 2820, 2934, 2935, 2936, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157])
      (callState s 0 [] .empty) =
    some (callState (sized s (s.executionEnv.calldata.size - 3732)) 4766
      [wd (s.executionEnv.calldata.size - 3732)]
      (MachineState.writeBytes .empty (Data.Bytes.natToBytesPadded 0 32)
        (MSGIN + (s.executionEnv.calldata.size - 3732) + 256))) := by
  have hr : (callState s 0 [] .empty).halt = .Running := h0.running
  simp only [sized, sizedWords, MSGIN]
  evm_block [Ctx0.code, Ctx0.running, activeWordsAfter_zero, haw]
  exact ⟨congrArg _ (by omega), congrArg _ (by omega)⟩

/-- The round-constant words. -/
def rcv (i : Nat) : Nat := (Crypto.Keccak.RC[i]!).toNat

theorem rc_block1 {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    Reach (callState s 4766 [wd mlen] M) (callState s 4847 [wd mlen] (storeWords M RC rcv 8))
      72 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  evm_reach [3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181]
  rfl

theorem rc_block2 {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    Reach (callState s 4847 [wd mlen] (storeWords M RC rcv 8))
      (callState s 4925 [wd mlen] (storeWords M RC rcv 16)) 72 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  evm_reach [3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205]
  rfl

theorem rc_block3 {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    Reach (callState s 4925 [wd mlen] (storeWords M RC rcv 16))
      (callState s 3003 [wd 5026, wd mlen] (storeWords M RC rcv 24)) 86 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2535 ≤ s.activeWords.toNat := hs.sized
  evm_reach [3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3231, 3232]
  rfl

theorem sized_activeWords (s : State) (mlen : Nat) (h : mlen < 2 ^ 64) :
    (sized s mlen).activeWords.toNat = sizedWords mlen :=
  toNat_ofNat_of_lt (by unfold sizedWords MSGIN; omega)

theorem sized_ctx {s : State} (h0 : Ctx0 s) (hfit : s.executionEnv.calldata.size < 2 ^ 64)
    (mlen : Nat) (h : mlen < 2 ^ 64) : Ctx (sized s mlen) where
  code := h0.code
  fork := h0.fork
  notPrecompile := h0.notPrecompile
  running := h0.running
  sized := by
    rw [sized_activeWords s mlen h]; unfold sizedWords fixedWords; omega
  small := by
    rw [sized_activeWords s mlen h]; unfold sizedWords MSGIN; omega
  calldataFits := hfit

theorem sized_mem (s : State) (mlen : Nat) (h : mlen < 2 ^ 64) :
    MSGIN + mlen + 288 ≤ 32 * (sized s mlen).activeWords.toNat := by
  rw [sized_activeWords s mlen h]; unfold sizedWords; omega

theorem rcTable_storeWords (M : ByteArray) : RCTable (storeWords M RC rcv 24) := by
  intro i hi
  rw [word_storeWords (by unfold rcv; have := (Crypto.Keccak.RC[i]!).toNat_lt; omega) 24 hi]
  rfl

theorem rc_blocks {s : State} (hs : Ctx s) (mlen : Nat) (M : ByteArray) :
    ∃ M', RCTable M' ∧ FrameExcept M M' [(RC, RC + 768)] ∧
      Reach (callState s 4766 [wd mlen] M) (callState s 3003 [wd 5026, wd mlen] M') 230 := by
  refine ⟨storeWords M RC rcv 24, rcTable_storeWords M, ?_,
    ((rc_block1 hs mlen M).trans (rc_block2 hs mlen M)).trans (rc_block3 hs mlen M)⟩
  simpa using FrameExcept.storeWords M RC rcv 24

end MlDsa44.Proofs.Main
