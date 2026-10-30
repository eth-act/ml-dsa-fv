import MlDsa44.Proofs.Infra
set_option warningAsError true
/-!
# Block lemmas for the top-level frame

* `Ctx0`: the execution facts of the top frame that hold before memory is
  sized (no bound on `activeWords`).
* `reach_block_pot`: a straight-line block from any `Ctx0` state to any
  state (memory may grow, the last instruction may halt) costs its static
  opcode sum plus the growth of the memory potential.
* `reach_calldatacopy`: one `CALLDATACOPY` inside sized memory.
-/

namespace MlDsa44.Proofs.Main

open EvmSemantics
open EvmSemantics.EVM
open EvmProof.Stepper
open MlDsa44.Proofs.Artifact
open MlDsa44.Proofs.Infra

/-- Facts about a running state of the reference code, without memory bounds. -/
structure Ctx0 (s : State) : Prop where
  code : s.executionEnv.code = referenceBytecode
  fork : s.fork = .Osaka
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  running : s.halt = .Running

theorem Ctx.ctx0 {s : State} (hs : Ctx s) : Ctx0 s :=
  ⟨hs.code, hs.fork, hs.notPrecompile, hs.running⟩

theorem Ctx0.callState {s : State} (h : Ctx0 s) (pc : Nat) (stk : List UInt256)
    (m : ByteArray) : Ctx0 (callState s pc stk m) :=
  ⟨h.code, h.fork, h.notPrecompile, h.running⟩

theorem reach_block_pot {s t : State} (h0 : Ctx0 s) (path : List (Fin 3375)) {cost : Nat}
    (hok : blockOK path cost = true)
    (hrun : runLocatedBlock (locatedPath path) s = some t) :
    Reach s t (cost + MachineState.memCost t.activeWords.toNat -
      MachineState.memCost s.activeWords.toNat) := by
  simp only [blockOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨hfree, hcost⟩ := hok
  have hcode : s.executionEnv.code = referenceArtifact.code := h0.code
  let g := runLocatedBlock_sound referenceArtifact .Osaka (locatedPath path) hcode h0.fork hrun
    h0.running h0.notPrecompile
  refine ⟨g, le_of_eq ?_⟩
  have hpot := EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree (locatedPath path)
    (blockCost path) hrun h0.fork ?free ?static
  · change runLocatedBlockCost (locatedPath path) s = _
    omega
  case free =>
    intro l hl
    simp only [locatedPath, List.mem_map] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    rw [located_instruction_eq]
    exact hfree i hi
  case static =>
    unfold EvmProof.Meter.runLocatedBlockStaticCost blockCost locatedPath
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, located_instruction_eq]

/-- One `CALLDATACOPY` of `n` bytes from calldata offset `src` to `d`, inside
the active memory. -/
theorem reach_calldatacopy {s : State} (hs : Ctx s) (i : Fin 3375) {pc d src n : Nat}
    {rest : List UInt256} {m : ByteArray}
    (hi : instrAt i.val = .op .CALLDATACOPY) (hpc : pcAt i.val = pc)
    (hd : d < 2 ^ 256) (hsrc : src < 2 ^ 256) (hn : n < 2 ^ 256) (hpc' : pc + 1 < 2 ^ 256)
    (hmem : d + n ≤ 32 * s.activeWords.toNat) (hlen : rest.length ≤ 1000) :
    Reach (callState s pc (wd d :: wd src :: wd n :: rest) m)
      (callState s (pc + 1) rest
        (MachineState.writeBytes m
          (MachineState.readPadded s.executionEnv.calldata src n) d))
      (3 + 3 * ((n + 31) / 32)) := by
  have hrun : runLocatedBlock (locatedPath [i]) (callState s pc (wd d :: wd src :: wd n :: rest) m) =
      some (callState s (pc + 1) rest
        (MachineState.writeBytes m
          (MachineState.readPadded s.executionEnv.calldata src n) d)) := by
    have hpcw : (UInt256.ofNat pc).toNat = pc := toNat_ofNat_of_lt (by omega)
    simp only [locatedPath, List.map_cons, List.map_nil, runLocatedBlock]
    rw [show runLocated (located i) (callState s pc (wd d :: wd src :: wd n :: rest) m) =
        stepL (some (callState s pc (wd d :: wd src :: wd n :: rest) m)) (located i) by
      rw [stepL_some, runIfRunning_of (s := callState s pc (wd d :: wd src :: wd n :: rest) m) _
        hs.running]]
    rw [stepL_located, hi, hpc]
    simp only [callState, hs.running, guardHalt_running, hpcw, if_true, runInstr, wd,
      List.length_cons, toNat_ofNat_of_lt hd, toNat_ofNat_of_lt hsrc, toNat_ofNat_of_lt hn,
      State.activeWordsAfterUInt256, activeWordsAfter_of_le hmem, ofNat_toNat,
      EvmProof.Word.succ_ofNat_mod]
    rw [if_pos (by omega)]
  have hcode : (callState s pc (wd d :: wd src :: wd n :: rest) m).executionEnv.code =
      referenceArtifact.code := hs.code
  let g := runLocatedBlock_sound referenceArtifact .Osaka (locatedPath [i]) hcode hs.fork hrun
    hs.running hs.notPrecompile
  refine ⟨g, le_of_eq ?_⟩
  have hpot := EvmProof.Meter.runLocatedBlock_cost_potential (locatedPath [i]) hrun
  change runLocatedBlockCost (locatedPath [i]) _ = _
  change _ + MachineState.memCost s.activeWords.toNat = _ + MachineState.memCost s.activeWords.toNat at hpot
  have hw : EvmProof.Meter.runLocatedBlockCostWithoutMemory (locatedPath [i])
      (callState s pc (wd d :: wd src :: wd n :: rest) m) = 3 + 3 * ((n + 31) / 32) := by
    simp only [locatedPath, List.map_cons, List.map_nil,
      EvmProof.Meter.runLocatedBlockCostWithoutMemory, located_instruction_eq, hi,
      EvmProof.Meter.instrCostWithoutMemory, callState, Gas.copyWordCost, wd,
      toNat_ofNat_of_lt hn, Nat.add_zero]
    rfl
  omega

end MlDsa44.Proofs.Main
