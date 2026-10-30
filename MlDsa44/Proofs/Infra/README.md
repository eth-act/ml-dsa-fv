# Proof infrastructure for the subroutine contracts

`import MlDsa44.Proofs.Infra`. The worked examples are `bswap64_call` (Fn/Lanes.lean,
straight-line code that returns a value), `brv8_call` (Fn/Zetas.lean, a loop that
returns a value) and `zeroPoly_call` (Fn/Ntt.lean, a loop that writes memory, with
`PolyAt` and `FrameExcept` posts). There is also a composition example below.

## Modules

| file | contents |
|---|---|
| `Infra/Code.lean` | lookup trees `instrTree`/`pcTree` (validated once by `tables_ok`, one linear kernel pass of about 15 s at build time), `instrAt`/`pcAt`, `pcOf`, `instructionPC_eq_pcOf`, `jumpdest_of`; simprocs `instrAt_lit`, `pcAt_lit`, `instructionPC_lit`, `isValidJumpDest_lit` |
| `Infra/Block.lean` | `runLocatedBlock_eq_foldl`, `stepL_located`, tactic `evm_block` |
| `Infra/Reach.lean` | `Reach s t c`, `.trans/.mono/.of_eq/.loop/.loopSum`, `call_iff`, `RetOK.callee`, `reach_block`, `blockCost`, `blockCostEval`, tactic `evm_reach` |
| `Infra/Word.lean` | `ofNat_land/lor/xor/mul/shl/shr/sub/lt/gt/eq/isZero`, `isTrue_ofNat`, `ofNat_mod_ofNat`, `ofNat_div_ofNat`, `ofNat_addMod`, `ofNat_mulMod`, `toNat_ofNat_of_lt`, `ofNat_eq_ofNat_iff` |
| `Infra/Memory.lean` | `activeWordsAfter_of_le`, `byteAt_writeBytes`, `byteAt_mstore8`, `word_mstore`, `word_mstore_disjoint`, `word_writeBytes_disjoint`, `word_eq_beNat` (big-endian), `word_congr`, `readWord_eq_word`, `Avoids`, `FrameExcept.refl/trans/mono/writeBytes/mstore/byteAt/word`, `BytesAt/LanesAt/PolyAt/RCTable/ZetaTable/HintAt.frame`, `storeWords` + `storeWords_succ`, `word_storeWords`, `FrameExcept.storeWords` |
| `Infra/Bits.lean` | `testBit_lit` simproc, `eq_of_testBit_lt`, `bswap_masks` |

## Recipe

1. **Read the code.** Read `docs/reference.listing`: `index<TAB>pc<TAB>instr`, where
   `DUP[k]`/`SWAP[k]` are 0-based. Split the function into straight-line paths that
   end at a `JUMP`, at a taken or untaken `JUMPI`, or just before a loop head. A
   path may run *through* a `JUMPI` whose condition `simp` can decide (for example
   the loop exit test for `j < 256` when `hj : j < 256` is in context).
2. **State one block lemma per path** between `callState s pc stk m` states that
   share the same base `s`:
   ```lean
   have h : Infra.Reach (callState s 3069 (wd j :: wd p :: wd ret :: tail) M)
       (callState s 3069 (wd (j+1) :: wd p :: wd ret :: tail) M') 71 := by
     evm_reach [1959, 1960, …, 1979] with [extra simp lemmas]
   ```
   The cost is the exact static opcode sum: `#eval Infra.blockCostEval [1959, …]`.
   If you state the wrong cost, `evm_reach` fails with a message that says so.
   Memory never grows: `activeWords` stays `s.activeWords`, so the static cost is
   the exact gas.
3. **Context needed by `evm_reach`/`evm_block`.** It uses these hypotheses through
   `assumption`/`omega`:
   * `hs : Ctx s`, used for the code, fork, `running` and precompile facts;
   * a stack-depth fact in `omega` form, e.g. `tail.length ≤ 960`. Get it with
     `have := hr.depth; simp only [Stack.f, Stack.leaf] at this; omega`;
   * every memory access needs `off + 32 ≤ 32 * s.activeWords.toNat` (MLOAD/MSTORE).
     Unfold layout constants first (`simp only [POLY] at hmem`). To drop the
     `% 2^256` around addresses, put
     `have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small` in context;
   * bounds on symbolic values, so `% 2^256` disappears: `hx : x < 2^64`,
     `hacc : acc < 256`, …;
   * conditions of `JUMPI`/comparisons such as `hj : j < 8`. These are decided by
     `if_pos`/`if_neg` with `omega` as the discharger.
4. **Residual goal.** `evm_block` rewrites the whole run and then splits
   `some st = some st'` into its fields. What is left is the facts it could not
   close, usually `UInt256.ofNat A = UInt256.ofNat B` for a stack value or a memory
   equation. The `Word.lean` lemmas are already in the simp set, so every stack
   word ends up as `UInt256.ofNat (a Nat expression)`. Shifts appear as `* 2^k` and
   `/ 2^k`, literals are evaluated, and MLOAD gives `ofNat (word m a)`; MSTORE
   leaves `MachineState.writeBytes m (Data.Bytes.natToBytesPadded v 32) a` in the
   memory field. Close the
   residual by passing rewriting lemmas in `with […]` (as `bswap64_call` does with
   `Infra.bswap_masks`), or by a separate `Nat` lemma.
5. **Loops.** Use a state family `I : Nat → State` indexed by the iteration count,
   with the invariant data (accumulator, memory so far) computed from `j`. Prove
   entry `Reach start (I 0) c₀`, body `∀ j < n, Reach (I j) (I (j+1)) c`, and exit
   `Reach (I n) final c₁`. Then
   `(hentry.trans (Infra.Reach.loop n hbody)).trans hexit` gives cost
   `c₀ + n*c + c₁`. Use `Reach.loopSum` when the per-iteration cost varies. For a
   loop that writes memory, `Infra.storeWords m base v j` is the memory after `j`
   word stores; `storeWords_succ` (pass it in `with`) matches the block's residual,
   and `word_storeWords` / `FrameExcept.storeWords` give the `PolyAt` /
   `FrameExcept` posts.
6. **Closing the contract.** `rw [Infra.call_iff, Entry.f, Gas.f]`, then
   `exact (h.mono (by norm_num)).of_eq (by simp) (by simp)`. The `of_eq` goals
   normalise `args ++ List.replicate k (ofNat 0) ++ ofNat ret :: tail`.
7. **Calling a subroutine.** Make the caller's block end at the callee entry with
   stack `args ++ zeros ++ wd ret' :: (callerLocals ++ wd ret :: tail)`. Then:
   ```lean
   -- inside initZetas: hr : RetOK Stack.initZetas ret tail,
   -- hblk : Reach (callState s 3007 …) (callState s 2956
   --          (wd i :: wd 0 :: wd 3028 :: wd w :: wd i :: wd w :: wd ret :: tail) m) 48
   have hcall := Infra.call_iff.mp (brv8_call hs
     (hr.callee (B' := Stack.brv8) (ret' := 3028) (extra := [wd w, wd i, wd w, wd ret])
        (by decide) (by simp) (by simp only [Infra.isValidJumpDest_lit]) (by norm_num)) m hi)
   exact hblk.trans (hcall.of_eq (by simp [Entry.brv8]) rfl)
   ```
   (This snippet was checked against the real `brv8_call`. Give `ret'` explicitly:
   the jumpdest simproc needs a literal.)
   Costs add up. Bound them against `Gas.f` with `Reach.mono` and `omega`/`norm_num`.

## Pitfalls

* **Never let the kernel unfold `Artifact.located i`, `referenceArtifact.instructionPC n`
  or `referenceInstructions`.** Each of these walks the 3375-element list at about
  0.2 ms per element, which costs about 1 s per occurrence. `evm_block` avoids them
  through `stepL_located` (a propositional step lemma) and the tree simprocs. Do
  **not** add `runLocated`, `Located.ofIndex`, `located` or `instructionPC` to the
  simp set, and do not prove instruction facts with `rfl`/`decide` on those
  definitions. Use `instrAt`/`pcAt`/`jumpdest_of n pc (by decide +kernel)` instead.
* **Keep large concrete data abstract in block lemmas.** For example, state the loop
  exit for an arbitrary memory `M` and instantiate it with `mem 256` afterwards
  (see `zeroPoly_call`). Otherwise the kernel may evaluate
  `storeWords … 256` (deep recursion).
* `decide +kernel` is fine for bounded `Nat` facts (`∀ i < 256, …`). `brv8_call`
  uses it for the bit-reversal equation and the accumulator bound.
* Bit-twiddling identities: `Infra.eq_of_testBit_lt`, then `interval_cases j` and
  one `simp only [Nat.testBit_*, testBit_lit, …]` per bit (see `bswap_masks`,
  about 2 s for 64 bits).
* Prefer `Infra.Reach` over raw `GasSteps`; `Call` is definitionally `Reach`.
* Stack values from `PUSH` are normalised to `UInt256.ofNat n`, and `PUSH0` to
  `UInt256.ofNat 0`. State stacks with `wd n` (= `UInt256.ofNat n`).

## Measured cost (this machine)

* `bswap64_call`: one 41-instruction block plus the value lemma. simp 0.73 s,
  kernel 0.48 s, simproc interpretation 0.24 s; the whole file takes 3.9 s wall /
  2.25 GB RSS, of which about 2.5 s / 2 GB is imports.
* A ~40-instruction block on its own: about 0.35 s simp + 0.3 s kernel (~1 s per
  50-instruction block).
* `zeroPoly_call` (3 blocks, 34 instructions, plus posts): about 2.8 s; file 5.5 s /
  2.3 GB.
* `brv8_call` (3 blocks plus two `decide +kernel` table checks): file 6.8 s / 2.4 GB.
* `Infra/Code.lean` (validating the trees once): 10.8 s / 3.3 GB.
