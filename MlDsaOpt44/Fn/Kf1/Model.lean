import MlDsaOpt44.Fn.Kf1.Tables
/-!
# `kf1`: word model of one round and its 64-bit lane mirror

`kf1` keeps one Keccak state with every lane replicated, `rep v`, and computes
a round with single shifts instead of rotations (`scripts/opt_keccak.py`,
`rot_top` with `decay`). The word model below is the round exactly as the code
computes it (operand order of every opcode included), so the block lemmas of
`Blocks*.lean` can state their post-states with it:

* `Cw A x`: column parity `C_x` of the words `A`;
* `Dw C x`: `D_x = C_{x−1} ⊕ (C_{x+1} << 1)`;
* `Bw A D j`: `shf j (D_{j mod 5} ⊕ A_j)` (theta, then rho by one shift);
* `outW A D rc j`: chi (`chiW`) of the five `B`s of row `j / 5`, iota on lane 0;
* `rerepW o`: `((o >> 64) & M64) · REP`, the re-replication of the second round.

`CL`, `DL`, `BL`, `outL` mirror the model on `UInt64` lanes (shifts become
rotations). `Win.lean` relates the two on bit windows.
-/

namespace MlDsaOpt44.Proofs.Kf1

open EvmSemantics
open EvmSemantics.EVM

/-- `2^64 − 1`, as the code pushes it. -/
def M64w : UInt256 := UInt256.ofNat 18446744073709551615

/-- `1 + 2^64 + 2^128 + 2^192`, as the code pushes it. -/
def REPw : UInt256 := UInt256.ofNat 6277101735386680764176071790128604879584176795969512275969

/-- Column parity `C_x`. -/
def Cw (A : Nat → UInt256) (x : Nat) : UInt256 :=
  (A (x + 20)).xor ((A (x + 15)).xor ((A (x + 10)).xor ((A (x + 5)).xor (A x))))

/-- `SHL 1`. -/
def sh1 (v : UInt256) : UInt256 := v.shiftLeft (UInt256.ofNat 1)

/-- `D_x`. -/
def Dw (C : Nat → UInt256) : Nat → UInt256
  | 0 => (sh1 (C 1)).xor (C 4)
  | 1 => (sh1 (C 2)).xor (C 0)
  | 2 => (sh1 (C 3)).xor (C 1)
  | 3 => (C 2).xor (sh1 (C 4))
  | 4 => (sh1 (C 0)).xor (C 3)
  | _ => UInt256.ofNat 0

/-- Source lane of position `k` of output row `y` (rho-pi). -/
def srcLane (y k : Nat) : Nat := (k + 3 * y) % 5 + 5 * k

/-- Theta and rho of source lane `j`. -/
def Bw (A D : Nat → UInt256) (j : Nat) : UInt256 := shf j ((D (j % 5)).xor (A j))

/-- Output lane `j` of a round (before re-replication). -/
def outW (A D : Nat → UInt256) (rc : UInt256) (j : Nat) : UInt256 :=
  if j = 0 then rc.xor (chiW 0 fun k => Bw A D (srcLane 0 k))
  else chiW j fun k => Bw A D (srcLane (j / 5) k)

/-- Re-replication of bits `[64, 128)`. -/
def rerepW (o : UInt256) : UInt256 := REPw * UInt256.land M64w (o.shiftRight (UInt256.ofNat 64))

/-- Output lane `j` of a round from the words `A`. -/
def roundW (A : Nat → UInt256) (rc : UInt256) (j : Nat) : UInt256 := outW A (Dw (Cw A)) rc j

/-! ## Lane mirror -/

open EvmSemantics.Crypto.Keccak in
/-- `C_x` on lanes. -/
def CL (s : Nat → UInt64) (x : Nat) : UInt64 :=
  s (x + 20) ^^^ (s (x + 15) ^^^ (s (x + 10) ^^^ (s (x + 5) ^^^ s x)))

open EvmSemantics.Crypto.Keccak in
/-- `D_x` on lanes. -/
def DL (C : Nat → UInt64) : Nat → UInt64
  | 0 => rotl64 (C 1) 1 ^^^ C 4
  | 1 => rotl64 (C 2) 1 ^^^ C 0
  | 2 => rotl64 (C 3) 1 ^^^ C 1
  | 3 => C 2 ^^^ rotl64 (C 4) 1
  | 4 => rotl64 (C 0) 1 ^^^ C 3
  | _ => 0

open EvmSemantics.Crypto.Keccak in
/-- `B` of source lane `j` on lanes. -/
def BL (s D : Nat → UInt64) (j : Nat) : UInt64 := rotl64 (D (j % 5) ^^^ s j) rotOff[j]!

/-- Output lane `j` on lanes. -/
def outL (s D : Nat → UInt64) (rc : UInt64) (j : Nat) : UInt64 :=
  if j = 0 then rc ^^^ (chiL 0 fun k => BL s D (srcLane 0 k))
  else chiL j fun k => BL s D (srcLane (j / 5) k)

/-- One round on lanes, in the code's form. -/
def roundL (s : Nat → UInt64) (rc : UInt64) (j : Nat) : UInt64 := outL s (DL (CL s)) rc j

/-! ## Memory -/

/-- `MSTORE` of a word. -/
def mst (M : ByteArray) (a : Nat) (v : UInt256) : ByteArray :=
  MachineState.writeBytes M (Data.Bytes.natToBytesPadded v.toNat 32) a

end MlDsaOpt44.Proofs.Kf1
