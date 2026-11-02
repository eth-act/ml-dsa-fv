#!/usr/bin/env python3
"""Generate the `dz` proof of the Glamsterdam ML-DSA-44 bytecode.

  python3 MlDsaOptGlam44/Fn/Decode/gen_dz.py        # 44
  python3 MlDsaOptGlam44/Fn/Decode/gen_dz.py 65|87  # gen_dz_nn.py

Writes `Z4GBlocks.lean` and `Z4GLoop.lean` next to this script, from
`MlDsaOptGlam44/listing.tsv` only. The code is v4's `dz` (`MlDsaOpt44/Fn/Decode/
Z4*.lean`) with the gather loop of a chunk unrolled (`DZ_UNROLL`): gather step
`j < 4` shifts the four windows by the immediate `54 j` and stores at the
immediate offsets `dp + 96 j + 32 k`. Entry, the four window loads and the
chunk tail are v4's instructions (the tail without the gather test). v4's
lane algebra (`gW`, `zR`, `zv4`, `zf4`, `raw_pack`, `ZInvM`, `ZInvA`) is reused.
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] != "44":
    sys.path.insert(0, HERE)
    from gen_dz_nn import main
    main(int(sys.argv[1]))
    sys.exit(0)
ROOT = os.path.join(HERE, "..", "..", "..")

ROWS = [l.rstrip("\n").split("\t") for l in open(os.path.join(ROOT, "MlDsaOptGlam44", "listing.tsv"))][1:]
INS = [(int(i), int(p), t) for i, p, t in ROWS]
BYPC = {p: i for i, p, _ in INS}

GAS = {"JUMPDEST": 1, "PUSH0": 2, "POP": 2, "MUL": 5, "JUMP": 8, "JUMPI": 10}


def gas(t):
    return GAS.get(t.split()[0], 3)


def cost(a, b):
    return sum(gas(INS[i][2]) for i in range(a, b))


def idx(a, b):
    return "[" + ", ".join(str(i) for i in range(a, b)) + "]"


def pc(i):
    return INS[i][1]


def op(i):
    return INS[i][2].split()[0]


ENTRY, HEAD = 8770, 8809
E0, H = BYPC[ENTRY], BYPC[HEAD]
assert op(E0) == "JUMPDEST" and op(H) == "JUMPDEST"
# window loads: each ends after the CALLDATALOAD's byte swap; v4's boundaries
L = [H] + [next(i for i in range(H + 1, H + 400) if op(i) == f"DUP{7 + k}" and INS[i + 1][2].startswith("PUSH2")
              and INS[i + 3][2] == "CALLDATALOAD") for k in range(3)]
G0 = next(i for i in range(L[3], L[3] + 200) if op(i) == "POP" and op(i + 1) == "DUP4") + 1
assert [pc(i) for i in L] == [8809, 8990, 9057, 9124] and pc(G0) == 9199, [pc(i) for i in L]
# the end of the unrolled gather: six POPs, then v4's chunk tail
T0 = next(i for i in range(G0, G0 + 1200) if all(op(i + d) == "POP" for d in range(6)))
TAIL = T0 + 2                                       # the last step's own two POPs
STEPS = []
cur = G0
for j in range(4):
    p0 = next(i for i in range(cur, TAIL) if op(i) == "PUSH0")
    ms = [i for i in range(p0, TAIL) if op(i) == "MSTORE"][:3]
    ends = [m + 2 for m in ms]
    assert all(op(m + 1) == "OR" for m in ms)
    tl = ends[2] + 5
    assert [op(i) for i in range(ends[2], tl)] == ["DUP9", "OR", "SWAP8", "POP", "POP"]
    STEPS.append((cur, p0, ends, tl))
    cur = tl
assert cur == TAIL
DONE = next(i for i in range(TAIL, TAIL + 100) if op(i) == "JUMPI")
NC = next(i for i in range(DONE + 1, DONE + 100) if op(i) == "JUMPI")
LOOPJ = next(i for i in range(NC + 1, NC + 100) if op(i) == "JUMPDEST")
XD = LOOPJ + 3
assert op(XD) == "JUMPDEST" and op(XD - 1) == "JUMP"
XE = next(i for i in range(XD, XD + 20) if op(i) == "JUMP") + 1


def store_off(m):
    """The immediate added to `dp` before the `MSTORE` at `m` (0 if none)."""
    if op(m - 1) == "ADD":
        return int(INS[m - 2][2].split()[1], 16)
    assert op(m - 1) == "DUP9"
    return 0


def addr(c):
    return "dp" if c == 0 else f"({c} + dp)"


MBL = 1645498280219470655563407987279682868948834857825835856559341567
C = ["6277101735386680763495507056286727952657427581105975853055",
     "26959946660873538060741835960174461801791452538186943042387869433855",
     "1766820105243087041267848467410591083712559083657179364930612997358944255",
     "450552876409790643671482431940419874915447411150352389258589821042463539455"]
CS = " :: ".join(f"wd {c}" for c in C)
LOADW = "[st1_eq, st2_eq, st3_eq, st4_eq, st1_mod, st2_mod, st3_mod, st4_mod, bsw_word]"
VS = "wd V3 :: wd V2 :: wd V1 :: wd V0"
CH = "wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail"
DIVS = ["W", "(W / 262144)", "(W / 68719476736)"]


def step_blocks(j):
    w0, p0, ends, tl = STEPS[j]
    out = f'''
theorem zg_w{j} (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{V0 V1 V2 V3 dp off acc e : Nat}}
    (h0 : V0 < 2 ^ 256) (h1 : V1 < 2 ^ 256) (h2 : V2 < 2 ^ 256) (h3 : V3 < 2 ^ 256) :
    Reach (callState s {pc(w0)} ({VS} :: {CH}) M)
      (callState s {pc(p0)} (wd (gW {54 * j} V0 V1 V2 V3) :: {VS} :: {CH}) M) {cost(w0, p0)} := by
  glam44_rreach {idx(w0, p0)} with [gW, Nat.div_one]
'''
    starts = [p0, ends[0], ends[1]]
    for k in range(3):
        a, b = starts[k], ends[k]
        c = store_off(b - 2)
        assert c == 96 * j + 32 * k, (j, k, c)
        pre = "wd W" if k == 0 else "wd Lf :: wd W"
        lf = f"zf4 (zR {DIVS[k]})" + ("" if k == 0 else " ||| Lf")
        extra = ", Nat.or_zero" if k == 0 else ""
        hw = "" if k == 0 else " (hW : W < 2 ^ 256)"
        lfv = "" if k == 0 else "Lf "
        out += f'''
theorem zg_s{j}{k} (hs : Ctx s) (M : ByteArray) {{{lfv}W x1 x2 x3 x4 dp x6 x7 : Nat}}
    {{rest : List UInt256}} (hrest : rest.length ≤ 962){hw}
    (haw : s.activeWords.toNat ≤ 18446744073709551616) (hgp : {c + 32} + dp ≤ 32 * s.activeWords.toNat) :
    Reach (callState s {pc(a)} ({pre} :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd dp :: wd x6 :: wd x7 :: wd MBL :: rest) M)
      (callState s {pc(b)} (wd ({lf}) :: wd W :: wd x1 :: wd x2 :: wd x3 :: wd x4 :: wd dp :: wd x6 :: wd x7 :: wd MBL :: rest)
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv4 (zR {DIVS[k]})) 32) {addr(c)})) {cost(a, b)} := by
  glam44_rreach {idx(a, b)} with [zR_eq, zsub4, zv4_mod, zf4_eq{extra}]
'''
    out += f'''
theorem zg_t{j} (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{Lf W V0 V1 V2 V3 dp off acc e : Nat}} :
    Reach (callState s {pc(ends[2])} (wd Lf :: wd W :: {VS} :: {CH}) M)
      (callState s {pc(tl)} ({VS} :: {CH.replace("wd acc", "wd (acc ||| Lf)")}) M) {cost(ends[2], tl)} := by
  glam44_rreach {idx(ends[2], tl)}
'''
    return out


blocks = f'''import MlDsaOptGlam44.Infra.Reflect
import MlDsaOptGlam44.Layout
import MlDsaOpt44.Fn.Decode.Z4Loop
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# `dz` (glam): straight-line blocks

Generated by `Fn/Decode/gen_dz.py`; do not edit. Chunk head `{HEAD}` (stack
`dp, off, acc, MB, end`); v4's four window loads (`z4_load*`, the last without
v4's gather-loop counters), then four unrolled gather steps `j < 4`: `zg_w j`
forms `gW (54 j)` from the windows, `zg_s j k` stores lane word `3 j + k` at
`dp + 96 j + 32 k` and ORs its flag word, `zg_t j` ORs the step's flags into
`acc`. The chunk tail (`zg_nc`, `zg_clamp`, `zg_exit`) is v4's.
-/

namespace MlDsaOptGlam44.Proofs.DecodeZ4

open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.DecodeZ
open MlDsaOpt44.Proofs.DecodeZ4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon

local notation "MBL" => ({MBL} : Nat)

section
variable {{s : State}} {{ret : Nat}} {{tail : List UInt256}}

theorem zg_entry (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) :
    Reach (callState s {ENTRY} (wd ZH :: wd Z0 :: wd ret :: tail) M)
      (callState s {HEAD} (wd ZH :: wd Z0 :: wd 0 :: wd MBL :: wd (ZH + 7808) :: wd ret :: tail) M) {cost(E0, H)} := by
  simp only [ZH, Z0]
  glam44_rreach {idx(E0, H)}

theorem zg_load0 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{dp off acc e : Nat}}
    (hoff : off < 2 ^ 64) :
    Reach (callState s {HEAD} ({CH}) M)
      (callState s {pc(L[1])} (wd (leNat s.executionEnv.calldata off 32) :: {CS} :: {CH}) M) {cost(L[0], L[1])} := by
  glam44_rreach {idx(L[0], L[1])} with {LOADW}

theorem zg_load1 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{dp off acc e V0 : Nat}}
    (hoff : off < 2 ^ 64) :
    Reach (callState s {pc(L[1])} (wd V0 :: {CS} :: {CH}) M)
      (callState s {pc(L[2])} (wd (leNat s.executionEnv.calldata (576 + off) 32) :: wd V0 :: {CS} :: {CH}) M) {cost(L[1], L[2])} := by
  glam44_rreach {idx(L[1], L[2])} with {LOADW}

theorem zg_load2 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{dp off acc e V0 V1 : Nat}}
    (hoff : off < 2 ^ 64) :
    Reach (callState s {pc(L[2])} (wd V1 :: wd V0 :: {CS} :: {CH}) M)
      (callState s {pc(L[3])} (wd (leNat s.executionEnv.calldata (1152 + off) 32) :: wd V1 :: wd V0 :: {CS} :: {CH}) M) {cost(L[2], L[3])} := by
  glam44_rreach {idx(L[2], L[3])} with {LOADW}

theorem zg_load3 (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray) {{dp off acc e V0 V1 V2 : Nat}}
    (hoff : off < 2 ^ 64) :
    Reach (callState s {pc(L[3])} (wd V2 :: wd V1 :: wd V0 :: {CS} :: {CH}) M)
      (callState s {pc(G0)} (wd (leNat s.executionEnv.calldata (1728 + off) 32) :: wd V2 :: wd V1 :: wd V0 :: {CH}) M) {cost(L[3], G0)} := by
  glam44_rreach {idx(L[3], G0)} with {LOADW}
{"".join(step_blocks(j) for j in range(4))}
theorem zg_nc (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {{V0 V1 V2 V3 dp off acc e : Nat}} (hle : dp + 384 ≤ e) (he : e < 2 ^ 64) :
    Reach (callState s {pc(TAIL)} ({VS} :: {CH}) M)
      (callState s {HEAD} (wd (384 + dp) :: wd (27 + off) :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        {cost(TAIL, NC + 1) + cost(LOOPJ, XD)} := by
  glam44_rreach {idx(TAIL, NC + 1)[:-1] + ", " + idx(LOOPJ, XD)[1:]}

theorem zg_clamp (hs : Ctx s) (htl : tail.length ≤ 960) (M : ByteArray)
    {{V0 V1 V2 V3 dp off acc e : Nat}} (hne : dp ≠ e) (hgt : e < dp + 384) (he : dp < 2 ^ 64)
    (hoff : off < 2 ^ 64) :
    Reach (callState s {pc(TAIL)} ({VS} :: {CH}) M)
      (callState s {HEAD} (wd (384 + dp - 256) :: wd (27 + off - 18) :: wd acc :: wd MBL :: wd e ::
        wd ret :: tail) M) {cost(TAIL, XD)} := by
  glam44_rreach {idx(TAIL, XD)}

theorem zg_exit (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (htl : tail.length ≤ 960) (M : ByteArray)
    {{V0 V1 V2 V3 dp off acc : Nat}} :
    Reach (callState s {pc(TAIL)} ({VS} :: wd dp :: wd off :: wd acc :: wd MBL :: wd dp :: wd ret :: tail) M)
      (callState s ret (wd acc :: tail) M) {cost(TAIL, DONE + 1) + cost(XD, XE)} := by
  have := hr.small
  glam44_rreach {idx(TAIL, DONE + 1)[:-1] + ", " + idx(XD, XE)[1:]} with [hr.jumpdest]

end

end MlDsaOptGlam44.Proofs.DecodeZ4
'''

STEP = [cost(STEPS[j][0], STEPS[j][3]) for j in range(4)]
CHUNK = cost(L[0], G0) + sum(STEP)
NCC = cost(TAIL, NC + 1) + cost(LOOPJ, XD)
CLC = cost(TAIL, XD)
EXC = cost(TAIL, DONE + 1) + cost(XD, XE)
TOTAL = cost(E0, H) + 20 * (CHUNK + NCC) + CHUNK + CLC + CHUNK + EXC

WIN = ("wd (leNat cd (1728 + off) 32) :: wd (leNat cd (1152 + off) 32) :: "
       "wd (leNat cd (576 + off) 32) :: wd (leNat cd off 32)")


def gstep(j):
    w0, p0, ends, tl = STEPS[j]
    gp = "dp" if j == 0 else f"({96 * j} + dp)"
    rw = "" if j == 0 else f'''  rw [show {96 * j + 32} + dp = 32 + {gp} by omega, show {96 * j + 64} + dp = 64 + {gp} by omega] at r
'''
    s0 = "" if j == 0 else f"show ({96 * j} + dp) = ({96 * j} + dp) from rfl, "
    def wb(m, k):
        return (f"(MachineState.writeBytes {m} (Data.Bytes.natToBytesPadded (zv4 (zR {DIVS[k]})) 32) "
                f"{addr(96 * j + 32 * k)})")
    m1 = wb("M", 0)
    m2 = wb(m1, 1)
    m3 = wb(m2, 2)
    xs = "(x1 := leNat cd (1728 + off) 32) (x2 := leNat cd (1152 + off) 32) (x3 := leNat cd (576 + off) 32) (x4 := leNat cd off 32) (dp := dp) (x6 := off) (x7 := acc) (rest := wd e :: wd ret :: tail)"
    return f'''
theorem zg_step{j} (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {{m₀ M : ByteArray}} {{u T acc dp off e : Nat}} (hu : 4 * u + 12 ≤ 256)
    (hdp : dp = ZH + 128 * u) (hoff : off = Z0 + 9 * u)
    (hM : ZInvM s.executionEnv.calldata m₀ M (max T (4 * u + 3 * {j})))
    (hA : ZInvA s.executionEnv.calldata acc (max T (4 * u + 3 * {j}))) :
    ∃ M' acc', ZInvM s.executionEnv.calldata m₀ M' (max T (4 * u + 3 * {j} + 3)) ∧
      ZInvA s.executionEnv.calldata acc' (max T (4 * u + 3 * {j} + 3)) ∧
      Reach (callState s {pc(w0)} ({WIN.replace("cd", "s.executionEnv.calldata")} ::
          wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s {pc(tl)} ({WIN.replace("cd", "s.executionEnv.calldata")} ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') {STEP[j]} := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hsz : memWords ≤ s.activeWords.toNat := hs.sized
  simp only [memWords] at hsz
  have hgp96 : {96 * j} + dp + 96 ≤ ZH + 8192 := by simp only [ZH] at hdp ⊢; omega
  have hmem : {96 * j} + dp + 96 ≤ 32 * s.activeWords.toNat := by simp only [ZH] at hgp96; omega
  generalize hcdv : s.executionEnv.calldata = cd at hM hA hcd ⊢
  have hV : ∀ a, leNat cd a 32 < 2 ^ 256 := fun a => leNat_lt cd a 32
  set W := gW {54 * j} (leNat cd off 32) (leNat cd (576 + off) 32) (leNat cd (1152 + off) 32)
    (leNat cd (1728 + off) 32) with hW
  have hWlt : W < 2 ^ 256 := by
    rw [hW, ← gW_mod]; exact Nat.mod_lt _ (by norm_num)
  have h1 := zg_w{j} (ret := ret) (tail := tail) hs htl M (dp := dp) (off := off) (acc := acc) (e := e)
    (hV off) (hV (576 + off)) (hV (1152 + off)) (hV (1728 + off))
  have h2 := zg_s{j}0 hs M (W := W) {xs} (by simp; omega) haw (by omega)
  have h3 := zg_s{j}1 hs {m1} (Lf := zf4 (zR W)) (W := W) {xs} (by simp; omega) hWlt haw (by omega)
  have h4 := zg_s{j}2 hs {m2} (Lf := zf4 (zR (W / 262144)) ||| zf4 (zR W)) (W := W) {xs} (by simp; omega) hWlt haw (by omega)
  have h5 := zg_t{j} (ret := ret) (tail := tail) hs htl {m3}
    (Lf := zf4 (zR (W / 68719476736)) ||| (zf4 (zR (W / 262144)) ||| zf4 (zR W))) (W := W)
    (V0 := leNat cd off 32) (V1 := leNat cd (576 + off) 32) (V2 := leNat cd (1152 + off) 32)
    (V3 := leNat cd (1728 + off) 32) (dp := dp) (off := off) (acc := acc) (e := e)
  have r := h1.trans (h2.trans (h3.trans (h4.trans h5)))
{rw}  obtain ⟨hM', hA'⟩ := zg_inv hcd (g := {j}) (gp := {gp}) (by omega) hu hdp hoff (by omega) rfl hM hA
  exact ⟨_, _, hM', hA', r.mono (by norm_num)⟩
'''


loop = f'''import MlDsaOptGlam44.Fn.Decode.Z4GBlocks
import MlDsaOptGlam44.Budget
set_option warningAsError true
set_option linter.unusedVariables false
/-!
# `dz` (glam): gather steps, chunks and the trace of the call

Generated by `Fn/Decode/gen_dz.py`; do not edit. As v4's `Z4Loop.lean`, with the
four gather steps of a chunk unrolled (`zg_step0` … `zg_step3`); `zg_inv` is
v4's invariant step (`z_gstep`'s memory and accumulator part) for one step.
-/

namespace MlDsaOptGlam44.Proofs.DecodeZ4

open MlDsaOpt44.Proofs
open MlDsaOpt44.Proofs.DecodeZ
open MlDsaOpt44.Proofs.DecodeZ4

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44

local notation "MBL" => ({MBL} : Nat)

/-- The invariants after gather step `g` of the chunk at coefficient `4 u`: its three
lane words are stored at `gp`, `32 + gp`, `64 + gp` and its flag words ORed into `acc`. -/
theorem zg_inv {{cd m₀ M : ByteArray}} (hcd : HDR ≤ cd.size) {{u g T acc dp off gp W : Nat}}
    (hg : g ≤ 3) (hu : 4 * u + 12 ≤ 256) (hdp : dp = ZH + 128 * u) (hoff : off = Z0 + 9 * u)
    (hgp : gp = dp + 96 * g) (hgs : W = gW (54 * g) (leNat cd off 32) (leNat cd (576 + off) 32)
      (leNat cd (1152 + off) 32) (leNat cd (1728 + off) 32))
    (hM : ZInvM cd m₀ M (max T (4 * u + 3 * g))) (hA : ZInvA cd acc (max T (4 * u + 3 * g))) :
    ZInvM cd m₀ (MachineState.writeBytes (MachineState.writeBytes
        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded (zv4 (zR W)) 32) gp)
        (Data.Bytes.natToBytesPadded (zv4 (zR (W / 262144))) 32) (32 + gp))
        (Data.Bytes.natToBytesPadded (zv4 (zR (W / 68719476736))) 32) (64 + gp))
      (max T (4 * u + 3 * g + 3)) ∧
    ZInvA cd (acc ||| (zf4 (zR (W / 68719476736)) ||| (zf4 (zR (W / 262144)) ||| zf4 (zR W))))
      (max T (4 * u + 3 * g + 3)) := by
  have hgp96 : gp + 96 ≤ ZH + 8192 := by simp only [ZH] at hdp ⊢; omega
  have hR : ∀ kk, kk ≤ 2 → zR (W / 2 ^ (18 * kk)) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + kk)) := by
    intro kk hkk
    rw [hgs]
    exact raw_pack hcd hoff hg hkk (by omega)
  have hR0 : zR W = pack4 (fun k => rawZ cd k (4 * u + 3 * g)) := by simpa using hR 0 (by omega)
  have hR1 : zR (W / 262144) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 1)) := by
    simpa using hR 1 (by omega)
  have hR2 : zR (W / 68719476736) = pack4 (fun k => rawZ cd k (4 * u + 3 * g + 2)) := by
    simpa using hR 2 (by omega)
  refine ⟨?_, ?_⟩
  · rw [hR0, hR1, hR2, zv_raw, zv_raw, zv_raw]
    obtain ⟨hfr, hw⟩ := hM
    have hlt : ∀ t, pack4 (fun k => zLane cd k t) < 2 ^ 256 := fun t =>
      pack4_lt' fun k _ => (zLane_lt' cd k t)
    refine ⟨?_, fun t ht => ?_⟩
    · refine FrameExcept.mono (FrameExcept.trans (FrameExcept.trans (FrameExcept.trans hfr
        (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) (FrameExcept.mstore _ _ _)) ?_
      intro r hr
      refine ⟨(ZH, ZH + 8192), by simp, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [ZH] at hgp96 hdp ⊢ <;> omega
    · have hgpt : gp = ZH + 32 * (4 * u + 3 * g) := by omega
      by_cases h2 : t = 4 * u + 3 * g + 2
      · subst h2
        rw [show ZH + 32 * (4 * u + 3 * g + 2) = 64 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h1 : t = 4 * u + 3 * g + 1
      · subst h1
        rw [show ZH + 32 * (4 * u + 3 * g + 1) = 32 + gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      by_cases h0 : t = 4 * u + 3 * g
      · subst h0
        rw [show ZH + 32 * (4 * u + 3 * g) = gp by omega, word_mstore _ _ _ (hlt _)]
      rw [word_mstore_disjoint _ _ (by omega)]
      exact hw t (by omega)
  · obtain ⟨hlt, hiff⟩ := hA
    refine ⟨Nat.or_lt_two_pow hlt (Nat.or_lt_two_pow (zf4_zR_lt _)
      (Nat.or_lt_two_pow (zf4_zR_lt _) (zf4_zR_lt _))), ?_⟩
    rw [hR0, hR1, hR2, or_and_eq_zero, or_and_eq_zero, or_and_eq_zero, hiff, zf_raw, zf_raw, zf_raw]
    constructor
    · rintro ⟨ha, h2, h1, h0⟩ t ht
      by_cases e2 : t = 4 * u + 3 * g + 2
      · subst e2; exact h2
      by_cases e1 : t = 4 * u + 3 * g + 1
      · subst e1; exact h1
      by_cases e0 : t = 4 * u + 3 * g
      · subst e0; exact h0
      exact ha t (by omega)
    · intro h
      exact ⟨fun t ht => h t (by omega), h _ (by omega), h _ (by omega), h _ (by omega)⟩

section
variable {{s : State}} {{ret : Nat}} {{tail : List UInt256}}
{"".join(gstep(j) for j in range(4))}
/-! ## One chunk: four loads, four gather steps -/

theorem zg_chunk (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    {{m₀ M : ByteArray}} {{u T acc dp off e : Nat}} (hu : 4 * u + 12 ≤ 256) (hT : 4 * u ≤ T)
    (hdp : dp = ZH + 128 * u) (hoff : off = Z0 + 9 * u)
    (hM : ZInvM s.executionEnv.calldata m₀ M T) (hA : ZInvA s.executionEnv.calldata acc T) :
    ∃ M' acc', ZInvM s.executionEnv.calldata m₀ M' (max T (4 * u + 12)) ∧
      ZInvA s.executionEnv.calldata acc' (max T (4 * u + 12)) ∧
      Reach (callState s {HEAD} (wd dp :: wd off :: wd acc :: wd MBL :: wd e :: wd ret :: tail) M)
        (callState s {pc(TAIL)} ({WIN.replace("cd", "s.executionEnv.calldata")} ::
          wd dp :: wd off :: wd acc' :: wd MBL :: wd e :: wd ret :: tail) M') {CHUNK} := by
  have hoff64 : off < 2 ^ 64 := by simp only [Z0] at hoff; omega
  have l0 := zg_load0 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e) hoff64
  have l1 := zg_load1 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) hoff64
  have l2 := zg_load2 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32) hoff64
  have l3 := zg_load3 (ret := ret) (tail := tail) hs htl M (dp := dp) (acc := acc) (e := e)
    (V0 := leNat s.executionEnv.calldata off 32) (V1 := leNat s.executionEnv.calldata (576 + off) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + off) 32) hoff64
  obtain ⟨M1, a1, hM1, hA1, r1⟩ := zg_step0 (ret := ret) (tail := tail) (e := e) hs htl hcd hu hdp hoff
    (by rwa [show max T (4 * u + 3 * 0) = T by omega]) (by rwa [show max T (4 * u + 3 * 0) = T by omega])
  obtain ⟨M2, a2, hM2, hA2, r2⟩ := zg_step1 (ret := ret) (tail := tail) (e := e) hs htl hcd hu hdp hoff
    (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega]) (by rwa [show 4 * u + 3 * 1 = 4 * u + 3 * 0 + 3 by omega])
  obtain ⟨M3, a3, hM3, hA3, r3⟩ := zg_step2 (ret := ret) (tail := tail) (e := e) hs htl hcd hu hdp hoff
    (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega]) (by rwa [show 4 * u + 3 * 2 = 4 * u + 3 * 1 + 3 by omega])
  obtain ⟨M4, a4, hM4, hA4, r4⟩ := zg_step3 (ret := ret) (tail := tail) (e := e) hs htl hcd hu hdp hoff
    (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega]) (by rwa [show 4 * u + 3 * 3 = 4 * u + 3 * 2 + 3 by omega])
  refine ⟨M4, a4, by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega],
    by rwa [show 4 * u + 12 = 4 * u + 3 * 3 + 3 by omega], ?_⟩
  exact (l0.trans (l1.trans (l2.trans (l3.trans (r1.trans (r2.trans (r3.trans r4))))))).mono (by norm_num)

/-! ## The chunk loop and the whole subroutine -/

theorem zg_chunks (hs : Ctx s) (htl : tail.length ≤ 960) (hcd : HDR ≤ s.executionEnv.calldata.size)
    (m : ByteArray) : ∀ j, j ≤ 20 → ∃ M acc, ZInvM s.executionEnv.calldata m M (12 * j) ∧
      ZInvA s.executionEnv.calldata acc (12 * j) ∧
      Reach (callState s {HEAD} (wd ZH :: wd Z0 :: wd 0 :: wd MBL :: wd (ZH + 7808) :: wd ret :: tail) m)
        (callState s {HEAD} (wd (ZH + 384 * j) :: wd (Z0 + 27 * j) :: wd acc :: wd MBL :: wd (ZH + 7808) ::
          wd ret :: tail) M) ({CHUNK + NCC} * j)
  | 0, _ => ⟨m, 0, ⟨FrameExcept.refl _ _, fun t ht => absurd ht (by omega)⟩,
      ⟨by norm_num, by simp⟩, (Reach.refl _).of_eq rfl (by simp)⟩
  | j + 1, hj => by
    obtain ⟨M, acc, hM, hA, r⟩ := zg_chunks hs htl hcd m j (by omega)
    obtain ⟨M', acc', hM', hA', c⟩ := zg_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
      (u := 3 * j) (dp := ZH + 384 * j) (off := Z0 + 27 * j) (by omega) (by omega) (by omega) (by omega) hM hA
    have x := zg_nc (ret := ret) (tail := tail) hs htl M'
      (V0 := leNat s.executionEnv.calldata (Z0 + 27 * j) 32)
      (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 27 * j)) 32)
      (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 27 * j)) 32)
      (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 27 * j)) 32)
      (dp := ZH + 384 * j) (off := Z0 + 27 * j) (acc := acc') (e := ZH + 7808)
      (by simp only [ZH]; omega) (by simp only [ZH]; omega)
    refine ⟨M', acc', by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega],
      by rwa [show 12 * (j + 1) = max (12 * j) (4 * (3 * j) + 12) by omega], ?_⟩
    refine ((r.trans (c.trans x)).mono (by omega)).of_eq rfl ?_
    rw [show 384 + (ZH + 384 * j) = ZH + 384 * (j + 1) by omega,
      show 27 + (Z0 + 27 * j) = Z0 + 27 * (j + 1) by omega]

theorem dz_main (hs : Ctx s) (hr : RetOK Stack.dz ret tail) (m : ByteArray)
    (hcd : HDR ≤ s.executionEnv.calldata.size) :
    ∃ m', ∃ f, f < 2 ^ 256 ∧ ((f &&& zBits4 = 0) ↔ okZ s.executionEnv.calldata = true) ∧
      (∀ t, t < 256 → word m' (ZH + 32 * t) = pack4 fun k => zLane s.executionEnv.calldata k t) ∧
      FrameExcept m m' [(ZH, ZH + 8192)] ∧
      Call s Entry.dz [wd ZH, wd Z0] ret tail m [wd f] m' Gas.dz := by
  have htl : tail.length ≤ 960 := by
    have := hr.depth; simp only [Stack.dz, Stack.leaf] at this; omega
  have en := zg_entry (ret := ret) (tail := tail) hs htl m
  obtain ⟨M, acc, hM, hA, r⟩ := zg_chunks (ret := ret) hs htl hcd m 20 le_rfl
  obtain ⟨M', acc', hM', hA', c⟩ := zg_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
    (u := 60) (dp := ZH + 384 * 20) (off := Z0 + 27 * 20) (by omega) (by omega) (by omega) (by omega) hM hA
  have x := zg_clamp (ret := ret) (tail := tail) hs htl M'
    (V0 := leNat s.executionEnv.calldata (Z0 + 27 * 20) 32)
    (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 27 * 20)) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 27 * 20)) 32)
    (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 27 * 20)) 32)
    (dp := ZH + 384 * 20) (off := Z0 + 27 * 20) (acc := acc') (e := ZH + 7808)
    (by norm_num [ZH]) (by norm_num [ZH]) (by norm_num [ZH]) (by norm_num [Z0])
  have hx : 384 + (ZH + 384 * 20) - 256 = ZH + 7808 := by norm_num [ZH]
  have hy : 27 + (Z0 + 27 * 20) - 18 = Z0 + 9 * 61 := by norm_num [Z0]
  rw [hx, hy] at x
  obtain ⟨M'', f, hM'', hA'', c'⟩ := zg_chunk (ret := ret) (tail := tail) (e := ZH + 7808) hs htl hcd
    (u := 61) (dp := ZH + 7808) (off := Z0 + 9 * 61) (by omega) (by omega) (by norm_num [ZH]) rfl
    hM' hA'
  have ex := zg_exit (ret := ret) (tail := tail) hs hr htl M''
    (V0 := leNat s.executionEnv.calldata (Z0 + 9 * 61) 32)
    (V1 := leNat s.executionEnv.calldata (576 + (Z0 + 9 * 61)) 32)
    (V2 := leNat s.executionEnv.calldata (1152 + (Z0 + 9 * 61)) 32)
    (V3 := leNat s.executionEnv.calldata (1728 + (Z0 + 9 * 61)) 32)
    (dp := ZH + 7808) (off := Z0 + 9 * 61) (acc := f)
  have hcov : max (max (12 * 20) (4 * 60 + 12)) (4 * 61 + 12) = 256 := by norm_num
  rw [hcov] at hM'' hA''
  obtain ⟨hfr, hw⟩ := hM''
  obtain ⟨hlt, hiff⟩ := hA''
  refine ⟨M'', f, hlt, ?_, hw, hfr, ?_⟩
  · rw [hiff, okZ_iff hcd]
    exact ⟨fun h k hk t ht => h t ht k hk, fun h t ht k hk => h k hk t ht⟩
  · rw [call_iff, Entry.dz, Gas.dz]
    exact ((en.trans (r.trans (c.trans (x.trans (c'.trans ex))))).mono (by norm_num)).of_eq
      (by simp) (by simp)

end

end MlDsaOptGlam44.Proofs.DecodeZ4
'''

if __name__ == "__main__":
    with open(os.path.join(HERE, "Z4GBlocks.lean"), "w") as f:
        f.write(blocks)
    with open(os.path.join(HERE, "Z4GLoop.lean"), "w") as f:
        f.write(loop)
    print("entry", cost(E0, H), "chunk", CHUNK, "steps", STEP, "nc", NCC, "clamp", CLC, "exit", EXC,
          "total", TOTAL)
