# Generator of the block lemmas of MlDsaOpt44/Fn/Group/Pass3.lean and Pass3m.lean (WP6).
# Usage (from the repo root): python3 MlDsaOpt44/Fn/Group/gen_p3.py p3|p3m
# prints the per-word block lemmas, tail/exit blocks and the iteration lemma;
# the file header and the `pass3*_reach` theorem are written by hand.
import sys
rows = [l.rstrip('\n').split('\t') for l in open('MlDsaOpt44/listing.tsv')]
pc = {int(r[0]): int(r[1]) for r in rows if r[0].isdigit()}

def gen(kind):
    if kind == 'p3':
        loop, w0, wl, nw, tail_start, jumpi, exit_end = 4079, 16, 21, 8, 4242, 4256, 4261
        entry = [4077, 4078]; ename = 'pass3'
        stk = lambda a, z, c: f"wd ({a}) :: wd sh :: wd ({z}) :: wd ({c}) :: wd ret :: tail"
        v = 'p3v M a z c sh'; vdef = "(word M (c + o) + word M (a + o) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256"
        fdef = "(word m (ACC + 32 * t) + word m (ABUF + 32 * t) * (word m (ZH + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256"
        vsig = "(M : ByteArray) (a z c sh o : Nat)"; fsig = "(m : ByteArray) (sh t : Nat)"
        extra_h = ""; fapp = "p3f m sh"; vapp = lambda M, o: f"p3v {M} (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) sh ({o})"
        name = 'p3'; extra_args = ''
    else:
        loop, w0, wl, nw, tail_start, jumpi, exit_end = 4264, 18, 23, 8, 4443, 4457, 4463
        entry = [4262, 4263]; ename = 'pass3m'
        stk = lambda a, z, c: f"wd ({a}) :: wd lm :: wd sh :: wd ({z}) :: wd ({c}) :: wd ret :: tail"
        v = 'p3mv M a z c lm sh'; vdef = "(word M (c + o) + (word M (a + o) &&& lm) * (word M (z + o) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256"
        fdef = "(word m (ACC + 32 * t) + (word m (ABUF + 32 * t) &&& lm) * (word m (ZH + 32 * t) / 2 ^ sh % 2 ^ 64)) % 2 ^ 256"
        vsig = "(M : ByteArray) (a z c lm sh o : Nat)"; fsig = "(m : ByteArray) (lm sh t : Nat)"
        extra_h = ""
        fapp = "p3mf m lm sh"; vapp = lambda M, o: f"p3mv {M} (ABUF + 256 * j) (ZH + 256 * j) (ACC + 256 * j) lm sh ({o})"
        name = 'p3m'; extra_args = ''; 
    out = []
    P = out.append
    P(f"/-- Value `{ename}` stores at `ACC[t]`. -/")
    P(f"def {name}f {fsig} : Nat :=\n  {fdef}\n")
    P(f"/-- Value a word block stores at `c + o` (reads of the current memory). -/")
    P(f"def {name}v {vsig} : Nat :=\n  {vdef}\n")
    blocks = []
    start = loop
    for i in range(nw):
        n = w0 if i == 0 else wl
        idx = list(range(start, start + n)); start += n
        blocks.append(idx)
    assert start == tail_start, (start, tail_start)
    hyps = ("{s : State} (hs : Ctx s) {tail : List UInt256} (htail : tail.length ≤ 960)\n"
            "    {a z c sh ret" + (" lm" if kind != 'p3' else "") + " : Nat} (M : ByteArray) (hsh : sh < 256)" + extra_h + "\n"
            "    (ha1 : 20480 ≤ a) (ha2 : a + 256 ≤ 28672) (hz1 : 32768 ≤ z) (hz2 : z + 256 ≤ 40960)\n"
            "    (hc1 : 43264 ≤ c) (hc2 : c + 256 ≤ 51456)")
    for i, idx in enumerate(blocks):
        p0, p1 = pc[idx[0]], pc[idx[-1] + 1]
        cost = 'COST'
        P(f"theorem {name}_w{i} {hyps} :\n"
          f"    Reach (callState s {p0} ({stk('a','z','c')}) M)\n"
          f"      (callState s {p1} ({stk('a','z','c')})\n"
          f"        (MachineState.writeBytes M (Data.Bytes.natToBytesPadded ({v} (32 * {i})) 32) (c + 32 * {i}))) {{cost{i}}} := by\n"
          f"  have hsz := hs.sized; simp only [memWords] at hsz\n"
          f"  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small\n"
          f"  opt44_reach {idx} with [{name}v, land_m64, land_m64', Nat.add_zero, Nat.add_comm,\n"
          f"    Nat.mul_comm, Nat.and_comm]\n")
    tidx = list(range(tail_start, jumpi + 1))
    P(f"theorem {name}_tail {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)\n"
      f"    {{a z c sh ret{' lm' if kind != 'p3' else ''} : Nat}} (M : ByteArray) (hlt : a + 256 < 28672) :\n"
      f"    Reach (callState s {pc[tail_start]} ({stk('a','z','c')}) M)\n"
      f"      (callState s {pc[loop]} ({stk('a + 256','z + 256','c + 256')}) M) {{costT}} := by\n"
      f"  opt44_reach {tidx}\n  simp only [Nat.add_comm, and_self]\n")
    eidx = list(range(tail_start, exit_end))
    P(f"theorem {name}_exit {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)\n"
      f"    {{z c sh ret{' lm' if kind != 'p3' else ''} : Nat}} (M : ByteArray) :\n"
      f"    Reach (callState s {pc[tail_start]} ({stk('28416','z','c')}) M) (callState s {pc[exit_end]} (wd ret :: tail) M) {{costE}} := by\n"
      f"  opt44_reach {eidx}\n")
    # iteration
    Mem = lambda e: f"storeWords m ACC ({fapp}) ({e})"
    P(f"theorem {name}_iter {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)\n"
      f"    {{sh ret{' lm' if kind != 'p3' else ''} j : Nat}} (m : ByteArray) (hsh : sh < 256){extra_h} (hj : j < 32) :\n"
      f"    Reach (callState s {pc[loop]} ({stk('ABUF + 256 * j','ZH + 256 * j','ACC + 256 * j')}) ({Mem('8 * j')}))\n"
      f"      (callState s {pc[tail_start]} ({stk('ABUF + 256 * j','ZH + 256 * j','ACC + 256 * j')}) ({Mem('8 * j + 8')})) {{costI}} := by\n"
      f"  have hb : ∀ i, i < 8 → {vapp('(' + Mem('8 * j + i') + ')', '32 * i')} = {fapp} (8 * j + i) := by\n"
      f"    intro i hi\n"
      f"    unfold {name}v {name}f\n"
      f"    rw [show ABUF + 256 * j + 32 * i = ABUF + 32 * (8 * j + i) by omega,\n"
      f"      show ZH + 256 * j + 32 * i = ZH + 32 * (8 * j + i) by omega,\n"
      f"      show ACC + 256 * j + 32 * i = ACC + 32 * (8 * j + i) by omega,\n"
      f"      word_storeWords_out (a := ABUF + 32 * (8 * j + i)) (by unfold ABUF ACC; omega),\n"
      f"      word_storeWords_out (a := ZH + 32 * (8 * j + i)) (by unfold ZH ACC; omega),\n"
      f"      word_storeWords_out (a := ACC + 32 * (8 * j + i)) (by omega)]\n"
      f"  have e : ∀ i, i < 8 → MachineState.writeBytes ({Mem('8 * j + i')})\n"
      f"      (Data.Bytes.natToBytesPadded ({vapp('(' + Mem('8 * j + i') + ')', '32 * i')}) 32) (ACC + 256 * j + 32 * i) =\n"
      f"      {Mem('8 * j + i + 1')} := fun i hi =>\n"
      f"    storeWords_next rfl (by omega) (hb i hi)\n"
      f"  have ha1 : 20480 ≤ ABUF + 256 * j := by unfold ABUF; omega\n"
      f"  have ha2 : ABUF + 256 * j + 256 ≤ 28672 := by unfold ABUF; omega\n"
      f"  have hz1 : 32768 ≤ ZH + 256 * j := by unfold ZH; omega\n"
      f"  have hz2 : ZH + 256 * j + 256 ≤ 40960 := by unfold ZH; omega\n"
      f"  have hc1 : 43264 ≤ ACC + 256 * j := by unfold ACC; omega\n"
      f"  have hc2 : ACC + 256 * j + 256 ≤ 51456 := by unfold ACC; omega\n")
    chain = []
    for i in range(nw):
        P(f"  have w{i} := {name}_w{i} hs htail (ret := ret){' (lm := lm)' if kind != 'p3' else ''} ({Mem(f'8 * j + {i}')}) hsh{extra_args} ha1 ha2 hz1 hz2 hc1 hc2\n"
          f"  rw [e {i} (by norm_num)] at w{i}")
    expr = "w0"
    for i in range(1, nw):
        expr = f"({expr}.trans w{i})"
    P(f"  exact {expr}\n")
    return out, blocks, tidx, eidx, entry

ins = {int(r[0]): r[2].split()[0] for r in rows if r[0].isdigit()}
def cost(idx):
    t = {'JUMPDEST':1,'PUSH0':2,'POP':2,'MUL':5,'JUMP':8,'JUMPI':10}
    return sum(t.get(ins[i], 3) for i in idx)
kind = sys.argv[1]
out, blocks, tidx, eidx, entry = gen(kind)
txt = "\n".join(out)
for i,b in enumerate(blocks): txt = txt.replace('{cost%d}'%i, str(cost(b)))
txt = txt.replace('{costT}', str(cost(tidx))).replace('{costE}', str(cost(eidx))).replace('{costI}', str(sum(cost(b) for b in blocks)))
print(txt)
print('-- entry', cost(entry), 'iter', sum(cost(b) for b in blocks), 'tail', cost(tidx), 'exit', cost(eidx))
