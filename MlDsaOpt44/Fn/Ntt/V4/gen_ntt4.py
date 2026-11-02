"""Generator of the v4 `ntt`/`intt` block lemmas and loop bodies
(MlDsaOpt44/Fn/Ntt/V4/{FwdA,FwdB,FwdC,InvC,InvB,InvA}.lean).

Same method as the v3 generator `MlDsaOpt44/Fn/Ntt/gen_ntt.py`: symbolically
execute the kernels of `scripts/opt_ntt.py` (v4: `biased`, `premont`, `post =
uh_word`) over `MlDsaOpt44/listing.tsv`, with stack words as Lean terms in the
normal form `opt44_block` produces; cut each loop body into load / layer /
store blocks and emit one `opt44_reach` lemma per block plus the loop-body
lemma that composes them and discharges the lane semantics (`V4/Step.lean`).

v4 shapes (`opt_ntt.py`, `Kernel.ct`/`gs`, `gen_opt.py` `uh_word`):
* forward: `a' = u + a`, `b' = a − u` (`ftA`/`ftB`), with `u = montU (z b)`
  (table zetas) or `u = shU zs zt b` (Shoup, pass A immediates);
* inverse: `b' = montU (z ((C − a) + b))` (`gsB4`), `a' = b + a` (`gsA`), last
  layer `a' = montU (f (b + a))` (`gsAs`);
* inverse pass A' stores `uh4W x s h` (UseHint against the `SP` word `s` and the
  `HP` word `h` of the stored coefficient), one block per stored word.

Pass heads, layer ends and store ends are found from the listing (labels of
`MlDsaOpt/44/opt.asm`, butterfly completions, `MSTORE` counts).

Run from the repository root: `python3 MlDsaOpt44/Fn/Ntt/V4/gen_ntt4.py [fA fB fC iC iB iA]`
(`uhdef` prints the UseHint word as a Lean term). The hand-written support is
`V4/{Defs,Sem,Step,Ctl,Passes,Top}.lean` and `Math/NttV4.lean`.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.abspath(__file__)) + '/../../../..'
sys.path.insert(0, ROOT + '/scripts')

from opt_ref import ZETAS  # noqa: E402
from opt_ntt import Kernel  # noqa: E402

L = {}
PC = {}
IDX = {}
for line in open(ROOT + '/MlDsaOpt44/listing.tsv'):
    i, pc, ins = line.rstrip('\n').split('\t')
    if i == 'index':
        continue
    L[int(i)] = ins
    PC[int(i)] = int(pc)
    IDX[int(pc)] = int(i)

LAB = {}
_lines = open(ROOT + '/MlDsaOpt/44/opt.asm').read().split('\n')
for _k, _l in enumerate(_lines):
    _m = re.match(r'^(\w+):$', _l)
    if _m and _k + 1 < len(_lines):
        LAB[_m.group(1)] = IDX[int(_lines[_k + 1].split()[0])]

GAS = {'ADD': 3, 'MUL': 5, 'SUB': 3, 'AND': 3, 'SHR': 3, 'GT': 3, 'ISZERO': 3, 'POP': 2,
       'MLOAD': 3, 'MSTORE': 3, 'JUMP': 8, 'JUMPI': 10, 'JUMPDEST': 1}


def cost(ins):
    op = ins.split()[0]
    if op.startswith('PUSH') or op.startswith('DUP') or op.startswith('SWAP'):
        return 3
    return GAS[op]


OUT = ROOT + '/MlDsaOpt44/Fn/Ntt/V4/'
Q = 8380417
QINV = 0xfc7fdfff
M32 = 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
CINV = 0x04007fa80300000004007fa80300000004007fa80300000004007fa803
MEMB = 32 * 2616
ACC, SP, HP = 0xa900, 0x6800, 0xc900


def zm(m):
    return ZETAS[m] * (1 << 32) % Q


# ---------------------------------------------------------------- values
# N: ('lit', n) | ('nv', name) | ('nadd', a, b) | ('nsub', a, b) | ('nop', op, a, b) | ('nshr', v, k)
#    | ('montE', w)
# U: ('var', name) | ('op', op, top, second) | ('montU', t) | ('shU', zs, zt, b) | ('ftA', xa, u)
#    | ('ftB', xa, u) | ('gsA', xa, xb) | ('gsB4', C, xa, xb, z) | ('gsAs', f, xa, xb)
#    | ('uh4', x, s, h)
NK = {'lit', 'nv', 'nadd', 'nsub', 'nop', 'nshr', 'montE'}


def isN(v):
    return v[0] in NK


def lit(n):
    return ('lit', n)


def pn(v):
    """Lean Nat expression of an N value."""
    k = v[0]
    if k == 'lit':
        return str(v[1])
    if k == 'nv':
        return v[1]
    if k == 'nadd':
        return f"({pn(v[1])} + {pn(v[2])})"
    if k == 'nsub':
        return f"({pn(v[1])} - {pn(v[2])})"
    if k == 'nop':
        o = {'mul': '*', 'land': '&&&', 'add': '+'}[v[1]]
        return f"({pn(v[2])} {o} {pn(v[3])})"
    if k == 'montE':
        return f"(montE {pn(v[1])})"
    if k == 'nshr':
        return f"({pn(v[1])} % 2 ^ 256 / 2 ^ {v[2]})"
    raise ValueError(v)


def pu(v):
    """Lean UInt256 expression."""
    if isN(v):
        return f"(UInt256.ofNat {pn(v)})"
    k = v[0]
    if k == 'var':
        return v[1]
    if k == 'montU':
        return f"(montU {pu(v[1])})"
    if k == 'shU':
        return f"(shU {v[1]} {v[2]} {pu(v[3])})"
    if k == 'ftA':
        return f"(ftA {pu(v[1])} {pu(v[2])})"
    if k == 'ftB':
        return f"(ftB {pu(v[1])} {pu(v[2])})"
    if k == 'gsA':
        return f"(gsA {pu(v[1])} {pu(v[2])})"
    if k == 'gsB4':
        return f"(gsB4 {pu(v[1])} {pu(v[2])} {pu(v[3])} {pu(v[4])})"
    if k == 'gsAs':
        return f"(gsAs {pu(v[1])} {pu(v[2])} {pu(v[3])})"
    if k == 'uh4':
        return f"(uh4W {pu(v[1])} {v[2]} {v[3]})"
    if k == 'op':
        o = {'mul': '*', 'add': '+', 'sub': '-'}.get(v[1])
        if o:
            return f"({pu(v[2])} {o} {pu(v[3])})"
        if v[1] == 'land':
            return f"(UInt256.land {pu(v[2])} {pu(v[3])})"
        if v[1] == 'shr':
            return f"(UInt256.shiftRight {pu(v[2])} {pu(v[3])})"
    raise ValueError(v)


def mont_arg(v):
    """If v (U) is the raw Montgomery reduction of t, return t."""
    if v[0] != 'op' or v[1] != 'shr' or v[3] != lit(32):
        return None
    ad = v[2]
    if ad[0] != 'op' or ad[1] != 'add':
        return None
    mu, t = ad[2], ad[3]
    if mu[0] != 'op' or mu[1] != 'mul' or mu[2] != lit(Q):
        return None
    an = mu[3]
    if an[0] != 'op' or an[1] != 'land' or an[2] != lit(M32):
        return None
    mq = an[3]
    if mq[0] != 'op' or mq[1] != 'mul' or mq[2] != lit(QINV):
        return None
    an2 = mq[3]
    if an2[0] != 'op' or an2[1] != 'land' or an2[2] != lit(M32) or an2[3] != t:
        return None
    return t


def montE_arg(v):
    if v[0] != 'nshr' or v[2] != 32:
        return None
    ad = v[1]
    if ad[0] != 'nadd':
        return None
    mu, w = ad[1], ad[2]
    if mu != ('nop', 'mul', lit(Q), ('nop', 'land', lit(M32), ('nop', 'mul', lit(QINV), ('nop', 'land', lit(M32), w)))):
        return None
    return w


def shoup_zs(a, b):
    """`zt * xb − q * (M32 & ((zs * xb) >> 32))` (a = top, b = second): return zs."""
    if not (a[0] == 'op' and a[1] == 'mul' and a[2][0] == 'lit' and a[3][0] == 'var'):
        return None
    if not (b[0] == 'op' and b[1] == 'mul' and b[2] == lit(Q)):
        return None
    an = b[3]
    if not (an[0] == 'op' and an[1] == 'land' and an[2] == lit(M32)):
        return None
    sh = an[3]
    if not (sh[0] == 'op' and sh[1] == 'shr' and sh[3] == lit(32)):
        return None
    mu = sh[2]
    if not (mu[0] == 'op' and mu[1] == 'mul' and mu[2][0] == 'lit' and mu[3] == a[3]):
        return None
    return mu[2][1]


def is_u(v):
    return v[0] in ('montU', 'shU') and (v[0] == 'shU' or (v[1][0] == 'op' and v[1][1] == 'mul'))


def binop(op, a, b):
    """a = top, b = second."""
    if isN(a) and isN(b):
        if a[0] == 'lit' and b[0] == 'lit':
            f = {'add': lambda x, y: x + y, 'mul': lambda x, y: x * y, 'land': lambda x, y: x & y}[op]
            return lit(f(a[1], b[1]) % (1 << 256))
        if op == 'add':
            return ('nadd', a, b)
        return ('nop', op, a, b)
    if op == 'add':
        if is_u(a) and b[0] == 'var':
            return ('ftA', b, a)
        if a[0] == 'var' and b[0] == 'var':
            return ('gsA', b, a)
    return ('op', op, a, b)


def emulate(start, end, stack, hyps):
    """stack top first. hyps: map Lean address string -> N value name for MLOAD.
    Returns (indices, cost, stack, stores)."""
    st = list(stack)
    idx, c, stores = [], 0, []
    for i in range(start, end):
        ins = L[i]
        idx.append(i)
        c += cost(ins)
        p = ins.split()
        op = p[0]
        if op.startswith('PUSH'):
            st.insert(0, lit(int(p[1], 16)))
        elif op.startswith('DUP'):
            st.insert(0, st[int(op[3:]) - 1])
        elif op.startswith('SWAP'):
            n = int(op[4:])
            st[0], st[n] = st[n], st[0]
        elif op == 'JUMPDEST':
            pass
        elif op in ('ADD', 'MUL', 'AND'):
            a, b = st.pop(0), st.pop(0)
            st.insert(0, binop({'ADD': 'add', 'MUL': 'mul', 'AND': 'land'}[op], a, b))
        elif op == 'SUB':
            a, b = st.pop(0), st.pop(0)
            r = ('op', 'sub', a, b)
            if a[0] == 'nv' and b[0] == 'lit':
                r = ('nsub', a, b)      # pointer minus offset (discharged from a hypothesis)
            elif a[0] == 'var' and is_u(b):
                r = ('ftB', a, b)
            else:
                zs = shoup_zs(a, b)
                if zs is not None:
                    r = ('shU', zs, a[2][1], a[3])
            st.insert(0, r)
        elif op == 'SHR':
            a, b = st.pop(0), st.pop(0)
            if isN(a) and isN(b):
                r = ('nshr', b, a[1])
                w = montE_arg(r)
                if w is not None:
                    r = ('montE', w)
            else:
                r = ('op', 'shr', b, a)
                t = mont_arg(r)
                if t is not None:
                    r = ('montU', t)
                    if t[0] == 'op' and t[1] == 'mul':
                        z, d = t[2], t[3]
                        if (d[0] == 'op' and d[1] == 'add' and d[2][0] == 'op' and d[2][1] == 'sub'
                                and isN(d[2][2]) and d[2][3][0] == 'var' and d[3][0] == 'var'):
                            r = ('gsB4', d[2][2], d[2][3], d[3], z)
                        elif d[0] == 'gsA':
                            r = ('gsAs', z, d[1], d[2])
            st.insert(0, r)
        elif op == 'MLOAD':
            a = st.pop(0)
            key = pn(a)
            if key in hyps:
                st.insert(0, ('nv', hyps[key]))
            else:
                raise ValueError(f"unmapped MLOAD at {i}: {key}")
        elif op == 'MSTORE':
            a, v = st.pop(0), st.pop(0)
            stores.append((a, v))
        elif op == 'POP':
            st.pop(0)
        else:
            raise ValueError(f"control op {op} at {i}")
    return idx, c, st, stores


def u_b(u):
    """The multiplied operand of a forward `u`."""
    return u[3] if u[0] == 'shU' else u[1][3]


def slot_of(v):
    k = v[0]
    if k == 'ftA':
        return v[1][1]
    if k == 'ftB':
        return u_b(v[2])[1]
    if k == 'gsA':
        return v[1][1]
    if k == 'gsB4':
        return v[3][1]
    if k == 'gsAs':
        return v[2][1]
    raise ValueError(v)


def bfly_of(v):
    """(kind, slot a, slot b, zeta info) of an output word; None for a-outputs
    of the inverse (their butterfly is listed with the b-output)."""
    k = v[0]
    if k in ('ftA', 'ftB'):
        xa = v[1][1]
        u = v[2]
        if u[0] == 'shU':
            return ('cts', xa, u[3][1], (u[1], u[2]))
        return ('ctm', xa, u[1][3][1], u[1][2])
    if k == 'gsA':
        return None
    if k == 'gsB4':
        return ('gs', v[2][1], v[3][1], v[4])
    if k == 'gsAs':
        return ('gsS', v[2][1], v[3][1], v[1])
    raise ValueError(v)


def is_bout(v):
    """A butterfly's b-output (completes the butterfly)."""
    return v[0] in ('ftB', 'gsB4')


def stack_text(st):
    return ' :: '.join(pu(v) for v in st)


HDR = """import MlDsaOpt44.Fn.Ntt.V4.Step
/-! Generated by `MlDsaOpt44/Fn/Ntt/V4/gen_ntt4.py` (v4 `ntt`/`intt`, MlDsaOpt/44/opt.asm): {title}. -/

namespace MlDsaOpt44.Proofs.Ntt4

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs MlDsaOpt44.Proofs.NttW

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
"""

SIMP_DEFS = "montU, shU, ftA, ftB, gsA, gsB4, gsAs, uh4W, uF, uV, uD, uY, uQ, uX, wrU, montE"


def block_lemma(name, start, end, pre, hyps_map, nat_params, uint_params, hyps, extra_simp, mem_ops,
                post_override=None, mem_params='(mem : ByteArray)', pre_tac=''):
    idx, c, post, stores = emulate(start, end, pre, hyps_map)
    if post_override:
        post, stores = post_override(post, stores)
    pc0, pc1 = PC[start], PC[end]
    mem_post = 'mem'
    for a, v in stores:
        mem_post = f"(wrU {mem_post} {pn(a)} {pu(v)})"
    params = ''
    if nat_params:
        params += f" ({' '.join(nat_params)} : Nat)"
    if uint_params:
        params += f" ({' '.join(uint_params)} : UInt256)"
    hs_ = ''.join(f"\n    ({h})" for h in hyps)
    simp = ', '.join([SIMP_DEFS] + extra_simp)
    txt = f"""
theorem {name} {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)
    {mem_params}{params}{hs_} :
    Reach (callState s {pc0} ({stack_text(pre)} :: tail) mem)
      (callState s {pc1} ({stack_text(post)} :: tail) {mem_post}) {c} := by
"""
    txt += pre_tac
    if mem_ops:
        txt += "  have hmw := hs.sized; unfold memWords at hmw\n"
    txt += f"  opt44_reach [{', '.join(map(str, idx))}] with [{simp}]\n"
    return txt, post, c, stores


def projB(u):
    return '.1' if u == 0 else '.2' * u + ('.1' if u < 6 else '')


def projC(u):
    return '.1' if u == 0 else '.2' * u + ('.1' if u < 2 else '')


M_B = ['8 + {b}', '16 + 2 * {b}', '17 + 2 * {b}', '32 + 4 * {b}', '32 + 4 * {b} + 1', '32 + 4 * {b} + 2',
       '32 + 4 * {b} + 3']
M_C = ['64 + {b}', '128 + 2 * {b}', '129 + 2 * {b}']


def rec_val(kind, b, u):
    if kind == 'B':
        return f"nttRec (7 * {b})" if u == 0 else f"nttRec (7 * {b} + {u})"
    return f"nttRec (56 + 3 * {b})" if u == 0 else f"nttRec (56 + 3 * {b} + {u})"


def rec_index(kind, b, u):
    if kind == 'B':
        return f"7 * {b}" if u == 0 else f"7 * {b} + {u}"
    return f"56 + 3 * {b}" if u == 0 else f"56 + 3 * {b} + {u}"


IMM_M = {}
for _m in range(1, 256):
    IMM_M.setdefault(zm(_m), _m)
SHOUP_M = {(Kernel.shoup(m), ZETAS[m]): m for m in range(1, 8)}

CIN = lit(CINV)
M32N = lit(M32)

FWD_ST = lambda X: [('nv', 'pj'), ('nv', X), M32N, lit(32768), ('nv', 'ret')]
INV_ST = lambda X: [('nv', 'pj'), ('nv', X), CIN, M32N, lit(43264), ('nv', 'ret')]

PASSES = [
    dict(name='fA', title='forward pass A (layers 1-3, Shoup)', head='ntta_1',
         nw=8, off=1024, P=32768, X='e', Xn='33792', ctl=FWD_ST, premont=False, tbl=None, kind='ct', L0=0,
         n='c', nbound='32', pj='32768 + 32 * c', slot='c + 32 * {i}',
         D='t % 32 < {n}', S='t % 32 = c', dec='⟨t / 32, by omega⟩', model='fwd'),
    dict(name='fB', title='forward pass B (layers 4-6)', head='nttb_2',
         nw=8, off=128, P=32768, X='zb', Xn='4096 + 224 * (n / 4)', ctl=FWD_ST, premont=False, tbl='B',
         rb='(n / 4)', kind='ct', L0=3, n='n', nbound='32', pj='32768 + 1024 * (n / 4) + 32 * (n % 4)',
         slot='32 * (n / 4) + n % 4 + 4 * {i}', D='4 * (t / 32) + t % 4 < {n}',
         S='t / 32 = n / 4 ∧ t % 4 = n % 4', dec='⟨t % 32 / 4, by omega⟩', model='fwd'),
    dict(name='fC', title='forward pass C (layers 7-8)', head='nttc_4',
         nw=4, off=32, P=32768, X='zc', Xn='5888 + 96 * n', ctl=FWD_ST, premont=False, tbl='C', rb='n',
         kind='ct', L0=6, n='n', nbound='64', pj='32768 + 128 * n', slot='4 * n + {i}',
         D='t / 4 < {n}', S='t / 4 = n', dec='⟨t % 4, by omega⟩', model='fwd'),
    dict(name='iC', title='inverse pass C (layers 1-2, premont)', head='intc_5',
         nw=4, off=32, P=43264, X='zc', Xn='11936 - 96 * n', ctl=INV_ST, premont=True, tbl='C', rb='(63 - n)',
         kind='gs', L0=0, n='n', nbound='64', pj='43264 + 128 * n', slot='4 * n + {i}',
         D='t / 4 < {n}', S='t / 4 = n', dec='⟨t % 4, by omega⟩', model='inv',
         Pre='(fun t w => LOK (UInt256.ofNat w) (2 ^ 57) (fun k => h k t))',
         Post='(fun t w => LOK (UInt256.ofNat w) (Bi 2) (fun k => invL (scaleR h k) 2 t))'),
    dict(name='iB', title='inverse pass B (layers 3-5)', head='intb_6',
         nw=8, off=128, P=43264, X='zb', Xn='5664 - 224 * (n / 4)', ctl=INV_ST, premont=False, tbl='B',
         rb='(7 - n / 4)', kind='gs', L0=2, n='n', nbound='32', pj='43264 + 1024 * (n / 4) + 32 * (n % 4)',
         slot='32 * (n / 4) + n % 4 + 4 * {i}', D='4 * (t / 32) + t % 4 < {n}',
         S='t / 32 = n / 4 ∧ t % 4 = n % 4', dec='⟨t % 32 / 4, by omega⟩', model='inv',
         Pre='(fun t w => LOK (UInt256.ofNat w) (Bi 2) (fun k => invL (scaleR h k) 2 t))',
         Post='(fun t w => LOK (UInt256.ofNat w) (Bi 5) (fun k => invL (scaleR h k) 5 t))'),
    dict(name='iA', title='inverse pass A (layers 6-8, scaling, UseHint)', head='inta_7',
         nw=8, off=1024, P=43264, X='e', Xn='44288', ctl=INV_ST, premont=False, tbl=None, kind='gs', L0=5,
         n='c', nbound='32', pj='43264 + 32 * c', slot='c + 32 * {i}',
         D='t % 32 < {n}', S='t % 32 = c', dec='⟨t / 32, by omega⟩', model='inv',
         Pre='(fun t w => LOK (UInt256.ofNat w) (Bi 5) (fun k => invL (scaleR h k) 5 t))',
         Post='(fun t w => UHP m0 t w (fun k => Sc * invL (scaleR h k) 8 t))'),
]
PASS = {p['name']: p for p in PASSES}
for _p in PASSES:
    if _p['model'] == 'fwd':
        L0 = _p['L0']
        nl = 3 if _p['nw'] == 8 else 2
        _p['Pre'] = f"(fun t w => LI (UInt256.ofNat w) {L0} (fun k => fwdL (h k) {L0} t))"
        _p['Post'] = f"(fun t w => LI (UInt256.ofNat w) {L0 + nl} (fun k => fwdL (h k) {L0 + nl} t))"


def layer_end(start, nw, cur, zhyps):
    """Index (exclusive) where the layer starting at `start` (operands `cur` are
    vars) completes its last butterfly."""
    st = list(cur)
    done = 0
    i = start
    while True:
        _, _, st, _ = emulate(i, i + 1, st, zhyps)
        i += 1
        if st and is_bout(st[0]):
            done += 1
            if done == nw // 2:
                return i


def to_vars(post, nw):
    return [('var', f"x{int(slot_of(v)[1:])}") for v in post[:nw]] + post[nw:]


def layer_ends(start, nw, nlayers, cur, zhyps):
    ends = []
    for _ in range(nlayers):
        e = layer_end(start, nw, cur, zhyps)
        ends.append(e)
        _, _, post, _ = emulate(start, e, cur, zhyps)
        cur = to_vars(post, nw)
        start = e
    return ends


class AnyZ(dict):
    """MLOAD map for probing: any address is a fresh zeta name."""

    def __contains__(self, key):
        return True

    def __getitem__(self, key):
        return 'zz'


def gen_blocks(ps):
    name, nw, off, P = ps['name'], ps['nw'], ps['off'], ps['P']
    ctl = ps['ctl'](ps['X'])
    out = ''
    head = LAB[ps['head']]
    k, i = 0, head
    while k < nw:
        if L[i] == 'MLOAD':
            k += 1
        i += 1
    load_end = i + (12 if ps['premont'] else 0)
    addrs = ['pj'] + [f"({off * j} + pj)" for j in range(1, nw)]
    hmap = {a: f"w{j}" for j, a in enumerate(addrs)}
    hyps = [f"hpj : pj + {off * (nw - 1) + 32} ≤ {MEMB}"] + [f"hw{j} : word mem {a} = w{j}" for j, a in enumerate(addrs)]
    txt, post, cld, _ = block_lemma(f"{name}_ld", head, load_end, ctl, hmap,
                                    ['pj', ps['X'], 'ret'] + [f"w{j}" for j in range(nw)], [], hyps,
                                    [f"hw{j}" for j in range(nw)], True)
    out += txt
    costs = [cld]

    def slot_load(v):
        if v[0] == 'nv':
            return int(v[1][1:])
        if v[0] == 'montE':
            return int(v[1][1][1:])
        raise ValueError(v)

    cur = [('var', f"x{slot_load(v)}") for v in post[:nw]] + post[nw:]
    nlayers = 3 if nw == 8 else 2
    ends = layer_ends(load_end, nw, nlayers, cur, AnyZ())
    layers = []
    start = load_end
    zaddrs = None
    if ps['tbl']:
        zoff = [0, 32, 64, 96, 128, 160, 192] if ps['tbl'] == 'B' else [0, 32, 64]
        zaddrs = {(ps['X'] if o == 0 else f"({o} + {ps['X']})"): u for u, o in enumerate(zoff)}
    for li, e in enumerate(ends):
        zmap, zhyps, zparams, zsimp, zus = {}, [], [], [], []
        if zaddrs:
            used = set()

            class Rec(dict):
                def __contains__(self, key):
                    return key in zaddrs

                def __getitem__(self, key):
                    used.add(key)
                    return f"z{zaddrs[key]}"
            emulate(start, e, cur, Rec())
            for a in sorted(used, key=lambda a: zaddrs[a]):
                u = zaddrs[a]
                zmap[a] = f"z{u}"
                zparams.append(f"z{u}")
                zus.append(u)
                zhyps.append(f"hz{u} : word mem {a} = z{u}")
                zsimp.append(f"hz{u}")
            zhyps = [f"hX : {ps['X']} + 224 ≤ {MEMB}"] + zhyps
        txt, post, cl, _ = block_lemma(f"{name}_l{li + 1}", start, e, cur, zmap,
                                       ['pj', ps['X'], 'ret'] + zparams, [f"x{j}" for j in range(nw)], zhyps,
                                       zsimp, bool(zaddrs))
        out += txt
        costs.append(cl)
        bfs = []
        for v in post[:nw]:
            bf = bfly_of(v)
            if bf is None:
                continue
            prev = [j for j, b in enumerate(bfs) if (b[1], b[2]) == (bf[1], bf[2])]
            if not prev:
                bfs.append(bf)
            elif bf[0] == 'gsS':
                bfs[prev[0]] = bf          # the scaled last layer: a' = mont(f (b + a))
        assert len(bfs) == nw // 2, (name, li, bfs)
        layers.append((bfs, zus))
        cur = to_vars(post, nw)
        start = e
    # stores: up to the nw-th MSTORE
    k, i = 0, start
    while k < nw:
        if L[i] == 'MSTORE':
            k += 1
        i += 1
    ctl_i = i
    sthyp = [f"hpj : pj + {off * (nw - 1) + 32} ≤ {MEMB}"]
    st_blocks = []
    if ps['name'] != 'iA':
        txt, post, cst, stores = block_lemma(f"{name}_st", start, ctl_i, cur, {},
                                             ['pj', ps['X'], 'ret'], [f"x{j}" for j in range(nw)],
                                             sthyp, [], True)
        out += txt
        costs.append(cst)
        st_blocks.append((f"{name}_st", stores, []))
    else:
        # one block per stored word: uh4W of the top word, then MSTORE
        s0 = start
        rest = list(cur)
        for j in range(nw):
            e = s0
            while L[e] != 'MSTORE':
                e += 1
            e += 1
            x = rest[0]
            xi = int(x[1][1:])
            # SP read: pj - d, HP read: c + pj
            soff = ACC - SP - off * xi
            hoff = HP - ACC + off * xi
            skey = f"(pj - {soff})"
            hkey = f"({hoff} + pj)"
            hm = {skey: 'sv', hkey: 'hv'}
            tmpl = uh_tree(x)

            def override(post, stores, tmpl=tmpl, x=x):
                assert len(stores) == 1 and stores[0][1] == tmpl, (stores, tmpl)
                return post, [(stores[0][0], ('uh4', x, 'sv', 'hv'))]
            vs = [f"x{int(v[1][1:])}" for v in rest[:nw - j]]
            hy = [f"hpj : pj + {HP - ACC + off * (nw - 1) + 32} ≤ {MEMB}", f"hpj0 : {soff} ≤ pj",
                  f"hpA : {ACC} ≤ pj", f"hpB : pj < {ACC + 1024}",
                  f"hF : FrameExcept M0 mem [({ACC}, {ACC} + 8192)]",
                  f"hsv0 : word M0 (pj - {soff}) = sv", f"hhv0 : word M0 ({hoff} + pj) = hv"]
            ptac = (f"  have hsv : word mem (pj - {soff}) = sv := (FrameExcept.word hF (by\n"
                    f"    simp only [avoids_cons, avoids_nil, and_true]; omega)).trans hsv0\n"
                    f"  have hhv : word mem ({hoff} + pj) = hv := (FrameExcept.word hF (by\n"
                    f"    simp only [avoids_cons, avoids_nil, and_true]; omega)).trans hhv0\n")
            txt, post, cst, stores = block_lemma(f"{name}_st{j}", s0, e, rest, hm,
                                                 ['pj', ps['X'], 'ret', 'sv', 'hv'], vs, hy,
                                                 ['hsv', 'hhv'], True, override,
                                                 '(mem M0 : ByteArray)', ptac)
            out += txt
            costs.append(cst)
            st_blocks.append((f"{name}_st{j}", stores, [x, soff, hoff, vs]))
            rest = post
            s0 = e
        assert s0 == ctl_i
    return out, layers, costs, st_blocks, ctl_i


def _subst(t, x):
    if t == ('var', 'X'):
        return x
    if isinstance(t, tuple):
        return tuple(_subst(a, x) for a in t)
    return t


def uh_tree(x):
    """The tree uh_word builds for word x (MLOAD names sv, hv): the template of
    word 0 with X := x. Every stored word must match it (`Ntt4.uh4W`)."""
    return _subst(UH_TEMPLATE, x)


def _uh_template():
    """Emulate word 0's uh_word of pass A' (from the end of the last layer up to
    its MSTORE) with x abstract."""
    ps = PASS['iA']
    # find the store start: end of the third layer
    head = LAB[ps['head']]
    k, i = 0, head
    while k < 8:
        if L[i] == 'MLOAD':
            k += 1
        i += 1
    cur = [('var', f"x{j}") for j in range(8)] + INV_ST('e')
    ends = layer_ends(i, 8, 3, cur, AnyZ())
    s0 = ends[-1]
    e = s0
    while L[e] != 'MSTORE':
        e += 1
    # the top word becomes X
    stk = [('var', 'X')] + [('var', f"y{j}") for j in range(1, 8)] + INV_ST('e')

    class Any(dict):
        def __contains__(self, key):
            return True

        def __getitem__(self, key):
            return 'sv' if '-' in key else 'hv'
    _, _, post, stores = emulate(s0, e + 1, stk, Any())
    assert len(stores) == 1 and pn(stores[0][0]) == '(7168 + pj)', stores[0][0]
    return stores[0][1]


UH_TEMPLATE = _uh_template()


def uh_def():
    """Lean text of the template (compare with `uh4W` in `V4/Defs.lean`)."""
    t = UH_TEMPLATE
    return pu(t).replace('(UInt256.ofNat sv)', '(UInt256.ofNat s)').replace('(UInt256.ofNat hv)', '(UInt256.ofNat h)') \
        .replace(' X', ' x').replace('(X ', '(x ')


CIT = str(CINV)
M32T = str(M32)


def head_stack(ps, pjexpr, Xexpr):
    if ps['model'] == 'fwd':
        return (f"UInt256.ofNat ({pjexpr}) :: UInt256.ofNat ({Xexpr}) :: "
                f"UInt256.ofNat {M32T} :: UInt256.ofNat {ps['P']} :: UInt256.ofNat ret :: tail")
    return (f"UInt256.ofNat ({pjexpr}) :: UInt256.ofNat ({Xexpr}) :: UInt256.ofNat {CIT} :: "
            f"UInt256.ofNat {M32T} :: UInt256.ofNat {ps['P']} :: UInt256.ofNat ret :: tail")


def gen_body(ps, layers, costs, st_blocks, ctl_i):
    name, nw, off, P = ps['name'], ps['nw'], ps['off'], ps['P']
    n = ps['n']
    slot = lambda i: ps['slot'].format(i=i)
    D0 = ps['D'].format(n=n)
    D1 = ps['D'].format(n=f"{n} + 1")
    hb = f"(h{n} : {n} < {ps['nbound']})"
    tbl = " (htbl : TblAt M)" if ps['tbl'] else ""
    uh = ps['name'] == 'iA'
    inv = f"PI M {P} (fun t => {{D}}) {ps['Pre']} {ps['Post']}"
    hs = head_stack(ps, ps['pj'], ps['Xn'])
    cost = sum(costs)
    extra = ''
    if uh:
        extra = (f"\n    (m0 : ByteArray) (hF : FrameExcept m0 M [({P}, {P} + 8192)])"
                 f"\n    (hSH : H → ∀ t, t < 256 → ∀ r, r < 4 → lane (word m0 (SP + 32 * t)) r ≤ spOff ∧"
                 f"\n      lane (word m0 (HP + 32 * t)) r ≤ 1)")
    out = f"""
theorem {name}_body {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)
    (ret : Nat) (H : Prop) (h : Nat → Nat → F) ({n} : Nat) {hb} (M : ByteArray){tbl}{extra}
    (hP : H → {inv.format(D=D0)}) :
    ∃ M', (H → {inv.format(D=D1).replace('PI M ', "PI M' ")}) ∧
      FrameExcept M M' [({P}, {P} + 8192)] ∧
      Reach (callState s {PC[LAB[ps['head']]]} ({hs}) M)
        (callState s {PC[ctl_i]} ({hs}) M') {cost} := by
"""
    pj, X = ps['pj'], ps['Xn']
    ws = ' '.join(f"(word M ({P} + 32 * ({slot(i)})))" for i in range(nw))
    hws = ' '.join("(congrArg (word M) (by omega))" for i in range(nw))
    parts = [f"({name}_ld hs htail M ({pj}) ({X}) ret {ws} (by omega) {hws})"]
    for li, (bfs, zus) in enumerate(layers):
        zv = ' '.join(f"({rec_val(ps['tbl'], ps['rb'], u)})" for u in zus)
        hz = ' '.join(f"(by rw [← htbl ({rec_index(ps['tbl'], ps['rb'], u)}) (by omega)]; congr 1; unfold TBL; omega)"
                      for u in zus)
        xs = ' '.join('_' for _ in range(nw))
        extra_args = f" (by omega) {hz}" if ps['tbl'] else ""
        parts.append(f"({name}_l{li + 1} hs htail M ({pj}) ({X}) ret {zv} {xs}{extra_args})")
    if not uh:
        xs = ' '.join('_' for _ in range(nw))
        parts.append(f"({name}_st hs htail M ({pj}) ({X}) ret {xs} (by omega))")
    else:
        for j, (bn, stores, (x, soff, hoff, vs)) in enumerate(st_blocks):
            xi = int(x[1][1:])
            sv = f"(word M (SP + 32 * ({slot(xi)})))"
            hv = f"(word M (HP + 32 * ({slot(xi)})))"
            xs = ' '.join('_' for _ in vs)
            parts.append(f"({bn} hs htail _ M ({pj}) ({X}) ret {sv} {hv} {xs} (by omega) (by omega) "
                         f"(by omega) (by omega)\n      (by repeat (first | exact FrameExcept.refl _ _ | "
                         f"refine frame_wrU _ ?_ (by omega) (by omega)))\n"
                         f"      (congrArg (word M) (by unfold SP; omega)) (congrArg (word M) (by unfold HP; omega)))")
    r = parts[-1]
    for p in reversed(parts[:-1]):
        r = f"({p}.trans\n    {r})"
    out += f"  have hR := {r}\n"
    out += "  refine ⟨_, fun hH => ?sem, ?frm, hR.mono (by norm_num)⟩\n"
    out += "  case frm =>\n    repeat (first | exact FrameExcept.refl _ _ | refine frame_wrU _ ?_ (by omega) (by omega))\n"
    out += "  case sem =>\n    have hI := hP hH\n"
    for i in range(nw):
        f = f"passInvG_pre hI (t := {slot(i)}) (by omega) (by omega)"
        if ps['premont']:
            f = f"premont_step h ({slot(i)}) _ (({f}).mono (by norm_num))"
        out += f"    have v0_{i} := {f}\n"
    for li, (bfs, zus) in enumerate(layers):
        Lr = ps['L0'] + li
        for (kind, a, b, z) in bfs:
            a, b = int(a[1:]), int(b[1:])
            ia, ib = slot(a), slot(b)
            if kind == 'gsS':
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gsS4_step (scaleR h) ({ia}) ({ib}) (by omega) "
                        f"(by omega) v{li}_{a} v{li}_{b}\n")
                continue
            if kind == 'cts':
                zs, zt = z
                m = SHOUP_M[(zs, zt)]
                ln = 128 >> Lr
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := ct4s_step h {Lr} {ln} ({ia}) ({ib}) {m} "
                        f"(by norm_num) (by norm_num) (by omega) (by omega) (by omega) shoup{m} "
                        f"v{li}_{a} v{li}_{b}\n")
                continue
            if z[0] == 'lit':
                m = IMM_M[z[1]]
                mexpr, zexpr, hz = str(m), str(z[1]), f"zmi{m}.symm"
            else:
                u = int(z[1][1:])
                Mt = M_B if ps['tbl'] == 'B' else M_C
                mexpr = Mt[u].format(b=ps['rb'])
                zexpr = rec_val(ps['tbl'], ps['rb'], u)
                rl = 'recB' if ps['tbl'] == 'B' else 'recC'
                pr = projB(u) if ps['tbl'] == 'B' else projC(u)
                hz = f"(({rl} (b := {ps['rb']}) (by omega)){pr})"
            if ps['model'] == 'fwd':
                ln = 128 >> Lr
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := ct4m_step h {Lr} {ln} ({ia}) ({ib}) ({mexpr}) "
                        f"({zexpr}) (by norm_num) (by norm_num) (by omega) (by omega) (by omega) {hz} "
                        f"v{li}_{a} v{li}_{b}\n")
            else:
                ln = 1 << Lr
                m0 = 1 << (8 - Lr)
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gs4_step (scaleR h) {Lr} {ln} {m0} ({ia}) ({ib}) "
                        f"({mexpr}) ({zexpr}) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) "
                        f"(by omega) {hz} v{li}_{a} v{li}_{b}\n")
    nl = len(layers)
    S = ps['S']
    if uh:
        # SP / HP words of m0 at the stored positions
        for i in range(nw):
            out += (f"    have u_{i} := uh_store (hSH hH) hF (t := {slot(i)}) (by omega) v{nl}_{i}\n")
    out += f"""    refine passInvG_store hI (S := fun t => {S}) (fun t => by omega) ?new ?old
    case old =>
      intro t ht hS
      simp (disch := omega) only [word_wrU, if_neg]
    case new =>
      intro t ht hS
      obtain ⟨i, rfl⟩ : ∃ i, t = {slot('i')} := {ps['dec']}
      have hi : i < {nw} := by omega
      rw [show {P} + 32 * ({slot('i')}) =
        {32 * off // 32} * i + ({pj}) by omega]
      interval_cases i
"""
    fin = 'u' if uh else f"v{nl}"
    for i in range(nw):
        out += (f"      · simp (disch := with_unfolding_all rfl) only [word_wrU_add_eq, word_wrU_add_ne, "
                f"word_wrU_base_eq, word_wrU_base_ne, ofNat_toNat]; exact {fin}_{i}\n")
    return out


def gen_file(ps):
    blocks, layers, costs, st_blocks, ctl_i = gen_blocks(ps)
    out = HDR.format(title=ps['title'])
    out += blocks
    out += gen_body(ps, layers, costs, st_blocks, ctl_i)
    return out, costs, ctl_i


if __name__ == '__main__':
    which = sys.argv[1:]
    if which == ['uhdef']:
        print(uh_def())
        sys.exit(0)
    for ps in PASSES:
        if which and ps['name'] not in which:
            continue
        txt, c, ctl_i = gen_file(ps)
        fn = {'fA': 'FwdA', 'fB': 'FwdB', 'fC': 'FwdC', 'iC': 'InvC', 'iB': 'InvB', 'iA': 'InvA'}[ps['name']]
        open(OUT + fn + '.lean', 'w').write(txt)
        print(fn, c, sum(c), 'head', LAB[ps['head']], PC[LAB[ps['head']]], 'ctl', ctl_i, PC[ctl_i])
