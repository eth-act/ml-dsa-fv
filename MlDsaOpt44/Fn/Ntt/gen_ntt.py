"""Generator of the WP7 `ntt`/`intt` block lemmas, loop bodies (MlDsaOpt44/Fn/Ntt/{Fwd,Inv}{A,B,C}.lean).

Symbolically executes the kernels of `scripts/opt_ntt.py` over `MlDsaOpt44/listing.tsv`
(stack words as Lean terms in the normal form `opt44_block` produces), cuts each loop body
into load / layer / store blocks, and emits the per-block `opt44_reach` lemmas plus the
loop-body lemma that composes them and discharges the lane semantics (`ct_step`, `gs_step`,
`gsS_step`, `premont_step`, `passInv_store`).

Run from the repository root: `python3 MlDsaOpt44/Fn/Ntt/gen_ntt.py`.
"""
import os
import sys

ROOT = os.path.dirname(os.path.abspath(__file__)) + '/../../..'
sys.path.insert(0, ROOT + '/scripts')

L = {}
PC = {}
for line in open(ROOT + '/MlDsaOpt44/listing.tsv'):
    i, pc, ins = line.rstrip('\n').split('\t')
    if i == 'index':
        continue
    L[int(i)] = ins
    PC[int(i)] = int(pc)

GAS = {'ADD': 3, 'MUL': 5, 'SUB': 3, 'AND': 3, 'SHR': 3, 'GT': 3, 'ISZERO': 3, 'POP': 2,
       'MLOAD': 3, 'MSTORE': 3, 'JUMP': 8, 'JUMPI': 10, 'JUMPDEST': 1}


def cost(ins):
    op = ins.split()[0]
    if op.startswith('PUSH') or op.startswith('DUP') or op.startswith('SWAP'):
        return 3
    return GAS[op]

OUT = ROOT + '/MlDsaOpt44/Fn/Ntt/'
Q = 8380417
QINV = 0xfc7fdfff
M32 = 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
C2 = 0xffc0020000000000ffc0020000000000ffc0020000000000ffc002
CINV = 0x04007fa80300000004007fa80300000004007fa80300000004007fa803
from opt_ref import ZETAS


def zm(m):
    return ZETAS[m] * (1 << 32) % Q


# ---------------------------------------------------------------- values
# N: ('lit', n) | ('nv', name) | ('nadd', a, b) | ('nop', op, a, b) | ('nshr', v, k) | ('montE', w) | ('word', addr)
# U: ('var', name) | ('op', op, a, b) | ('montU', t) | ('ctA', a, b, z) | ('ctB', C, a, b, z)
#    | ('gsA', a, b) | ('gsB', C, a, b, z) | ('gsAs', f, a, b)
NK = {'lit', 'nv', 'nadd', 'nop', 'nshr', 'montE', 'word'}


def isN(v):
    return v[0] in NK


def pn(v):
    """Lean Nat expression of an N value."""
    k = v[0]
    if k == 'lit':
        return str(v[1])
    if k == 'nv':
        return v[1]
    if k == 'nadd':
        return f"({pn(v[1])} + {pn(v[2])})"
    if k == 'nop':
        o = {'mul': '*', 'land': '&&&', 'add': '+'}[v[1]]
        return f"({pn(v[2])} {o} {pn(v[3])})"
    if k == 'montE':
        return f"(montE {pn(v[1])})"
    if k == 'word':
        return f"(word mem {pn(v[1])})"
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
    if k == 'ctA':
        return f"(ctA {pu(v[1])} {pu(v[2])} {pu(v[3])})"
    if k == 'ctB':
        return f"(ctB {pu(v[1])} {pu(v[2])} {pu(v[3])} {pu(v[4])})"
    if k == 'gsA':
        return f"(gsA {pu(v[1])} {pu(v[2])})"
    if k == 'gsB':
        return f"(gsB {pu(v[1])} {pu(v[2])} {pu(v[3])} {pu(v[4])})"
    if k == 'gsAs':
        return f"(gsAs {pu(v[1])} {pu(v[2])} {pu(v[3])})"
    if k == 'op':
        o = {'mul': '*', 'add': '+', 'sub': '-'}.get(v[1])
        if o:
            return f"({pu(v[2])} {o} {pu(v[3])})"
        if v[1] == 'land':
            return f"(UInt256.land {pu(v[2])} {pu(v[3])})"
        if v[1] == 'shr':
            return f"(UInt256.shiftRight {pu(v[2])} {pu(v[3])})"
    raise ValueError(v)


def lit(n):
    return ('lit', n)


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
    # ('nshr', ('nadd', ('nop','mul', q, ('nop','land', M, ('nop','mul', QINV, ('nop','land', M, w))))), w), 32)
    if v[0] != 'nshr' or v[2] != 32:
        return None
    ad = v[1]
    if ad[0] != 'nadd':
        return None
    mu, w = ad[1], ad[2]
    if mu != ('nop', 'mul', lit(Q), ('nop', 'land', lit(M32), ('nop', 'mul', lit(QINV), ('nop', 'land', lit(M32), w)))):
        return None
    return w


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
        # ctA: montU (z * xb) + xa
        if a[0] == 'montU' and a[1][0] == 'op' and a[1][1] == 'mul' and b[0] == 'var':
            return ('ctA', b, a[1][3], a[1][2])
        if a[0] == 'var' and b[0] == 'var':
            return ('gsA', b, a)
    return ('op', op, a, b)


def is_slot(v):
    return v[0] == 'var'


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
            if (a[0] == 'op' and a[1] == 'add' and isN(a[2]) and is_slot(a[3]) and b[0] == 'montU'
                    and b[1][0] == 'op' and b[1][1] == 'mul'):
                r = ('ctB', a[2], a[3], b[1][3], b[1][2])
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
                    # gsB: montU (z * (C + xb - xa)); gsAs: montU (f * gsA xa xb)
                    if t[0] == 'op' and t[1] == 'mul':
                        z, d = t[2], t[3]
                        if (d[0] == 'op' and d[1] == 'sub' and d[2][0] == 'op' and d[2][1] == 'add'
                                and isN(d[2][2]) and is_slot(d[2][3]) and is_slot(d[3])):
                            r = ('gsB', d[2][2], d[3], d[2][3], z)
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


def slot_of(v):
    k = v[0]
    if k == 'ctA':
        return v[1][1]
    if k == 'ctB':
        return v[3][1]
    if k == 'gsA':
        return v[1][1]
    if k == 'gsB':
        return v[3][1]
    if k == 'gsAs':
        return v[2][1]
    raise ValueError(v)


def bfly_of(v):
    """(kind, slot a, slot b, zeta value) of an output word."""
    k = v[0]
    if k == 'ctA':
        return ('ct', v[1][1], v[2][1], v[3])
    if k == 'ctB':
        return ('ct', v[2][1], v[3][1], v[4])
    if k == 'gsA':
        return ('gsA', v[1][1], v[2][1], None)
    if k == 'gsB':
        return ('gs', v[2][1], v[3][1], v[4])
    if k == 'gsAs':
        return ('gsS', v[2][1], v[3][1], v[1])
    raise ValueError(v)


def stack_text(st):
    return ' :: '.join(pu(v) for v in st)


# ---------------------------------------------------------------- passes
C2N = lit(C2)
CIN = lit(CINV)
M32N = lit(M32)

HDR = """import MlDsaOpt44.Fn.Ntt.Step
/-! Generated by `MlDsaOpt44/Fn/Ntt/gen_ntt.py` (`ntt`/`intt`, MlDsaOpt/44/opt.asm): {title}. -/

namespace MlDsaOpt44.Proofs.NttW

open EvmSemantics EvmSemantics.EVM MlDsaOptCommon MlDsa44
open MlDsaOpt44.Proofs

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
"""

SIMP_DEFS = "montU, ctA, ctB, gsA, gsB, gsAs, wrU, montE"


def ctl_entries(pj, X, Cn, P, ret):
    return [pj, X, Cn, M32N, P, ret]


def block_lemma(name, start, end, pre, hyps_map, nat_params, uint_params, hyps, extra_simp, mem_ops):
    idx, c, post, stores = emulate(start, end, pre, hyps_map)
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
    (mem : ByteArray){params}{hs_} :
    Reach (callState s {pc0} ({stack_text(pre)} :: tail) mem)
      (callState s {pc1} ({stack_text(post)} :: tail) {mem_post}) {c} := by
"""
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
for m in range(1, 256):
    IMM_M.setdefault(zm(m), m)

PASSES = [
    dict(name='fA', title='forward pass A (layers 1-3)', head=7480, ends=[7598, 7686, 7774], ctl=7805,
         nw=8, off=1024, P=32768, X='e', Xn='33792', Cn=C2N, premont=False, tbl=None, kind='ct', L0=0,
         n='c', nbound='32', pj='32768 + 32 * c', slot='c + 32 * {i}',
         D='t % 32 < {n}', S='t % 32 = c', dec='⟨t / 32, by omega⟩', model='fwd', Bin='Bf 0', Bout='Bf 3',
         Pre='(fun k => fwdL (h k) 0)', Post='(fun k => fwdL (h k) 3)'),
    dict(name='fB', title='forward pass B (layers 4-6)', head=7816, ends=[7938, 8038, 8138], ctl=8169,
         nw=8, off=128, P=32768, X='zb', Xn='4096 + 224 * (n / 4)', Cn=C2N, premont=False, tbl='B', rb='(n / 4)',
         kind='ct', L0=3, n='n', nbound='32', pj='32768 + 1024 * (n / 4) + 32 * (n % 4)',
         slot='32 * (n / 4) + n % 4 + 4 * {i}', D='4 * (t / 32) + t % 4 < {n}', S='t / 32 = n / 4 ∧ t % 4 = n % 4',
         dec='⟨t % 32 / 4, by omega⟩', model='fwd', Bin='Bf 3', Bout='Bf 6',
         Pre='(fun k => fwdL (h k) 3)', Post='(fun k => fwdL (h k) 6)'),
    dict(name='fC', title='forward pass C (layers 7-8)', head=8191, ends=[8251, 8301], ctl=8316,
         nw=4, off=32, P=32768, X='zc', Xn='5888 + 96 * n', Cn=C2N, premont=False, tbl='C', rb='n',
         kind='ct', L0=6, n='n', nbound='64', pj='32768 + 128 * n', slot='4 * n + {i}',
         D='t / 4 < {n}', S='t / 4 = n', dec='⟨t % 4, by omega⟩', model='fwd', Bin='Bf 6', Bout='Bf 8',
         Pre='(fun k => fwdL (h k) 6)', Post='(fun k => fwdL (h k) 8)'),
    dict(name='iC', title='inverse pass C (layers 1-2, premont)', head=8338, ends=[8452, 8500], ctl=8515,
         nw=4, off=32, P=43264, X='zc', Xn='11936 - 96 * n', Cn=CIN, premont=True, tbl='C', rb='(63 - n)',
         kind='gs', L0=0, n='n', nbound='64', pj='43264 + 128 * n', slot='4 * n + {i}',
         D='t / 4 < {n}', S='t / 4 = n', dec='⟨t % 4, by omega⟩', model='inv', Bin='2 ^ 58', Bout='Bi 2',
         Pre='h', Post='(fun k => invL (scaleR h k) 2)'),
    dict(name='iB', title='inverse pass B (layers 3-5)', head=8532, ends=[8666, 8770, 8866], ctl=8897,
         nw=8, off=128, P=43264, X='zb', Xn='5664 - 224 * (n / 4)', Cn=CIN, premont=False, tbl='B',
         rb='(7 - n / 4)', kind='gs', L0=2, n='n', nbound='32', pj='43264 + 1024 * (n / 4) + 32 * (n % 4)',
         slot='32 * (n / 4) + n % 4 + 4 * {i}', D='4 * (t / 32) + t % 4 < {n}', S='t / 32 = n / 4 ∧ t % 4 = n % 4',
         dec='⟨t % 32 / 4, by omega⟩', model='inv', Bin='Bi 2', Bout='Bi 5',
         Pre='(fun k => invL (scaleR h k) 2)', Post='(fun k => invL (scaleR h k) 5)'),
    dict(name='iA', title='inverse pass A (layers 6-8, scaling)', head=8923, ends=[9045, 9137, 9285], ctl=9316,
         nw=8, off=1024, P=43264, X='e', Xn='44288', Cn=CIN, premont=False, tbl=None, kind='gs', L0=5,
         n='c', nbound='32', pj='43264 + 32 * c', slot='c + 32 * {i}',
         D='t % 32 < {n}', S='t % 32 = c', dec='⟨t / 32, by omega⟩', model='inv', Bin='Bi 5', Bout='Bu',
         Pre='(fun k => invL (scaleR h k) 5)', Post='(fun k t => Sc * invL (scaleR h k) 8 t)'),
]


def gen_blocks(ps):
    name, nw, off, P = ps['name'], ps['nw'], ps['off'], ps['P']
    pjv, Xv, retv = ('nv', 'pj'), ('nv', ps['X']), ('nv', 'ret')
    ctl = [pjv, Xv, ps['Cn'], M32N, lit(P), retv]
    out = ''
    head = ps['head']
    k, i = 0, head
    while k < nw:
        if L[i] == 'MLOAD':
            k += 1
        i += 1
    load_end = i + (12 if ps['premont'] else 0)
    addrs = ['pj'] + [f"({off * j} + pj)" for j in range(1, nw)]
    hmap = {a: f"w{j}" for j, a in enumerate(addrs)}
    hyps = [f"hpj : pj + {off * (nw - 1) + 32} ≤ 66080"] + [f"hw{j} : word mem {a} = w{j}" for j, a in enumerate(addrs)]
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

    def to_vars(post, slotf):
        return [('var', f"x{slotf(v)}") for v in post[:nw]] + post[nw:]

    cur = to_vars(post, slot_load)
    layers = []
    start = load_end
    zaddrs = None
    if ps['tbl']:
        zoff = [0, 32, 64, 96, 128, 160, 192] if ps['tbl'] == 'B' else [0, 32, 64]
        zaddrs = {(ps['X'] if o == 0 else f"({o} + {ps['X']})"): u for u, o in enumerate(zoff)}
    for li, e in enumerate(ps['ends']):
        zmap, zhyps, zparams, zsimp, zus = {}, [], [], [], []
        if zaddrs:
            used = set()

            class Rec(dict):
                def __contains__(self, key):
                    return key in zaddrs

                def __getitem__(self, key):
                    used.add(key)
                    return f"z{zaddrs[key]}"
            emulate(start, e + 1, cur, Rec())
            for a in sorted(used, key=lambda a: zaddrs[a]):
                u = zaddrs[a]
                zmap[a] = f"z{u}"
                zparams.append(f"z{u}")
                zus.append(u)
                zhyps.append(f"hz{u} : word mem {a} = z{u}")
                zsimp.append(f"hz{u}")
            zhyps = [f"hX : {ps['X']} + 224 ≤ 66080"] + zhyps
        txt, post, cl, _ = block_lemma(f"{name}_l{li + 1}", start, e + 1, cur, zmap,
                                       ['pj', ps['X'], 'ret'] + zparams, [f"x{j}" for j in range(nw)], zhyps,
                                       zsimp, bool(zaddrs))
        out += txt
        costs.append(cl)
        bfs = []
        for v in post[:nw]:
            bf = bfly_of(v)
            if bf[0] == 'gsA':
                continue
            if (bf[1], bf[2]) not in [(b[1], b[2]) for b in bfs]:
                bfs.append(bf)
        layers.append((bfs, zus))
        cur = to_vars(post, lambda v: int(slot_of(v)[1:]))
        start = e + 1
    txt, post, cst, stores = block_lemma(f"{name}_st", start, ps['ctl'], cur, {},
                                         ['pj', ps['X'], 'ret'], [f"x{j}" for j in range(nw)],
                                         [f"hpj : pj + {off * (nw - 1) + 32} ≤ 66080"], [], True)
    out += txt
    costs.append(cst)
    return out, layers, costs, stores


if False:
    for ps in PASSES:
        out, layers, costs, stores = gen_blocks(ps)
        print(ps['name'], 'costs', costs, sum(costs))
        for l in layers:
            print('  ', [(b[0], b[1], b[2], pu(b[3]) if b[3] else None) for b in l[0]], l[1])


C2T = str(C2)
CIT = str(CINV)
M32T = str(M32)


def head_stack(ps, pjexpr, Xexpr):
    C = C2T if ps['Cn'] == C2N else CIT
    return (f"UInt256.ofNat ({pjexpr}) :: UInt256.ofNat ({Xexpr}) :: UInt256.ofNat {C} :: "
            f"UInt256.ofNat {M32T} :: UInt256.ofNat {ps['P']} :: UInt256.ofNat ret :: tail")


def gen_body(ps, layers, costs, stores):
    name, nw, off, P = ps['name'], ps['nw'], ps['off'], ps['P']
    n = ps['n']
    slot = lambda i: ps['slot'].format(i=i)
    D0 = ps['D'].format(n=n)
    D1 = ps['D'].format(n=f"{n} + 1")
    hb = f"(h{n} : {n} < {ps['nbound']})"
    tbl = " (htbl : TblAt M)" if ps['tbl'] else ""
    inv = f"PassInv M {P} (fun t => {{D}}) ({ps['Bin']}) ({ps['Bout']}) {ps['Pre']} {ps['Post']}"
    hs = head_stack(ps, ps['pj'], ps['Xn'])
    cost = sum(costs)
    out = f"""
theorem {name}_body {{s : State}} (hs : Ctx s) {{tail : List UInt256}} (htail : tail.length ≤ 960)
    (ret : Nat) (H : Prop) (h : Nat → Nat → F) ({n} : Nat) {hb} (M : ByteArray){tbl}
    (hP : H → {inv.format(D=D0)}) :
    ∃ M', (H → {inv.format(D=D1).replace('PassInv M ', "PassInv M' ")}) ∧
      FrameExcept M M' [({P}, {P} + 8192)] ∧
      Reach (callState s {PC[ps['head']]} ({hs}) M)
        (callState s {PC[ps['ctl']]} ({hs}) M') {cost} := by
"""
    pj, X = ps['pj'], ps['Xn']
    # load
    ws = ' '.join(f"(word M ({P} + 32 * ({slot(i)})))" for i in range(nw))
    hws = ' '.join("(congrArg (word M) (by omega))" for i in range(nw))
    chain = f"({name}_ld hs htail M ({pj}) ({X}) ret {ws} (by omega) {hws})"
    parts = [chain]
    for li, (bfs, zus) in enumerate(layers):
        zv = ' '.join(f"({rec_val(ps['tbl'], ps['rb'], u)})" for u in zus)
        hz = ' '.join(f"(by rw [← htbl ({rec_index(ps['tbl'], ps['rb'], u)}) (by omega)]; congr 1; unfold TBL; omega)"
                      for u in zus)
        xs = ' '.join('_' for _ in range(nw))
        extra = f" (by omega) {hz}" if ps['tbl'] else ""
        parts.append(f"({name}_l{li + 1} hs htail M ({pj}) ({X}) ret {zv} {xs}{extra})")
    xs = ' '.join('_' for _ in range(nw))
    parts.append(f"({name}_st hs htail M ({pj}) ({X}) ret {xs} (by omega))")
    r = parts[-1]
    for p in reversed(parts[:-1]):
        r = f"({p}.trans\n    {r})"
    out += f"  have hR := {r}\n"
    out += "  refine ⟨_, fun hH => ?sem, ?frm, hR.mono (by norm_num)⟩\n"
    out += "  case frm =>\n    repeat (first | exact FrameExcept.refl _ _ | refine frame_wrU _ ?_ (by omega) (by omega))\n"
    out += "  case sem =>\n    have hI := hP hH\n"
    # loaded facts
    for i in range(nw):
        f = f"passInv_pre hI (t := {slot(i)}) (by omega) (by omega)"
        if ps['premont']:
            f = f"premont_step h ({slot(i)}) _ ({f})"
        out += f"    have v0_{i} := {f}\n"
    hmodel = 'h' if ps['model'] == 'fwd' else '(scaleR h)'
    for li, (bfs, zus) in enumerate(layers):
        L = ps['L0'] + li
        last_scaled = (ps['name'] == 'iA' and li == 2)
        for (kind, a, b, z) in bfs:
            a, b = int(a[1:]), int(b[1:])
            ia, ib = slot(a), slot(b)
            if last_scaled:
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gsS_step {hmodel} ({ia}) ({ib}) (by omega) "
                        f"(by omega) v{li}_{a} v{li}_{b}\n")
                continue
            # zeta
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
                ln = 128 >> L
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := ct_step h {L} {ln} ({ia}) ({ib}) ({mexpr}) "
                        f"({zexpr}) (by norm_num) (by norm_num) (by omega) (by omega) (by omega) {hz} "
                        f"v{li}_{a} v{li}_{b}\n")
            else:
                ln = 1 << L
                m0 = 1 << (8 - L)
                out += (f"    obtain ⟨v{li + 1}_{a}, v{li + 1}_{b}⟩ := gs_step {hmodel} {L} {ln} {m0} ({ia}) ({ib}) "
                        f"({mexpr}) ({zexpr}) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) "
                        f"(by omega) {hz} v{li}_{a} v{li}_{b}\n")
    nl = len(layers)
    S = ps['S']
    out += f"""    refine passInv_store hI (S := fun t => {S}) (fun t => by omega) ?new ?old
    case old =>
      intro t ht hS
      simp (disch := omega) only [word_wrU, if_neg]
    case new =>
      intro t ht hS
      obtain ⟨i, rfl⟩ : ∃ i, t = {slot('i')} := {ps['dec']}
      have hi : i < {nw} := by omega
      interval_cases i
"""
    for i in range(nw):
        out += f"      · simp (disch := omega) only [word_wrU, if_pos, if_neg, ofNat_toNat]; exact v{nl}_{i}\n"
    return out


def gen_file(ps):
    blocks, layers, costs, stores = gen_blocks(ps)
    out = HDR.format(title=ps['title'])
    out += blocks
    out += gen_body(ps, layers, costs, stores)
    return out, sum(costs)


if __name__ == '__main__':
    which = sys.argv[1:]
    for ps in PASSES:
        if which and ps['name'] not in which:
            continue
        txt, c = gen_file(ps)
        fn = {'fA': 'FwdA', 'fB': 'FwdB', 'fC': 'FwdC', 'iC': 'InvC', 'iB': 'InvB', 'iA': 'InvA'}[ps['name']]
        open(OUT + fn + '.lean', 'w').write(txt)
        print(fn, c)
