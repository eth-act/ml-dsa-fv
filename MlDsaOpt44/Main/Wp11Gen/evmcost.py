rows=[l.rstrip('\n').split('\t') for l in open('MlDsaOpt44/listing.tsv')][1:]
def c(i):
    op=rows[i][2].split()[0]
    if op=='PUSH0': return 2
    if op.startswith('PUSH') or op.startswith('DUP') or op.startswith('SWAP'): return 3
    t={'JUMPDEST':1,'MUL':5,'JUMP':8,'JUMPI':10,'POP':2,'CALLDATASIZE':2,'ADDRESS':2}
    if op in t: return t[op]
    if op=='RETURN': return 0
    if op in ('AND','OR','XOR','NOT','LT','GT','EQ','ISZERO','SHL','SHR','ADD','SUB','MLOAD','MSTORE','CALLDATALOAD','BYTE'): return 3
    raise Exception(op)
def cost(a,b): return sum(c(i) for i in range(a,b))
pc=lambda i:int(rows[i][1])
idx={int(r[1]):int(r[0]) for r in rows}
