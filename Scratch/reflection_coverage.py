"""Opcode-only upper bound; does not claim successful target bridges."""
from pathlib import Path
from collections import Counter
import re

root = Path(__file__).resolve().parent.parent
supported = {0x01, 0x16, 0x17, 0x18, 0x1B, 0x1C, 0x51, 0x52, 0x5B} | set(range(0x5F, 0x90))
total = eligible = 0
missing = Counter()
for level in (44, 65, 87):
    code = bytes.fromhex((root / f"MlDsaOpt/{level}/opt.hex").read_text().strip().removeprefix("0x"))
    ops = []
    pc = 0
    while pc < len(code):
        o = code[pc]
        ops.append(o)
        pc += 1 + (o - 0x5F if 0x60 <= o <= 0x7F else 0)
    n = ok = 0
    for path in (root / f"MlDsaOpt{level}").rglob("*.lean"):
        for match in re.finditer(rf"\bopt{level}_reach\s*\[([\d,\s]+)\]", path.read_text()):
            indices = [int(i) for i in match[1].split(",") if i.strip()]
            bad = {ops[i] for i in indices} - supported
            n += 1
            ok += not bad
            missing.update(bad)
    print(f"Opt{level}: {ok}/{n} ({ok/n:.1%}) literal reach paths use only supported opcodes")
    total += n
    eligible += ok
print(f"TOTAL {eligible}/{total} ({eligible/total:.1%})")
print("Unsupported opcode / calls containing it:", [(hex(k), v) for k, v in missing.most_common()])
