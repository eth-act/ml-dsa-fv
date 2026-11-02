"""blk prologue for the 8-way layout: one cross-word delta swap turns the two
half-words of a lane (8 states, bit 8b + s of word h = bit 2b + h of slot s)
into two ordinary 4-way kf4 words (slots 0-3 and 4-7, bit 4q + k = bit q of
slot k), after which v4's unzip and candidate extraction apply unchanged.

    t  = ((W0 >> 4) ^ W1) & 0x0f0f..0f
    X1 = W1 ^ t         (slots 4-7)
    X0 = W0 ^ (t << 4)  (slots 0-3)

Checked here on random lanes and measured: gas of the swap for one lane
pair, excluding the loads both layouts need."""
from __future__ import annotations

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import opt_evm  # noqa: E402
import opt_ref  # noqa: E402
from opt_asm import Asm  # noqa: E402

import lab  # noqa: E402

LO = int("0f" * 32, 16)


def code():
    a = Asm()
    # stack in: [W0, W1]; out: [X1, X0] then X0 finished: [X0, X1] (X1 on top first)
    a.op("DUP2"); a.push(4); a.op("SHR"); a.op("DUP2"); a.op("XOR"); a.push(LO); a.op("AND")  # [W0 W1 t]
    a.op("DUP1"); a.op("SWAP2"); a.op("XOR")            # [W0 t X1]
    a.op("SWAP2"); a.op("SWAP1"); a.push(4); a.op("SHL"); a.op("XOR")   # [X1 X0] (blk would consume X1 first: no swaps)
    a.op("STOP")
    return a.assemble()


if __name__ == "__main__":
    c = code()
    rng = random.Random(3)
    for _ in range(20):
        lanes = [rng.getrandbits(64) for _ in range(8)]
        hs = [lab.halves(v) for v in lanes]
        W0 = lab.interleave8([h[0] for h in hs])
        W1 = lab.interleave8([h[1] for h in hs])
        r = opt_evm.run(c, stack=[W0, W1])
        X1, X0 = r["stack"]
        assert opt_ref.deinterleave(X0) == lanes[:4] and opt_ref.deinterleave(X1) == lanes[4:]
    # the two SWAPs only exist in this standalone harness (blk consumes X1 first)
    print(f"cross swap ok: {r['gas_used'] - 6} gas per lane pair (+6 for the second MLOAD)")
