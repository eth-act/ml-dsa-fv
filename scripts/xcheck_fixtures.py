#!/usr/bin/env python3
"""Builds foundry/fixtures/vectors.txt: every row of vectors/calldata.txt plus
every ACVP sigVer row of vectors/acvp_internal.txt usable as EIP-8355
calldata (M' = 0x00 0x00 ‖ M, i.e. external interface with empty context),
each with its expected verdict, Lean-semantics frame gas and Lean
`Gas.schedule`. Also re-checks the closed-form schedule against Lean on a
dense range of sizes.

Usage (repository root):
    python3 scripts/xcheck_fixtures.py
"""
import sys
import time

import xcheck_common as xc


def main():
    t0 = time.time()
    cases = []
    for line in (xc.ROOT / "vectors" / "calldata.txt").read_text().splitlines():
        cd, expected, *note = line.split(" ")
        cd = b"" if cd == "-" else bytes.fromhex(cd)
        cases.append((cd, "kat", " ".join(note), int(expected)))
    acvp = 0
    for n, line in enumerate((xc.ROOT / "vectors" / "acvp_internal.txt").read_text().splitlines()):
        pk, sig, mprime, expected = line.split(" ")
        mprime = bytes.fromhex(mprime)
        if mprime[:2] != b"\x00\x00":
            continue
        acvp += 1
        cases.append((bytes.fromhex(pk) + bytes.fromhex(sig) + mprime[2:], "acvp",
                      f"acvp row {n + 1}", int(expected)))
    print(f"{len(cases) - acvp} calldata.txt rows, {acvp} usable ACVP rows")

    records, problems, known = xc.check_cases(cases)
    xc.write_fixture(xc.ROOT / "foundry" / "fixtures" / "vectors.txt", records)
    # Negative control for the replay harness: Lean gas off by one; verdict flipped.
    valid = [r for r in records if r["expected"] == 1][:2]
    xc.write_fixture(xc.ROOT / "foundry" / "fixtures" / "control.txt", [
        dict(valid[0], gas=valid[0]["gas"] + 1, note="control: lean gas + 1"),
        dict(valid[1], expected=0, note="control: verdict flipped"),
    ])

    # Closed form vs Lean on every size from 0 to 3732 + 4500 and a sparse tail.
    sizes = list(range(0, xc.HEADER + 4500)) + list(range(xc.HEADER + 4500, xc.HEADER + 200_000, 997))
    lean = xc.lean_schedule(sizes)
    bad = [n for n in sizes if lean[n] != xc.schedule(n)]
    print(f"closed-form schedule vs Lean Gas.schedule: {len(sizes) - len(bad)}/{len(sizes)} sizes agree")
    with (xc.ROOT / "foundry" / "fixtures" / "schedule.txt").open("w") as f:
        for n in sizes[::37] + [xc.HEADER - 1, xc.HEADER, xc.HEADER + 70, xc.HEADER + 71]:
            f.write(f"{n} {lean[n]}\n")

    print(f"known dilithium-py divergences: {known}")
    for rec, issues in problems:
        print(f"PROBLEM {rec['cat']} {rec['note']}: {issues}")
    print(f"max Lean gas {max(r['gas'] for r in records)}; {time.time() - t0:.0f}s")
    sys.exit(1 if problems or bad else 0)


if __name__ == "__main__":
    main()
