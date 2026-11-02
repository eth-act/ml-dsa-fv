"""Whole-verifier model for the 8-way memory-rotation kernel (kf8m).

Starts from the measured per-subroutine profile of the v4 and glam
verifiers (profile_verifiers.py, valid empty-message vector) and replaces
the Keccak-related subroutines:

* kf4 calls -> kf8m calls (measured, kf8m.py) at the 8-slot schedule below;
  "mixed" keeps one 4-slot kf4 group and needs both kernels;
* blk per kf8m call = 2 x blk per kf4 call (after the cross-word swap each
  half is an ordinary kf4 word, xswap.py) + 21 x 45 gas (swap + second load);
* trabs: +1,275 per call (8 instead of 4 extractions per calldata word, each
  stored twice; the 7-stage zip network is unchanged: it already produces
  bit 8b + 4h + i);
* cext: x2 (gather two half-words and re-interleave even/odd bits);
* ginit: x2.5 per group (50 words, stored twice);
* memory: +7.2 KB (KS/KB 3,200 B each, D 640 B, iota table 1,536 B, BK
  3,200 B) at the top: +2.6k;
* 87, pure schedule: tr in groups 0-3, so H(c~) and mu (|M| <= 69) ride in
  spare slots of groups 4-7 (-2 kf1 calls, as 44 and 65 do today).

Estimates (not measured): the blk/trabs/cext/ginit factors and memory.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

KF8 = {"v4": [("kf8m", 68_522, 2_982), ("kf8i", 71_558, 1_532)],
       "glam": [("kf8m6", 68_338, 8_919)]}
KF4 = {"v4": 40_238, "glam": 35_340}
KF1 = {"v4": 32_571, "glam": 27_705}
# (kf8 calls, kf4 calls, kf1 calls saved) per set and schedule
SCHED = {
    "pure": {44: (15, 0, 0), 65: (25, 0, 0), 87: (40, 0, 2)},
    "mixed": {44: (10, 5, 0), 65: (20, 5, 0), 87: (35, 5, 0)},
}
GROUPS4 = {44: 5, 65: 9, 87: 15}
XSWAP = 21 * 45
TRABS_EXTRA = 1_275
MEM_EXTRA = 2_600
CODE_EXTRA_GLUE = 240     # cross swap, trabs, cext, ginit changes (bytes, estimate)
LIMIT = {"v4": 24_576, "glam": 65_536}


def main():
    path = "/tmp/keccak_lab_prof.json"
    if not os.path.exists(path):
        out = subprocess.run([sys.executable, os.path.join(HERE, "profile_verifiers.py")],
                             check=True, capture_output=True, text=True).stdout
        open(path, "w").write(out)
    prof = json.load(open(path))
    rows = []
    for base in ("v4", "glam"):
      for kname, k8, k8size in KF8[base]:
        for sched in ("pure", "mixed"):
            for nn in (44, 65, 87):
                p = prof[f"{base}/{nn}"]
                R = p["regions"]
                n8, n4, kf1_saved = SCHED[sched][nn]
                blk4 = R["blk"]["gas"] / GROUPS4[nn] / 5
                g8 = n8 // 5
                d = {}
                d["keccak"] = n8 * k8 + n4 * KF4[base] - R["kf4"]["gas"] - kf1_saved * KF1[base]
                d["blk"] = n8 * (2 * blk4 + XSWAP) + n4 * blk4 - R["blk"]["gas"]
                d["trabs"] = R["trabs"]["calls"] * TRABS_EXTRA
                d["cext"] = R["cext"]["gas"]
                ginit4 = R["ginit"]["gas"] / GROUPS4[nn]
                d["ginit"] = g8 * 2.5 * ginit4 + (n4 // 5) * ginit4 - R["ginit"]["gas"]
                d["mem"] = MEM_EXTRA
                total = p["total"] + sum(d.values())
                kf4size = R["kf4"]["bytes"]
                size = p["size"] + k8size + CODE_EXTRA_GLUE - (kf4size if n4 == 0 else 0)
                rows.append((f"{base}, {kname}", sched, nn, p["total"], round(total), d, size, p["size"]))
    print("| base, kernel | schedule | set | today | modeled | delta | keccak | blk | trabs | cext | ginit | mem | code (B) |")
    print("|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for base, sched, nn, t0, t1, d, size, size0 in rows:
        fits = "" if size <= LIMIT[base.split(",")[0]] else " **over limit**"
        print(f"| {base} | {sched} | {nn} | {t0:,} | {t1:,} | {t1 - t0:+,} ({100 * (t1 - t0) / t0:+.1f}%) | "
              + " | ".join(f"{d[k]:+,.0f}" for k in ("keccak", "blk", "trabs", "cext", "ginit", "mem"))
              + f" | {size:,} (was {size0:,}){fits} |")


if __name__ == "__main__":
    main()
