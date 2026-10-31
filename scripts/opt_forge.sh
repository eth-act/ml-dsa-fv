#!/usr/bin/env bash
# Replays the vectors (and, for ML-DSA-44, the fuzz corpus) against an alternate
# verifier bytecode in revm via foundry/test/OptVerdicts.t.sol, checking only
# the verdict, then summarises the per-case TSVs in foundry/cache/opt/.
#
#   scripts/opt_forge.sh HEX SET [MATCH_TEST]
#
#   HEX         hex artifact (path relative to the current directory or absolute),
#               e.g. MlDsaOpt/44/opt.hex; must lie under a directory foundry.toml
#               grants read access to (MlDsaOpt/, MlDsa{44,65,87}/Reference/)
#   SET         44, 65 or 87
#   MATCH_TEST  optional forge --match-test regex (e.g. 'vectors|valid')
#
# Exit status: forge's, or 1 if it ran no case or any case mismatched.

if [ $# -lt 2 ] || [ $# -gt 3 ]; then
    sed -n '6,14p' "$0" >&2
    exit 2
fi
case "$2" in 44|65|87) ;; *) echo "SET must be 44, 65 or 87" >&2; exit 2 ;; esac

root=$(cd "$(dirname "$0")/.." && pwd)
hex=$(realpath "$1") || exit 2
[ -f "$hex" ] || { echo "no such file: $1" >&2; exit 2; }
set_=$2
match=${3:-}

cd "$root/foundry" || exit 2
export TMPDIR=$root/.lake/tmp
mkdir -p "$TMPDIR" cache/opt
rm -f cache/opt/"$set_"_*.tsv cache/opt/failures_"$set_"_*.txt

args=(test --match-contract '^OptVerdictsTest$' -vv)
# The fuzz corpus is ML-DSA-44 only; for 65/87 the corpus tests are no-ops.
if [ -n "$match" ]; then args+=(--match-test "$match")
elif [ "$set_" != 44 ]; then args+=(--match-test '^test_vectors')
fi

start=$(date +%s)
OPT_HEX=$(realpath --relative-to=. "$hex") OPT_SET=$set_ forge "${args[@]}"
status=$?
echo "forge exit status $status, $(( $(date +%s) - start )) s"

python3 - "$set_" <<'EOF'
import glob, os, sys

s = sys.argv[1]
min_len = {"44": 1312 + 2420, "65": 1952 + 3309, "87": 2592 + 4627}[s]
rows = []
# vectors first, so "first" below is the KAT empty-message row when present
tsvs = sorted(glob.glob(f"cache/opt/{s}_*.tsv"), key=lambda p: (not p.endswith("_vectors.tsv"), p))
for path in tsvs:
    with open(path) as f:
        rows += [l.rstrip("\n").split("\t") for l in f if l.strip()]
if not rows:
    print(f"set {s}: no results in cache/opt/{s}_*.tsv")
    sys.exit(1)

def summary(name, rs):
    gas = sorted(int(r[6]) for r in rs)
    n = len(gas)
    med = gas[n // 2] if n % 2 else (gas[n // 2 - 1] + gas[n // 2]) // 2
    bad = sum(r[4] != r[5] for r in rs)
    acc = sum(r[4] == "1" for r in rs)
    print(f"  {name:<34} cases={n:<5} accepted={acc:<4} mismatches={bad:<3} "
          f"gas min={gas[0]:,} median={med:,} max={gas[-1]:,}")
    return bad

files = {}
for r in rows:
    files.setdefault(r[1], []).append(r)
print(f"set {s}: per file")
for name, rs in files.items():
    summary(name, rs)
print(f"set {s}: total")
bad = summary("all", rows)

empty = [r for r in rows if r[4] == "1" and int(r[3]) == min_len]
if empty:
    gas = sorted(int(r[6]) for r in empty)
    first = empty[0]
    print(f"  valid empty-message cases (calldata {min_len} bytes): {len(empty)}, "
          f"gas min={gas[0]:,} max={gas[-1]:,}; first {first[1]}:{first[2]} gas={int(first[6]):,}")
else:
    print(f"  no valid empty-message case (calldata {min_len} bytes)")
fails = sorted(glob.glob(f"cache/opt/failures_{s}_*.txt"))
if fails:
    print("  failures: " + " ".join(os.path.join("foundry", f) for f in fails))
sys.exit(1 if bad else 0)
EOF
summary=$?
[ $status -eq 0 ] && status=$summary
exit $status
