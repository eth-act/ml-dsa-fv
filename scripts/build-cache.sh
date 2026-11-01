#!/usr/bin/env bash
# Build cache: the `.lake` build outputs of a master commit (the project's
# libraries and tools, and every dependency except Mathlib's .oleans, which
# `lake exe cache get` provides), published as assets of the GitHub release
# `build-cache` by .github/workflows/build-cache.yml.
#
#   scripts/build-cache.sh restore [--ancestor]   restore HEAD's cache; with
#       --ancestor, fall back to the nearest first-parent ancestor that has one
#   scripts/build-cache.sh pack DIR               write HEAD's cache to DIR
#   scripts/build-cache.sh publish DIR [KEEP]     upload DIR (needs gh auth) and
#       prune the release to the KEEP newest caches (default 10)
#
# A cache is only used when lean-toolchain and lake-manifest.json are
# identical to the commit it was built from; everything in it was built in one
# tree, so its .oleans are consistent with each other (Lean .oleans are not
# byte-reproducible, so never mix outputs from two builds of a module).
# Restoring from a different directory path is fine: Lake traces are
# content hashes.
set -euo pipefail
cd "$(dirname "$0")/.."

REPO=${BUILD_CACHE_REPO:-${GITHUB_REPOSITORY:-eth-act/ml-dsa-fv}}
TAG=build-cache
URL=${BUILD_CACHE_URL:-https://github.com/$REPO/releases/download/$TAG}
PART_SIZE=1900m   # release assets are limited to 2 GiB
MARKER=.lake/build-cache-restored

# Everything a build writes, minus Mathlib's .oleans and scratch space.
paths() {
  local d
  for d in .lake/build .lake/packages/*/.lake/build \
           .lake/packages/mathlib/.lake/build/{ir,bin}; do
    [ "$d" = .lake/packages/mathlib/.lake/build ] || [ ! -e "$d" ] || printf '%s\n' "$d"
  done
}

# Inputs that must match exactly for the dependencies' outputs to be valid.
fingerprint() { cat lean-toolchain lake-manifest.json | sha256sum | cut -c1-16; }

fetch() { curl -fsSL --retry 3 --connect-timeout 20 "$@"; }

restore_sha() {
  local sha=$1 index part
  index=$(fetch "$URL/$sha.index" 2>/dev/null) || return 1
  if [ "$(sed -n 's/^fingerprint //p' <<<"$index")" != "$(fingerprint)" ]; then
    echo "build cache $sha: toolchain or manifest differs, not used"
    return 1
  fi
  echo "restoring build cache of $sha"
  mkdir -p .lake
  # Download all parts and check them before unpacking anything.
  local tmp parts ok=1
  tmp=$(mktemp -d "$PWD/.lake/cache-dl.XXXXXX")
  parts=$(sed -n 's/^part //p' <<<"$index" | awk '{print $2}')
  (cd "$tmp" && for part in $parts; do fetch -o "$part" "$URL/$part" & done; wait) &&
    sed -n 's/^part //p' <<<"$index" | (cd "$tmp" && sha256sum --quiet -c -) &&
    (cd "$tmp" && cat $parts) | zstd -dc | tar -x || ok=0
  rm -rf "$tmp"
  [ $ok = 1 ] || { echo "build cache $sha: download or unpack failed"; return 1; }
  echo "$sha" > "$MARKER"
}

cmd_restore() {
  local head; head=$(git rev-parse HEAD)
  if [ "$(cat "$MARKER" 2>/dev/null)" = "$head" ]; then
    echo "build cache of $head already restored"; return 0
  fi
  restore_sha "$head" && return 0
  echo "no build cache for $head"
  [ "${1:-}" = --ancestor ] || return 1
  # Only into a tree without project builds: an older cache would overwrite
  # newer local outputs.
  if [ -e "$MARKER" ] || [ -d .lake/build/lib/lean/MlDsa44 ]; then return 1; fi
  local sha
  for sha in $(git rev-list --first-parent -n 30 HEAD~ 2>/dev/null); do
    if fetch -o /dev/null "$URL/$sha.index" 2>/dev/null; then
      restore_sha "$sha" && { echo "(an ancestor of HEAD: modules changed since then will rebuild)"; return 0; }
    fi
  done
  echo "no build cache for any recent ancestor"; return 1
}

cmd_pack() {
  local out=$1 head; head=$(git rev-parse HEAD)
  mkdir -p "$out"
  if ! git diff --quiet HEAD; then echo "pack: worktree has changes" >&2; exit 1; fi
  tar -c $(paths) | zstd -T0 -3 -q | split -b "$PART_SIZE" -d -a 2 - "$out/$head.tar.zst."
  {
    echo "commit $head"
    echo "fingerprint $(fingerprint)"
    (cd "$out" && sha256sum "$head".tar.zst.* | sed 's/^/part /')
  } > "$out/$head.index"
  du -ch "$out/$head".tar.zst.* | tail -1
}

cmd_publish() {
  local dir=$1 keep=${2:-10} head; head=$(git rev-parse HEAD)
  gh release view "$TAG" -R "$REPO" >/dev/null 2>&1 ||
    gh release create "$TAG" -R "$REPO" --prerelease --title "Build cache" \
      --notes "Lake build outputs per master commit, used by .agents/setup (scripts/build-cache.sh). Not a release." \
      --target "$head"
  # Parts first, index last: a cache is visible only once complete.
  gh release upload "$TAG" -R "$REPO" --clobber "$dir/$head".tar.zst.*
  gh release upload "$TAG" -R "$REPO" --clobber "$dir/$head.index"
  # Prune: keep the KEEP most recently uploaded caches.
  local id assets
  id=$(gh api "repos/$REPO/releases/tags/$TAG" --jq .id)
  assets=$(gh api --paginate "repos/$REPO/releases/$id/assets" --jq '.[] | "\(.created_at) \(.id) \(.name)"')
  sed -n 's/^\([^ ]*\) [0-9]* \([0-9a-f]\{40\}\)\.index$/\1 \2/p' <<<"$assets" | sort -r |
    tail -n +"$((keep + 1))" | while read -r _ sha; do
      awk -v p="$sha." 'index($3, p) == 1 {print $2}' <<<"$assets" |
        while read -r asset; do gh api -X DELETE "repos/$REPO/releases/assets/$asset"; done
    done
}

case "${1:-}" in
  restore) shift; cmd_restore "$@" ;;
  pack) cmd_pack "${2:?pack DIR}" ;;
  publish) cmd_publish "${2:?publish DIR [KEEP]}" "${3:-}" ;;
  *) sed -n '2,19p' "$0"; exit 2 ;;
esac
