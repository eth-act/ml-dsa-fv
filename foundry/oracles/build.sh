#!/usr/bin/env bash
# Builds the two native verdict oracles into foundry/oracles/bin.
#   mldsa44-oracle-rust  RustCrypto ml-dsa 0.1.1
#   mldsa44-oracle-go    Go standard library crypto/internal/fips140/mldsa
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$here/bin"

(cd "$here/rust" && cargo build --release --quiet)
cp "$here/rust/target/release/mldsa44-oracle-rust" "$here/bin/"

goroot="$(go env GOROOT)"
overlay="$here/bin/go-overlay.json"
printf '{"Replace":{"%s/src/crypto/mldsa44oracle/main.go":"%s/go/main.go"}}\n' "$goroot" "$here" > "$overlay"
(cd "$goroot/src" && go build -overlay "$overlay" -o "$here/bin/mldsa44-oracle-go" crypto/mldsa44oracle)
go version > "$here/bin/go-version.txt"
