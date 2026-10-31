// EIP-8355 verdict oracle backed by the Go standard library's FIPS 140-3
// module (crypto/internal/fips140/mldsa).
//
// The package is internal to the standard library, so build.sh compiles this
// file as the standard-library command `crypto/mldsa44oracle` through a
// `go build -overlay`; nothing in GOROOT is modified.
//
// Reads lines whose first whitespace-separated field is hex calldata (`-` for
// empty) and prints one `0`/`1` per line: `1` iff the calldata is
// `pk (1312) ‖ σ (2420) ‖ M` and ML-DSA-44.Verify(pk, M, σ, ctx = "") accepts.
package main

import (
	"bufio"
	"crypto/internal/fips140/mldsa"
	"encoding/hex"
	"os"
	"strings"
)

const pkLen, sigLen = 1312, 2420

func verdict(cd []byte) bool {
	if len(cd) < pkLen+sigLen {
		return false
	}
	pub, err := mldsa.NewPublicKey44(cd[:pkLen])
	if err != nil {
		return false
	}
	return mldsa.Verify(pub, cd[pkLen+sigLen:], cd[pkLen:pkLen+sigLen], "") == nil
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<26)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		fields := strings.Fields(in.Text())
		if len(fields) == 0 {
			continue
		}
		var cd []byte
		if fields[0] != "-" {
			var err error
			if cd, err = hex.DecodeString(fields[0]); err != nil {
				panic(err)
			}
		}
		if verdict(cd) {
			out.WriteString("1\n")
		} else {
			out.WriteString("0\n")
		}
	}
	if err := in.Err(); err != nil {
		panic(err)
	}
}
