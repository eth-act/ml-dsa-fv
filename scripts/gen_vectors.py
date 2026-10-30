#!/usr/bin/env python3
"""Generate ML-DSA-44 test vectors.

vectors/acvp_internal.txt: `pk sig M' expected` from the NIST ACVP sigVer
  file (ML-DSA-44 groups: external/pure with M' = 0 ‖ |ctx| ‖ ctx ‖ M, and
  internal without external mu). Checks `Fips204.verifyInternal`.
vectors/calldata.txt: `calldata expected note` for the full EIP-8355
  interface. Valid signatures come from dilithium-py (empty context);
  malformed variants carry the FIPS 204 verdict, not dilithium-py's (it
  accepts repeated hint indices, which Algorithm 21 rejects).

Usage: PYTHONPATH=.ref/pylib python3 scripts/gen_vectors.py .ref/acvp_sigver.json
"""
import json
import os
import random
import sys

from dilithium_py.ml_dsa import ML_DSA_44

PK_LEN, SIG_LEN, OMEGA, K = 1312, 2420, 80, 4
HINT_OFF = 32 + 4 * 576


def acvp(path):
    rows = []
    data = json.load(open(path))
    for group in data["testGroups"]:
        if group["parameterSet"] != "ML-DSA-44" or group.get("externalMu"):
            continue
        if group["signatureInterface"] == "external" and group["preHash"] != "pure":
            continue
        for t in group["tests"]:
            if group["signatureInterface"] == "external":
                ctx = bytes.fromhex(t["context"])
                mprime = bytes([0, len(ctx)]) + ctx + bytes.fromhex(t["message"])
            else:
                mprime = bytes.fromhex(t["message"])
            rows.append((t["pk"].lower(), t["signature"].lower(), mprime.hex(),
                         int(t["testPassed"])))
    return rows


def calldata_rows():
    rng = random.Random(8212)
    rows = []

    def add(pk, sig, msg, expected, note):
        rows.append(((pk + sig + msg).hex(), expected, note))

    for n, mlen in enumerate([0, 1, 31, 32, 69, 70, 71, 135, 136, 137, 205, 206, 207, 1000]):
        pk, sk = ML_DSA_44.key_derive(bytes([n]) * 32)
        msg = bytes(rng.randrange(256) for _ in range(mlen))
        sig = ML_DSA_44.sign(sk, msg, deterministic=True)
        assert ML_DSA_44.verify(pk, msg, sig)
        add(pk, sig, msg, 1, f"valid mlen={mlen}")
        if n % 3 == 0:
            bad = bytearray(sig); bad[0] ^= 1
            add(pk, bytes(bad), msg, 0, "flipped c~")
            bad = bytearray(sig); bad[100] ^= 4
            add(pk, bytes(bad), msg, 0, "flipped z")
            add(pk, sig, msg + b"\x00", 0, "extended message")
            bad = bytearray(pk); bad[40] ^= 1
            add(bytes(bad), sig, msg, 0, "flipped t1")
            bad = bytearray(pk); bad[0] ^= 1
            add(bytes(bad), sig, msg, 0, "flipped rho")

    pk, sk = ML_DSA_44.key_derive(bytes([99]) * 32)
    msg = b"malformed"
    sig = ML_DSA_44.sign(sk, msg, deterministic=True)
    hint = sig[HINT_OFF:]
    counts = list(hint[OMEGA:])

    # z coefficient 0 encodes γ1 − 0 = γ1: fails the norm bound.
    bad = bytearray(sig); bad[32:32 + 3] = b"\x00\x00\x00"
    add(pk, bytes(bad), msg, 0, "z = gamma1")
    # z coefficient encoding γ1 − β exactly (raw = β = 78): fails (strict <).
    bad = bytearray(sig)
    raw = 78
    v = int.from_bytes(bad[32:35], "little") & ~0x3FFFF | raw
    bad[32:35] = v.to_bytes(3, "little")
    add(pk, bytes(bad), msg, 0, "z = gamma1 - beta")
    # Hint count above ω.
    bad = bytearray(sig); bad[HINT_OFF + OMEGA + K - 1] = OMEGA + 1
    add(pk, bytes(bad), msg, 0, "hint count > omega")
    # Decreasing hint counts.
    if counts[0] > 0:
        bad = bytearray(sig); bad[HINT_OFF + OMEGA + 1] = counts[0] - 1
        add(pk, bytes(bad), msg, 0, "hint counts decrease")
    # Repeated hint index within a row (FIPS rejects, dilithium-py accepts).
    if counts[0] >= 2:
        bad = bytearray(sig); bad[HINT_OFF + 1] = bad[HINT_OFF]
        add(pk, bytes(bad), msg, 0, "repeated hint index")
    # Non-zero padding after the last used index.
    if counts[-1] < OMEGA:
        bad = bytearray(sig); bad[HINT_OFF + OMEGA - 1] = 1
        add(pk, bytes(bad), msg, 0, "nonzero hint padding")

    # Short inputs.
    add(pk, sig[:-1], b"", 0, "one byte short")
    rows.append(("", 0, "empty calldata"))
    return rows


def main():
    os.makedirs("vectors", exist_ok=True)
    with open("vectors/acvp_internal.txt", "w") as f:
        for row in acvp(sys.argv[1]):
            f.write(" ".join(map(str, row)) + "\n")
    with open("vectors/calldata.txt", "w") as f:
        for data, expected, note in calldata_rows():
            f.write(f"{data or '-'} {expected} {note}\n")


if __name__ == "__main__":
    main()
