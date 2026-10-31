#!/usr/bin/env python3
"""Generate ML-DSA-44/65/87 test vectors for the parametric spec.

For parameter set NN, writes into OUTDIR:

acvp_internal.txt: `pk sig M' expected` from the NIST ACVP sigVer file
  (ML-DSA-NN groups: external/pure with M' = 0 ‖ |ctx| ‖ ctx ‖ M, and
  internal without external mu). Checks `Fips204.verifyInternal`.
calldata.txt: `calldata expected note` for the EIP-8355 interface. Valid
  signatures come from dilithium-py (empty context); malformed variants carry
  the FIPS 204 verdict, not dilithium-py's (it accepts repeated hint indices,
  which Algorithm 21 rejects). For 65/87 the ACVP external/pure rows with an
  empty context are appended as calldata, together with extra malformed
  variants.

For NN = 44 the output is byte-identical to vectors/acvp_internal.txt and
vectors/calldata.txt (written by scripts/gen_vectors.py).

Usage: PYTHONPATH=.ref/pylib python3 scripts/gen_vectors_param.py NN \
         .ref/acvp_sigver.json OUTDIR
"""
import json
import os
import random
import sys

from dilithium_py.ml_dsa import ML_DSA_44, ML_DSA_65, ML_DSA_87

# FIPS 204 Table 1: k, l, eta, tau, lambda, gamma1, omega.
PARAMS = {
    44: (4, 4, 2, 39, 128, 2 ** 17, 80),
    65: (6, 5, 4, 49, 192, 2 ** 19, 55),
    87: (8, 7, 2, 60, 256, 2 ** 19, 75),
}
LIBS = {44: ML_DSA_44, 65: ML_DSA_65, 87: ML_DSA_87}


class Set:
    def __init__(self, nn):
        self.nn = nn
        self.k, self.l, eta, tau, lam, self.gamma1, self.omega = PARAMS[nn]
        self.beta = tau * eta
        self.clen = lam // 4
        self.zbits = (self.gamma1 - 1).bit_length() + 1
        self.zlen = 32 * self.zbits
        self.pk_len = 32 + 32 * self.k * 10
        self.hint_off = self.clen + self.l * self.zlen
        self.sig_len = self.hint_off + self.omega + self.k
        self.lib = LIBS[nn]


def hint_ok(s, sig):
    """FIPS 204 Algorithm 21 well-formedness (strict, unlike dilithium-py)."""
    y = sig[s.hint_off:]
    index = 0
    for i in range(s.k):
        bound = y[s.omega + i]
        if bound < index or bound > s.omega:
            return False
        for idx in range(index, bound):
            if idx > index and y[idx - 1] >= y[idx]:
                return False
        index = bound
    return all(b == 0 for b in y[index:s.omega])


def acvp(s, path, pure_empty=False):
    rows = []
    data = json.load(open(path))
    for group in data["testGroups"]:
        if group["parameterSet"] != f"ML-DSA-{s.nn}" or group.get("externalMu"):
            continue
        if group["signatureInterface"] == "external" and group["preHash"] != "pure":
            continue
        for t in group["tests"]:
            if group["signatureInterface"] == "external":
                ctx = bytes.fromhex(t["context"])
                mprime = bytes([0, len(ctx)]) + ctx + bytes.fromhex(t["message"])
                if pure_empty and not ctx:
                    rows.append((t["pk"].lower() + t["signature"].lower() + t["message"].lower(),
                                 int(t["testPassed"]), f"acvp tcId={t['tcId']}"))
            else:
                mprime = bytes.fromhex(t["message"])
            if not pure_empty:
                rows.append((t["pk"].lower(), t["signature"].lower(), mprime.hex(),
                             int(t["testPassed"])))
    return rows


def calldata_rows(s, extra):
    lib = s.lib
    rng = random.Random(8212)
    rows = []

    def add(pk, sig, msg, expected, note):
        if extra and len(sig) == s.sig_len and len(pk) == s.pk_len:
            # Cross-check against dilithium-py where it implements FIPS.
            lib_ok = lib.verify(pk, msg, sig)
            assert lib_ok == bool(expected) or (lib_ok and not hint_ok(s, sig)), note
        rows.append(((pk + sig + msg).hex(), expected, note))

    for n, mlen in enumerate([0, 1, 31, 32, 69, 70, 71, 135, 136, 137, 205, 206, 207, 1000]):
        pk, sk = lib.key_derive(bytes([n]) * 32)
        msg = bytes(rng.randrange(256) for _ in range(mlen))
        sig = lib.sign(sk, msg, deterministic=True)
        assert lib.verify(pk, msg, sig)
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

    pk, sk = lib.key_derive(bytes([99]) * 32)
    msg = b"malformed"
    sig = lib.sign(sk, msg, deterministic=True)
    hint = sig[s.hint_off:]
    counts = list(hint[s.omega:])
    c, hoff, omega, k = s.clen, s.hint_off, s.omega, s.k
    zmask = (1 << s.zbits) - 1

    def set_z0(raw):
        bad = bytearray(sig)
        v = int.from_bytes(bad[c:c + 3], "little") & ~zmask | raw
        bad[c:c + 3] = v.to_bytes(3, "little")
        return bytes(bad)

    # z coefficient 0 encodes γ1 − 0 = γ1: fails the norm bound.
    bad = bytearray(sig); bad[c:c + 3] = b"\x00\x00\x00"
    add(pk, bytes(bad), msg, 0, "z = gamma1")
    # z coefficient encoding γ1 − β exactly (raw = β): fails (strict <).
    add(pk, set_z0(s.beta), msg, 0, "z = gamma1 - beta")
    # Hint count above ω.
    bad = bytearray(sig); bad[hoff + omega + k - 1] = omega + 1
    add(pk, bytes(bad), msg, 0, "hint count > omega")
    # Decreasing hint counts.
    if counts[0] > 0:
        bad = bytearray(sig); bad[hoff + omega + 1] = counts[0] - 1
        add(pk, bytes(bad), msg, 0, "hint counts decrease")
    # Repeated hint index within a row (FIPS rejects, dilithium-py accepts).
    if counts[0] >= 2:
        bad = bytearray(sig); bad[hoff + 1] = bad[hoff]
        add(pk, bytes(bad), msg, 0, "repeated hint index")
    # Non-zero padding after the last used index.
    if counts[-1] < omega:
        bad = bytearray(sig); bad[hoff + omega - 1] = 1
        add(pk, bytes(bad), msg, 0, "nonzero hint padding")

    if extra:
        # z = −(γ1 − β) (raw = 2γ1 − β) fails; raw = β + 1 and 2γ1 − β − 1
        # pass the norm check but change z.
        add(pk, set_z0(2 * s.gamma1 - s.beta), msg, 0, "z = -(gamma1 - beta)")
        add(pk, set_z0(s.beta + 1), msg, 0, "z = gamma1 - beta - 1")
        add(pk, set_z0(2 * s.gamma1 - s.beta - 1), msg, 0, "z = -(gamma1 - beta - 1)")
        # Hint count exactly ω in the last row (well formed, wrong).
        bad = bytearray(sig); bad[hoff + omega + k - 1] = omega
        add(pk, bytes(bad), msg, 0, "last hint count = omega")
        # Decreasing indices within a row.
        if counts[0] >= 2:
            bad = bytearray(sig); bad[hoff], bad[hoff + 1] = bad[hoff + 1], bad[hoff]
            add(pk, bytes(bad), msg, 0, "decreasing hint indices")
        # Flipped last byte of c~ (the bytes beyond 32 feed SampleInBall).
        bad = bytearray(sig); bad[c - 1] ^= 0x80
        add(pk, bytes(bad), msg, 0, "flipped last c~ byte")
        # Flipped last t1 byte and last z byte.
        bad = bytearray(pk); bad[-1] ^= 1
        add(bytes(bad), sig, msg, 0, "flipped last t1 byte")
        bad = bytearray(sig); bad[hoff - 1] ^= 1
        add(pk, bytes(bad), msg, 0, "flipped last z byte")
        # Valid signature on the malformed-test key, for reference.
        add(pk, sig, msg, 1, "valid malformed-base")

    # Short inputs.
    add(pk, sig[:-1], b"", 0, "one byte short")
    rows.append(("", 0, "empty calldata"))
    return rows


def main():
    nn, acvp_path, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    s = Set(nn)
    assert s.pk_len == len(s.lib.key_derive(bytes(32))[0])
    extra = nn != 44
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "acvp_internal.txt"), "w") as f:
        for row in acvp(s, acvp_path):
            f.write(" ".join(map(str, row)) + "\n")
    rows = calldata_rows(s, extra)
    if extra:
        rows = rows[:-2] + acvp(s, acvp_path, pure_empty=True) + rows[-2:]
    with open(os.path.join(out, "calldata.txt"), "w") as f:
        for data, expected, note in rows:
            f.write(f"{data or '-'} {expected} {note}\n")


if __name__ == "__main__":
    main()
