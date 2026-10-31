#!/usr/bin/env python3
"""Differential fuzz corpus for the frozen ML-DSA-44 verifier.

Generates EIP-8355 calldata in the categories below (fresh keys, messages of
random and boundary lengths, valid signatures and structured malformations),
asks four verdict oracles (Lean spec, RustCrypto ml-dsa, Go stdlib mldsa,
dilithium-py), executes every case in the Lean EVM semantics for exact frame
gas, and writes:

* foundry/fixtures/fuzz/<category>.txt  replayed by foundry/test/FuzzCorpus.t.sol
  against revm (`calldata expected leanGas schedule category note`);
* vectors/fuzz/oracle_disagreements.txt reproducers for every disagreement
  between oracles, with the Lean-semantics execution, or with the generator's
  own expectation, and every Lean-semantics schedule violation (only written
  when non-empty);
* vectors/fuzz/dpy_known_divergence.txt  cases where only dilithium-py
  accepts because of a repeated hint index (FIPS 204 Algorithm 21 rejects).

Categories:
  valid        fresh key, message of boundary/random length (0..4096), hedged
               or deterministic signature; also z forced to ±(γ1−β−1)
  flip-*       one bit flipped in pk / c~ / z / hint / message
  hint-struct  structured hint malformations (unsorted, duplicated index,
               non-zero padding, counts > ω, decreasing counts, moved row
               boundaries, added/removed/changed indices, ...)
  z-raw        a z coefficient overwritten with a norm-boundary encoding
  z-forced     signatures searched so that one z coefficient is exactly
               ±(γ1−β−1) (must accept) or ±(γ1−β) (must reject although the
               signature verifies with the norm check disabled)
  length       truncated (< 3732), message truncated, message extended
  other        wrong key, other message, random/zero/0xff signatures and keys

Usage (repository root):
    python3 scripts/fuzz_corpus.py [--seed N] [--scale X] [--jobs 8]
"""
import argparse
import copy
import random
import shutil
import time
from collections import Counter

import xcheck_common as xc
from xcheck_common import BETA, GAMMA1, HEADER, HINT_OFF, K, OMEGA, PK_LEN, ML_DSA_44 as ML

Q = 8380417
Z_OFF = PK_LEN + 32            # calldata offset of z
H_OFF = PK_LEN + HINT_OFF      # calldata offset of the hint
BOUNDARY_LENGTHS = [0, 1, 2, 31, 32, 33, 63, 64, 65, 69, 70, 71, 135, 136, 137, 205, 206, 207,
                    341, 342, 343, 477, 478, 479, 1000, 1023, 1024, 1025, 2048, 3000, 4095, 4096]
Z_BOUND = GAMMA1 - BETA        # ‖z‖∞ must be < 130994
RELAXED = copy.copy(ML)        # dilithium-py with the z norm bound moved out of the way
RELAXED.beta = BETA - 2


def centered(c):
    c %= Q
    return c - Q if c > Q // 2 else c


def hint_rows(h):
    counts, rows, prev = list(h[OMEGA:]), [], 0
    for c in counts:
        rows.append(list(h[prev:c]))
        prev = c
    return rows


def encode_hint(rows):
    flat = [i for r in rows for i in r]
    counts, acc = [], 0
    for r in rows:
        acc += len(r)
        counts.append(acc)
    assert len(flat) <= OMEGA
    return bytes(flat + [0] * (OMEGA - len(flat)) + counts)


class Corpus:
    def __init__(self, seed, scale):
        self.rng = random.Random(seed)
        self.scale = scale
        self.cases = []
        self.bases = []  # (pk, sk, msg, sig)

    def n(self, count):
        return max(1, round(count * self.scale))

    def add(self, cd, cat, note, gen=None):
        self.cases.append((bytes(cd), cat, note, gen))

    def message(self, length):
        kind = self.rng.random()
        if kind < 0.1:
            return bytes(length)
        if kind < 0.15:
            return b"\xff" * length
        return self.rng.randbytes(length)

    def sign(self, sk, msg, deterministic):
        rnd = bytes(32) if deterministic else self.rng.randbytes(32)
        return ML._sign_internal(sk, b"\x00\x00" + msg, rnd)

    # ── valid ──────────────────────────────────────────────────────────────
    def valid(self):
        lengths = BOUNDARY_LENGTHS * max(1, round(2 * self.scale))
        lengths += [self.rng.randrange(0, 4097) for _ in range(self.n(150))]
        lengths += [self.rng.randrange(0, 300) for _ in range(self.n(60))]
        for mlen in lengths:
            pk, sk = ML.key_derive(self.rng.randbytes(32))
            msg = self.message(mlen)
            det = self.rng.random() < 0.3
            sig = self.sign(sk, msg, det)
            self.bases.append((pk, sk, msg, sig))
            self.add(pk + sig + msg, "valid", f"mlen={mlen} {'deterministic' if det else 'hedged'}", 1)

    def base(self):
        pk, sk, msg, sig = self.rng.choice(self.bases)
        return bytearray(pk + sig + msg), len(msg)

    # ── single bit flips ───────────────────────────────────────────────────
    def flips(self):
        regions = {
            "flip-pk": (0, PK_LEN, 150),
            "flip-ctilde": (PK_LEN, Z_OFF, 100),
            "flip-z": (Z_OFF, H_OFF, 150),
            "flip-hint": (H_OFF, HEADER, 200),
        }
        for cat, (lo, hi, count) in regions.items():
            for _ in range(self.n(count)):
                cd, _ = self.base()
                pos = self.rng.randrange(lo, hi)
                bit = self.rng.randrange(8)
                cd[pos] ^= 1 << bit
                self.add(cd, cat, f"byte={pos} bit={bit}")
        made = 0
        while made < self.n(100):
            cd, mlen = self.base()
            if mlen == 0:
                continue
            pos = self.rng.randrange(HEADER, len(cd))
            bit = self.rng.randrange(8)
            cd[pos] ^= 1 << bit
            self.add(cd, "flip-msg", f"byte={pos} bit={bit} mlen={mlen}", 0)
            made += 1

    # ── structured hint malformations ──────────────────────────────────────
    def hint_struct(self):
        kinds = [
            "swap-in-row", "dup-insert", "dup-replace", "nonzero-pad", "last-count-over-omega",
            "count-over-omega", "count-decrease", "boundary-shift", "index-change", "remove-hint",
            "add-hint", "all-zero", "last-count-omega", "max-index-append", "count-255",
        ]
        per = self.n(20)
        for kind in kinds:
            made, tries = 0, 0
            while made < per and tries < 50 * per:
                tries += 1
                cd, _ = self.base()
                orig = bytes(cd[H_OFF:HEADER])
                new = self.mutate_hint(kind, bytearray(orig))
                if new is None or bytes(new) == orig:
                    continue
                cd[H_OFF:HEADER] = new
                self.add(cd, "hint-struct", kind, None)
                made += 1

    def mutate_hint(self, kind, h):
        rng = self.rng
        rows = hint_rows(h)
        total = h[OMEGA + K - 1]
        nonempty = [j for j, r in enumerate(rows) if r]
        if kind == "swap-in-row":
            cand = [j for j, r in enumerate(rows) if len(r) >= 2]
            if not cand:
                return None
            j = rng.choice(cand)
            p = rng.randrange(len(rows[j]) - 1)
            rows[j][p], rows[j][p + 1] = rows[j][p + 1], rows[j][p]
            return encode_hint(rows)
        if kind == "dup-insert":  # same set, index repeated: FIPS rejects, dilithium-py accepts
            if total >= OMEGA or not nonempty:
                return None
            j = rng.choice(nonempty)
            p = rng.randrange(len(rows[j]))
            rows[j].insert(p, rows[j][p])
            return encode_hint(rows)
        if kind == "dup-replace":
            cand = [j for j, r in enumerate(rows) if len(r) >= 2]
            if not cand:
                return None
            j = rng.choice(cand)
            p = rng.randrange(len(rows[j]) - 1)
            rows[j][p + 1] = rows[j][p]
            return encode_hint(rows)
        if kind == "nonzero-pad":
            if total >= OMEGA:
                return None
            h[rng.randrange(total, OMEGA)] = rng.randrange(1, 256)
            return h
        if kind == "last-count-over-omega":
            h[OMEGA + K - 1] = OMEGA + 1
            return h
        if kind == "count-over-omega":
            j = rng.randrange(K)
            for t in range(j, K):
                h[OMEGA + t] = rng.randrange(OMEGA + 1, 256) if t == j else max(h[OMEGA + t], h[OMEGA + j])
            return h
        if kind == "count-decrease":
            j = rng.randrange(K - 1)
            if h[OMEGA + j + 1] == 0:
                return None
            h[OMEGA + j] = rng.randrange(h[OMEGA + j + 1] + 1, OMEGA + 1)
            return h
        if kind == "boundary-shift":
            j = rng.randrange(K)
            lo = h[OMEGA + j - 1] if j else 0
            hi = h[OMEGA + j + 1] if j < K - 1 else OMEGA
            choices = [c for c in (h[OMEGA + j] - 1, h[OMEGA + j] + 1) if lo <= c <= hi]
            if not choices:
                return None
            h[OMEGA + j] = rng.choice(choices)
            return h
        if kind == "index-change":
            if not nonempty:
                return None
            j = rng.choice(nonempty)
            p = rng.randrange(len(rows[j]))
            lo = rows[j][p - 1] + 1 if p else 0
            hi = rows[j][p + 1] - 1 if p + 1 < len(rows[j]) else 255
            choices = [v for v in range(lo, hi + 1) if v != rows[j][p]]
            if not choices:
                return None
            rows[j][p] = rng.choice(choices)
            return encode_hint(rows)
        if kind == "remove-hint":
            if not nonempty:
                return None
            j = rng.choice(nonempty)
            rows[j].pop(rng.randrange(len(rows[j])))
            return encode_hint(rows)
        if kind == "add-hint":
            if total >= OMEGA:
                return None
            j = rng.randrange(K)
            free = sorted(set(range(256)) - set(rows[j]))
            rows[j] = sorted(rows[j] + [rng.choice(free)])
            return encode_hint(rows)
        if kind == "all-zero":
            return bytearray(OMEGA + K)
        if kind == "last-count-omega":
            if total >= OMEGA:
                return None
            h[OMEGA + K - 1] = OMEGA
            return h
        if kind == "max-index-append":
            j = rng.randrange(K)
            if total >= OMEGA or (rows[j] and rows[j][-1] == 255):
                return None
            rows[j].append(255)
            return encode_hint(rows)
        if kind == "count-255":
            for t in range(rng.randrange(K), K):
                h[OMEGA + t] = 255
            return h
        raise ValueError(kind)

    # ── z at the norm boundary ─────────────────────────────────────────────
    def z_raw(self):
        raws = [0, 1, 77, 78, 79, 80, GAMMA1 - 1, GAMMA1, GAMMA1 + 1,
                2 * GAMMA1 - 80, 2 * GAMMA1 - 79, 2 * GAMMA1 - 78, 2 * GAMMA1 - 77, 2 * GAMMA1 - 1]
        for _ in range(self.n(150)):
            cd, _ = self.base()
            coeff = self.rng.choice([0, 1, 2, 3, 255, 256, 511, 1023, self.rng.randrange(1024)])
            raw = self.rng.choice(raws + [self.rng.randrange(1 << 18)])
            set_z_raw(cd, coeff, raw)
            self.add(cd, "z-raw", f"coeff={coeff} raw={raw} z={GAMMA1 - raw}")

    def z_forced(self):
        per = self.n(8)
        for target in (Z_BOUND - 1, -(Z_BOUND - 1), Z_BOUND, -Z_BOUND):
            for _ in range(per):
                pk, sk = ML.key_derive(self.rng.randbytes(32))
                msg = self.message(self.rng.choice([0, 1, 70, 136, self.rng.randrange(600)]))
                j, i = self.rng.randrange(4), self.rng.choice([0, 1, 2, 3, 255, self.rng.randrange(256)])
                sig = forced_z_signature(self.rng, sk, msg, j, i, target)
                accepts = abs(target) < Z_BOUND
                assert RELAXED.verify(pk, msg, sig), "forced signature does not verify without the norm check"
                assert ML.verify(pk, msg, sig) == accepts
                self.add(pk + sig + msg, "z-forced", f"z[{j}][{i}]={target} mlen={len(msg)}", int(accepts))
                if accepts:
                    self.bases.append((pk, sk, msg, sig))

    # ── lengths ────────────────────────────────────────────────────────────
    def lengths(self):
        fixed = [0, 1, 31, 32, 33, 1311, 1312, 1313, 3700, 3730, 3731]
        for size in fixed + [self.rng.randrange(HEADER) for _ in range(self.n(120))]:
            cd, _ = self.base()
            self.add(cd[:size], "length", f"truncated to {size}", 0)
        made = 0
        while made < self.n(40):
            cd, mlen = self.base()
            if mlen == 0:
                continue
            cut = self.rng.randrange(1, mlen + 1)
            self.add(cd[:-cut], "length", f"message truncated by {cut} of {mlen}", 0)
            made += 1
        for _ in range(self.n(60)):
            cd, mlen = self.base()
            extra = self.rng.randrange(1, 300)
            tail = bytes(extra) if self.rng.random() < 0.3 else self.rng.randbytes(extra)
            self.add(cd + tail, "length", f"message extended by {extra} (mlen={mlen})", 0)

    # ── other ──────────────────────────────────────────────────────────────
    def other(self):
        for _ in range(self.n(30)):
            a, b = self.rng.sample(self.bases, 2)
            self.add(b[0] + a[3] + a[2], "other", "signature under another key", 0)
        for _ in range(self.n(20)):
            pk, sk, msg, sig = self.rng.choice(self.bases)
            other = self.message(self.rng.randrange(0, 300))
            if other != msg:
                self.add(pk + sig + other, "other", "signature of another message", 0)
        for _ in range(self.n(20)):
            pk, sk, msg, sig = self.rng.choice(self.bases)
            self.add(pk + self.rng.randbytes(len(sig)) + msg, "other", "random signature", 0)
        for _ in range(self.n(20)):
            pk, sk, msg, sig = self.rng.choice(self.bases)
            self.add(self.rng.randbytes(PK_LEN) + sig + msg, "other", "random key", 0)
        for _ in range(self.n(15)):
            size = HEADER + self.rng.randrange(0, 300)
            self.add(self.rng.randbytes(size), "other", "random calldata", 0)
        for fill, name in ((0, "zero"), (0xFF, "0xff")):
            for mlen in (0, 1, 136):
                self.add(bytes([fill]) * (HEADER + mlen), "other", f"all-{name} calldata mlen={mlen}", 0)
                pk, sk, msg, sig = self.rng.choice(self.bases)
                self.add(pk + bytes([fill]) * len(sig) + msg, "other", f"all-{name} signature", 0)
                self.add(bytes([fill]) * PK_LEN + sig + msg, "other", f"all-{name} key", 0)


def set_z_raw(cd, coeff, raw):
    """Overwrite the 18-bit packed encoding γ1 − z of z coefficient `coeff`."""
    bit = coeff * 18
    word = int.from_bytes(cd[Z_OFF + bit // 8:Z_OFF + bit // 8 + 4], "little")
    shift = bit % 8
    word = (word & ~(((1 << 18) - 1) << shift)) | (raw << shift)
    cd[Z_OFF + bit // 8:Z_OFF + bit // 8 + 4] = word.to_bytes(4, "little")


def vec_polys(v):
    """The four polynomials of a dilithium-py length-4 vector (stored either
    as a 1×4 transposed or a 4×1 matrix)."""
    rows = len(v._data)
    return list(v._data[0]) if rows == 1 else [v._data[t][0] for t in range(rows)]


def forced_z_signature(rng, sk, msg, j, i, target, rounds=2000):
    """Signing loop of FIPS 204 Algorithm 7 with a chosen mask: y[j][i] is set
    so that z[j][i] = y[j][i] + (c·s1)[j][i] lands exactly on `target`, all
    other checks (other z coefficients, r0, c·t0, hint weight) as in signing,
    so the result verifies iff `target` passes the norm bound."""
    rho, _, tr, s1, s2, t0 = ML._unpack_sk(sk)
    s1_hat, s2_hat, t0_hat = s1.to_ntt(), s2.to_ntt(), t0.to_ntt()
    a_hat = ML._expand_matrix_from_seed(rho)
    mu = ML._h(tr + b"\x00\x00" + msg, 64)
    alpha = 2 * ML.gamma_2
    for _ in range(rounds):
        y0 = ML._expand_mask_vector(rng.randbytes(64), 0)
        polys = vec_polys(y0)
        for k in (0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6):
            coeffs = [centered(c) for c in polys[j].coeffs]
            coeffs[i] = target - k
            y = ML.M.vector([ML.R(coeffs) if t == j else polys[t] for t in range(4)])
            w = (a_hat @ y.to_ntt()).from_ntt()
            c_tilde = ML._h(mu + w.high_bits(alpha).bit_pack_w(ML.gamma_2), ML.c_tilde_bytes)
            c_hat = ML.R.sample_in_ball(c_tilde, ML.tau).to_ntt()
            z = y + s1_hat.scale(c_hat).from_ntt()
            zp = vec_polys(z)
            if centered(zp[j].coeffs[i]) != target:
                continue
            others = [centered(c) for t in range(4) for n, c in enumerate(zp[t].coeffs)
                      if (t, n) != (j, i)]
            if max(abs(c) for c in others) >= Z_BOUND:
                break
            c_s2 = s2_hat.scale(c_hat).from_ntt()
            if (w - c_s2).low_bits(alpha).check_norm_bound(ML.gamma_2 - BETA):
                break
            c_t0 = t0_hat.scale(c_hat).from_ntt()
            if c_t0.check_norm_bound(ML.gamma_2):
                break
            h = (-c_t0).make_hint(w - c_s2 + c_t0, alpha)
            if h.sum_hint() > OMEGA:
                break
            return ML._pack_sig(c_tilde, z, h)
    raise RuntimeError("forced-z search failed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=8355)
    ap.add_argument("--scale", type=float, default=1.0)
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()
    t0 = time.time()

    corpus = Corpus(args.seed, args.scale)
    corpus.valid()
    corpus.z_forced()
    corpus.flips()
    corpus.hint_struct()
    corpus.z_raw()
    corpus.lengths()
    corpus.other()
    print(f"generated {len(corpus.cases)} cases in {time.time() - t0:.0f}s:",
          dict(Counter(c[1] for c in corpus.cases)))

    records, problems, known = xc.check_cases(corpus.cases, jobs=args.jobs)

    out = xc.ROOT / "foundry" / "fixtures" / "fuzz"
    if out.exists():
        shutil.rmtree(out)
    by_cat = {}
    for r in records:
        by_cat.setdefault(r["cat"], []).append(r)
    for cat, rs in by_cat.items():
        xc.write_fixture(out / f"{cat}.txt", rs)

    fuzz_dir = xc.ROOT / "vectors" / "fuzz"
    dis = fuzz_dir / "oracle_disagreements.txt"
    if problems:
        xc.write_problems(dis, problems)
    elif dis.exists():
        dis.unlink()
    divergent = [r for r in records if r["verdicts"]["dpy"] != r["expected"]]
    xc.write_problems(fuzz_dir / "dpy_known_divergence.txt",
                      [(r, ["dpy accepts repeated hint index"]) for r in divergent
                       if xc.repeated_hint_index(r["cd"])])

    print(f"\n{'category':<12} {'cases':>6} {'accept':>6} {'max gas':>11} {'min slack*':>11}")
    for cat, rs in by_cat.items():
        longs = [r for r in rs if len(r["cd"]) >= HEADER]
        slack = min((r["schedule"] - r["gas"] for r in longs), default=None)
        print(f"{cat:<12} {len(rs):>6} {sum(r['expected'] for r in rs):>6} "
              f"{max(r['gas'] for r in rs):>11} {slack if slack is not None else '-':>11}")
    print("* schedule − Lean gas over calldata ≥ 3732 bytes; below that gas = schedule = 267")
    print(f"known dilithium-py divergences (repeated hint index): {known}")
    print(f"disagreements: {len(problems)}")
    for rec, issues in problems[:20]:
        print(f"  {rec['cat']} {rec['note']}: {issues}")
    print(f"total {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
