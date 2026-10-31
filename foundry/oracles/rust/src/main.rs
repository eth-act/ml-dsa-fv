//! EIP-8355 verdict oracle backed by RustCrypto `ml-dsa`.
//!
//! Reads lines whose first whitespace-separated field is hex calldata (`-` for
//! empty) and prints one `0`/`1` per line: `1` iff the calldata is
//! `pk (1312) ‖ σ (2420) ‖ M` and ML-DSA-44.Verify(pk, M, σ, ctx = "") accepts.
use std::io::{self, BufRead, BufWriter, Write};

use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa44, Signature, VerifyingKey};

const PK_LEN: usize = 1312;
const SIG_LEN: usize = 2420;

fn verdict(cd: &[u8]) -> bool {
    if cd.len() < PK_LEN + SIG_LEN {
        return false;
    }
    let pk = EncodedVerifyingKey::<MlDsa44>::try_from(&cd[..PK_LEN]).expect("pk length");
    let sig = EncodedSignature::<MlDsa44>::try_from(&cd[PK_LEN..PK_LEN + SIG_LEN]).expect("sig length");
    let vk = VerifyingKey::<MlDsa44>::decode(&pk);
    match Signature::<MlDsa44>::decode(&sig) {
        Some(sig) => vk.verify_with_context(&cd[PK_LEN + SIG_LEN..], &[], &sig),
        None => false,
    }
}

fn main() {
    let stdin = io::stdin();
    let mut out = BufWriter::new(io::stdout().lock());
    for line in stdin.lock().lines() {
        let line = line.expect("read");
        let Some(field) = line.split_whitespace().next() else { continue };
        let cd = if field == "-" { Vec::new() } else { hex::decode(field).expect("hex") };
        writeln!(out, "{}", verdict(&cd) as u8).expect("write");
    }
}
