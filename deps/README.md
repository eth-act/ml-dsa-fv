# Vendored dependencies

## `evm-semantics/`

The EVM semantics the correctness theorems are stated against (part of the
trust boundary). It is
[powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics) at
`2f8714d6ba960a3de67720019b54513f5bc1a2e3` (the revision `master` pins), with
`.claude/` and `.github/` left out, plus a patch adding a partial `Amsterdam`
fork (EIP-8024 `DUPN` / `SWAPN` / `EXCHANGE`, EIP-7954 code size). The commit
that adds this directory is the verbatim copy (58e20dd); the patch is the next
commit (cbc0a96), so `git diff 58e20dd cbc0a96 -- deps/evm-semantics` is the
whole trust-boundary change.

`lakefile.toml` requires it as a git package: this repository at cbc0a96
(`subDir = "deps/evm-semantics"`), so the gate sees an ordinary pinned
dependency. Editing this directory therefore changes nothing until the require
is re-pinned to a commit with the edit.

This is temporary: once the patch is published as a revision of
powdr-labs/evm-semantics (or a fork of it), the require goes back to that
`git = ...`, `rev = ...` and this directory is deleted.
