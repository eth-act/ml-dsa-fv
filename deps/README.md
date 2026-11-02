# Vendored dependencies

## `evm-semantics/`

The EVM semantics the correctness theorems are stated against (part of the
trust boundary). It is
[powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics) at
`2f8714d6ba960a3de67720019b54513f5bc1a2e3` (the revision `master` pins), with
`.claude/` and `.github/` left out, plus the commits on top that touch
`deps/evm-semantics/` (`git log -- deps/evm-semantics`). The first commit
adding this directory is the verbatim copy; every later commit is a patch to
review.

It is vendored, and required as a path dependency in `lakefile.toml`, only
until the patch is published as a git revision; the require then goes back to
`git = ...`, `rev = ...` and this directory is deleted.
