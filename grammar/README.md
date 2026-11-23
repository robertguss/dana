# Dana Executable Grammar

`dana-grammar` is Dana's executable syntax verifier for Language Reference v0.1. It checks:

- every sample program in `examples/*.dana`;
- every fenced `dana` code block in `docs/reference/README.md` and `README.md`;
- positive and negative syntax tests under `grammar/tests/`.

It is a **dev-only syntax instrument**, not the production compiler (the production compiler
is Zero-Crate Rust under `src/`).

## Design

- **`dana.y`**: Bison builds an IELR(1) parser with **no precedence declarations** and
  `%expect 0` (`-Werror`). Every operator precedence level is its own grammar rule, so a
  successful build mathematically proves the surface grammar has zero shift/reduce and zero
  reduce/reduce conflicts.
- **`lexer.c` / `lexer.h`**: Handles UTF-8 validation, rejects invisible/control characters,
  emits statement-terminating `NL` tokens according to Reference 2.4 line-continuation
  rules, and lexes ISO `Date`/`Timestamp` literals, `:atom` symbols, `?`/`!` identifier
  suffixes, multiline `"""` strings, and `#{...}` string interpolation.
- **`main.c`**: Parses a full module (`dana-grammar FILE.dana`) or a fragment
  (`dana-grammar --fragment FILE`).
- **`check.py`**: Runs `dana-grammar` across `examples/`, `docs/reference/README.md`,
  `README.md`, and `grammar/tests/`.

## Usage

```sh
make grammar
build/dana-grammar examples/expenses.dana
build/dana-grammar --fragment snippet.dana
```
