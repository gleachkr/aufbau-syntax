# Changelog

## Unreleased

Initial development. The layer stack is complete and tested end to end:

- MM0 statement reader (`parseSpec`) with `@syntax` annotations and spec
  validation.
- Character-level scanner: no-whitespace textbook input, declared-name
  and `@vars` lexicon tokens, alternative readings.
- Surface parser: a port of MM0's dynamic math parser with declared
  extensions only (grouping pairs, assoc-none levels, a closed lint set,
  per-term `elided` and `juxtaposed`), coercion insertion, and
  backtracking disambiguation.
- Printer: display mode (canonical-last spellings, full-paren-drop-outer,
  derived spacing, elision, juxtaposed atoms) and engine mode, with
  round-trip laws under test.
- Bidirectional token-rewrite layer (`@syntax rewrite`) with source-span
  origin mapping.
- Engine helpers: `stripSyntaxAnnotations`, `boundVariableBinders`;
  alignment with the real Aufbau compiler is proven in
  `tests/engine-align.test.ts`.
- Shipped specs: `forallx-calgary-2019`, `forallx-magnus`, `carnap-prop`.

Replaced before any release: the original `@syntax family` letter-schema
mechanism (letter ranges, subscript lexing, template elaboration,
combiner discovery by shape). The lexicon is now ordinary MM0 — declared
terms plus the engine's `@vars` pools — with two per-term annotations,
`elided` and `juxtaposed`, carrying what the declarations cannot say.
Deliberate casualties: subscripted atoms (`x_1`, `P0`; the vocabulary is
finite) and one-letter-two-kinds (bare `P` is now the seq-taking
declaration applied to the elided empty sequence, so trees read
`P(snil)`).
