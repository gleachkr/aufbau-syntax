# Changelog

## Unreleased

Initial development. The layer stack is complete and tested end to end:

- MM0 statement reader (`parseSpec`) with `@syntax` annotations and spec
  validation.
- Character-level scanner: no-whitespace textbook input, letter families,
  subscripts, alternative readings.
- Surface parser: a port of MM0's dynamic math parser with three declared
  extensions (grouping pairs, assoc-none levels, a closed lint set),
  coercion insertion, and backtracking disambiguation.
- Printer: display mode (canonical-last spellings, full-paren-drop-outer,
  derived spacing, juxtaposed atoms) and engine mode, with round-trip
  laws under test.
- Bidirectional token-rewrite layer (`@syntax rewrite`) with source-span
  origin mapping.
- Engine helpers: `stripSyntaxAnnotations`, `elaboratedDeclarations`,
  `boundVariableBinders`; alignment with the real Aufbau compiler is
  proven in `tests/engine-align.test.ts`.
- Shipped specs: `forallx-calgary-2019`, `forallx-magnus`, `carnap-prop`.
