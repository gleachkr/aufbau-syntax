# @aufbau/syntax

Surface syntax over MM0, for teaching logic.

An [MM0](https://github.com/digama0/mm0) theory file already fixes a
language's signature, binding structure, precedences, and canonical
notation. This library reads such a file — plus `@syntax` annotations in
[Aufbau](https://github.com/gleachkr/Aufbau)'s `--|` comment channel — and
derives from it the two things MM0's own math parser cannot give a logic
classroom:

- a **student surface language**: character-level, whitespace-free textbook
  notation (`∀xF(x)`, `Fxyz`, `~~P`), alias spellings, per-textbook bracket
  and parenthesization conventions;
- a **display language**: canonical pretty-printing with the textbook's own
  conventions (dropped outer parentheses, juxtaposed arguments, rotated
  brackets).

Everything a student types is parsed into a term tree over the declared
signature and can be printed back out — either sugared for display, or in
engine mode as spaced canonical text the Aufbau compiler parses directly.
One spec file per textbook system; no code per system.

## The layer stack

1. **Statement reader** — parses the MM0 statement grammar (sorts, terms,
   notations, coercions, delimiters) and `--|` annotations into a `Spec`.
   `@syntax` annotations are understood structurally; all others (`@acui`,
   `@congr`, …) pass through as data.
2. **Scanner** — character-level maximal munch over the declared tokens and
   letter families. No whitespace requirement; glue dissolves here.
3. **Rewrite layer** — bidirectional token-pattern rules for textbook sugar
   (`Fxy` ⇄ `F(x,y)`, `(x)Fx` ⇄ `∀xF(x)`). Regular by design: one pass per
   rule, spans threaded through, linear rules invert for printing.
4. **Math parser** — a faithful port of MM0's dynamic precedence parser,
   extended by exactly three declared conventions: variant grouping pairs,
   `assoc-none` precedence levels, and a closed set of lints.
5. **Printer** — last-declared notation is canonical; minimal parentheses
   by precedence; display options; invertible rewrites run in reverse.

## Status

Pre-release scaffolding. The API and the `@syntax` annotation vocabulary
are still settling; see `docs/` as stages land.

Published entry point is TypeScript source (`src/index.ts`) — Bun and every
mainstream bundler consume it directly; a `dist/` build step is deliberately
deferred until publishing needs one.

## Development

```sh
bun install
bun run validate   # bun test + tsc --noEmit + biome ci
```

`src/` is platform-global-free — no DOM, no Bun, no Workers APIs — because
its consumers are browsers, Cloudflare Workers, and Bun alike. A test
enforces this.
