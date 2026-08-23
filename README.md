# @aufbau/syntax

Surface syntax over MM0, for teaching logic.

An [MM0](https://github.com/digama0/mm0) theory file already fixes a
language's signature, lexicon, binding structure, precedences, and
canonical notation — the letters are ordinary term declarations, the
variables the engine's own `@vars` pools. This library reads such a file —
plus a small set of `@syntax` annotations in
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
   `@congr`, …) pass through as data — except `@vars`, which is read *and*
   passed through: the engine's variable pools are the surface lexicon's
   variables.
2. **Scanner** — character-level maximal munch over the declared tokens and
   lexicon names. No whitespace requirement; glue dissolves here.
3. **Elaboration layer** — bidirectional token-pattern rules (`@syntax
   elab`) for textbook sugar that really is local (`(x)Fx` ⇄ `∀xF(x)`,
   `(∀x)` ⇄ `∀x`). Regular by design: one pass per rule, spans threaded
   through, linear rules delaborate for printing. Juxtaposition is
   deliberately *not* here — it needs the parser's backtracking — hence
   the `juxtaposed` flag below.
4. **Math parser** — a faithful port of MM0's dynamic precedence parser,
   extended by declared conventions only: variant grouping pairs,
   `assoc-none` precedence levels, a closed set of lints, and per-term
   `elided` (bare `P` is `P(snil)`) and `juxtaposed` (adjacency at a sort
   denotes its combiner — `Rxy`) flags.
5. **Printer** — last-declared notation is canonical; minimal parentheses
   by precedence; display options; invertible elab rules delaborate.

## Status

Pre-release, but the layer stack is complete and tested end to end: three
example specs (`forallx-calgary-2019`, `forallx-magnus`, `carnap-prop`),
a behavioral corpus transcribed from the parsers this library replaces,
round-trip laws for both print modes, and an acceptance test in which the
real Aufbau compiler parses this library's engine output and certifies it
tree-identical to hand-written spellings (`tests/engine-align.test.ts`).

```ts
import { parseSpec, printTerm, SurfaceLanguage } from "@aufbau/syntax";

const { spec, diagnostics } = parseSpec(specSource); // an .mm0 + @syntax
const language = new SurfaceLanguage(spec);

const result = language.parse("AxEy~R(x,y)");        // student input
if (result.ok) {
  printTerm(language, result.term, "display");       // "∀x∃y¬R(x,y)"
  printTerm(language, result.term, "engine");        // for the compiler
}
```

See `docs/syntax-annotations.md` for the annotation reference and
`docs/authoring-a-spec.md` for how to write a new system.

## Installing

```sh
bun add @aufbau/syntax          # released
bun add @aufbau/syntax@canary   # the build of the current main
```

The package is code and nothing else: compiled JavaScript and declarations
(`dist/`, emitted by `tsc` — there is nothing to bundle, since there are no
runtime dependencies). Every release is published from CI with npm
provenance; see `docs/releasing.md`.

**The specs in this repository are examples, not a catalogue.** They exist to
exercise the layer stack and to show what a spec looks like; they are not
published, and no application should depend on one. A spec encodes a
*textbook's* conventions, which is the application's subject matter, not the
library's — so an application keeps its own specs in its own tree, in whatever
form its build wants (a string constant, a bundled asset, a database row),
and hands the source text to `parseSpec`. This library's business ends at
"given this spec, parse and print".

## Development

```sh
bun install
bun run validate   # bun test + tsc --noEmit + biome ci
bun run build      # dist/, what actually ships
node scripts/smoke.mjs   # the built package, exercised from plain Node
```

Relative imports inside `src/` carry `.js` extensions. `tsc` emits import
specifiers verbatim, so that is what makes the published `dist/` loadable by
Node's ESM resolver as well as by bundlers — Bun's own resolution is more
forgiving than the world's, which is why the smoke test runs under Node.

`src/` is platform-global-free — no DOM, no Bun, no Workers APIs — because
its consumers are browsers, Cloudflare Workers, and Bun alike. A test
enforces this.
