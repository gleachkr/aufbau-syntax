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

- a **student surface language**: tight, whitespace-free textbook notation
  (`∀xF(x)`, `Fxyz`, `~~P`), alias spellings, per-textbook bracket and
  parenthesization conventions;
- a **display language**: canonical pretty-printing with the textbook's own
  conventions (dropped outer parentheses, juxtaposed arguments and
  products).

Everything a student types is parsed into a term tree over the declared
signature and can be printed back out — either sugared for display, or in
engine mode as spaced canonical text the Aufbau compiler parses directly.
One spec file per textbook system; no code per system.

## The layer stack

1. **Statement reader** — parses the MM0 statement grammar (sorts, terms,
   definitions, axioms and theorems, notations, coercions, delimiters,
   input/output) and `--|` annotations into a `Spec`.
   `@syntax` annotations are understood structurally; all others
   (`@congr`, `@rewrite`, …) pass through as data — except `@vars`,
   `@fallback`, `@acui` and `@relation`, which are read *and* passed
   through: the engine's variable pools are the surface lexicon's
   variables, and the rest are what a consumer needs to compare terms and
   cite rules as the engine does.
2. **Scanner** — segment, then classify. Chunk boundaries come from the
   declared delimiter set alone (MM0's own tokenizer rule, generalized so
   that a delimiter may be any string — `∧`, `<->` — where the engine's
   byte table holds only single bytes), and *never* from the term or
   notation tables; only afterwards is a chunk looked up, as a token, as a
   lexicon name, or as both. Declaring the letters is what dissolves glue,
   and declaring it is what keeps a later declaration from silently
   re-reading input that already parsed.
3. **Elaboration layer** — bidirectional token-pattern rules (`@syntax
   elab`) for textbook sugar that really is local (`(x)Fx` ⇄ `∀xF(x)`,
   `(∀x)` ⇄ `∀x`). Regular by design: one pass per rule, spans threaded
   through, linear rules delaborate for printing. Juxtaposition is
   deliberately *not* here — it needs the parser's backtracking — hence
   the `juxtaposed` flag below.
4. **Math parser** — a faithful port of MM0's dynamic precedence parser,
   extended by declared conventions only: variant grouping pairs, a closed
   set of lints, per-connective `forbid` lists refusing unbracketed
   operands, and per-term `elided` (bare `P` is
   `P(snil)`) and `juxtaposed` (adjacency at a sort denotes its combiner —
   `Rxy` in argument position, `ab` for `a*b` free-standing) flags.
5. **Printer** — last-declared notation is canonical; minimal parentheses
   by precedence; display options; invertible elab rules delaborate.

## Status

Early, but the layer stack is complete and tested end to end: three
example specs (`forallx-calgary-2019`, `forallx-magnus`, `carnap-prop`),
a behavioral corpus transcribed from the parsers this library replaces,
a round-trip law for both print modes checked over random terms on every
spec and corpus file (`tests/round-trip.test.ts`), an acceptance test in
which the real
Aufbau compiler parses this library's engine output and certifies it
tree-identical to hand-written spellings (`tests/engine-align.test.ts`),
and a monotonicity suite pinning the property the delimiter design exists
to buy: declaring vocabulary cannot change how existing input is cut up
(`tests/monotonicity.test.ts`).

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

`printPieces(language, term)` is the display text again, as pieces that
each name the node they came from — `{ text: "∧", path: [1], kind:
"token" }` — for a reader that puts something under each subterm: a truth
table's cell under each connective, a highlight over one subformula. The
pieces join to exactly what `printTerm` displays.

### Reading text that belongs to a theorem

Text taken from inside a theorem is read in that theorem's **scope** — its
binders, name to sort:

```ts
language.parse("~(P & Q) <-> (~P | ~Q)", {
  scope: new Map([                  // theorem … (P Q: wff): …
    ["P", "wff"],
    ["Q", "wff"],
  ]),
});
```

A name in scope reads as a variable of that sort and stops reading as
whatever the lexicon declares it to be — which is what the engine's own
math parser does, a theorem's binders shadowing the file's declarations for
the length of that theorem. Without the scope, a spec that spells `P` as a
predicate letter answers in the metavariable's place, and quietly: `P → Q`
parses, to the wrong thing. Nothing about the *sort* makes a collision
dangerous — `{f: tm}` reads as the function letter `f` applied to the empty
sequence on the same terms.

Notation is not shadowed. Calgary spells ∀ `A`, and a theorem binding
`(A: wff)` still has to be able to quantify; which reading an occurrence
wants is settled by backtracking. Scope also settles what
`closed-sentences` counts as free: a line of a proof of `theorem unimp
{x: var} …` may mention `x`, because the theorem binds it.

`statementScope(statement)` is that scope for a statement of the file
itself, and `parseStatement(language, statement)` reads all of an axiom's
or theorem's formulas in it, the way the engine does. `binderShadows`
says which binders of a scope push a meaning of the language aside — a
lint for whoever wrote the statement.

### Spellings and lists

`spellingsOf(language, term)` lists the tokens a constructor is written
with, canonical first; `spellingMeanings(language, spelling)` goes the
other way, through notations, elab rules and `@vars` pools.
`splitTopLevel(language, text, ",")` splits a list of the language's
formulas outside the grouping pairs it declares, so `R(a, b), F(c)` is two
pieces.

### Terms the engine takes for the same

`normalTerm(language, term)` is a term's normal form under the theory's
`@rewrite` rules and `@acui` laws, as the engine computes it (up to the
order it sorts a bag's variables in), with defs left folded (a bag's
member that a def member covers is folded into it, as the engine does).
`sameTerm(language, derived, stated)` says whether the engine accepts a
line stating `stated` where its rule derives `derived`: the engine's own
decision, through defs (their dot-dummies included), normal forms and the
common targets it searches for between them, step for step. It is a
relation the engine need not keep symmetric. `termKey` is a key that
implies it, for grouping: two terms with one key are the same to the
engine (unless the two normalizations together pass its thousand-step
limit), but two the engine takes for the same can have different keys.
All three take the statement's `variables`
(`statementVariables(statement)`), which say what a rewrite's dependency
check needs to know: `{x / t} φ ⟺ φ` applies only where `φ` does not
mention `x`. `tests/normal-engine.test.ts` checks them against the
compiler, and says where the two still part ways.

`normalTerm` goes as far as the rules go, which can be further than the
engine can prove its way (a rewrite under a term with no `@congr`); the
engine then compares the term as written. `engineForm(language, term)` is
the term as the engine compares it, the one `termKey` keys.

### `@abstract`

`abstractContext(language, { left, right?, leftPlug, rightPlug, hole }, { variables? })`
is the context the engine's `@abstract` (with bare-name plugs) recovers:
`left` with each site made the hole, where a site is the left plug in
`left` against the right plug in `right`, both under their coercions to
the sort where the hole and plugs meet (`n2t a` against `n2t b`, the hole
going in as `v2t x`). The two are walked in parallel and must otherwise
agree; failing that, they are tried once more with their defs opened and
normalized, as the engine retries. Without `right`, every site of the left
plug is one. Null where there is no site, the structures differ, or the
sorts do not meet. The `variables` are the statement's, as above: the
retry's rewrites check dependencies with them. `tests/abstract-engine.test.ts` checks it against the
compiler through a probe rule that shows the context it recovered.

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

There is a flake, as in the other Aufbau repositories — `nix develop`, or
`direnv allow` and let the `.envrc` do it. The shell carries the toolchain CI
runs with — Bun for the suite, Node 24 for the release scripts and the smoke
test — so a failure here is a failure there. When a `flake.lock` bump moves
Bun off the version `.github/workflows/test.yml` pins, move the workflow too.

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
