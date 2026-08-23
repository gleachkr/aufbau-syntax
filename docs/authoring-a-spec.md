# Authoring a language spec

A spec is one `.mm0` file: ordinary MM0 declarations carrying the
signature, lexicon, and notations, plus [`@syntax`
annotations](syntax-annotations.md) for what MM0 cannot say.

A spec is owned by whoever teaches from it, not by this library — it encodes
one textbook's conventions, and those are subject matter, not machinery. The
three specs in `specs/` are worked examples and test fixtures; they are not
published, and an application should keep its own under its own tree. What
the library asks for is the source text; where it came from is not its
business.

The examples:

- `specs/forallx-calgary-2019.mm0` — parenthesized predicates, shared
  connective rungs, chain refusal, bracket discipline, closed sentences.
- `specs/forallx-magnus.mm0` — juxtaposed variadic atoms (`Rxy`), open
  formulas, permissive brackets.
- `specs/carnap-prop.mm0` — a propositional language: five separate
  rungs, ASCII only, nullary atoms.

## The shape of a first-order spec

1. **Sorts, variables, and coercions.** Variables ride the engine's own
   `@vars` annotation — a sort's pool is the surface lexicon of that
   sort, and whether a quantifier can bind a token falls out of the
   quantifiers' binder sorts. Calgary-style names (constants the
   quantifiers cannot touch) are just a pool on a second sort, exactly as
   Aufbau's proof theories treat them:

   ```mm0
   provable sort wff;
   --| @vars s t u v w x y z
   sort var;
   --| @vars a b c
   sort name;
   sort tm;
   sort seq;
   term v2t (x: var): tm;
   coercion v2t: var > tm;
   ...
   ```

2. **The argument-sequence trick, with elision.** Predicates take one
   `seq`, built by an infix comma, so one predicate letter is variadic —
   `F(a)` and `R(a,b,c)` share a shape. Mark the empty sequence `elided`
   and the same declaration covers the nullary use: bare `P` is `P(snil)`,
   the sentence letter; bare `f` is `f(snil)`, the constant. This is the
   same encoding Aufbau's zach.mm0 uses for its proof theory, which is
   the point: the surface spec *is* an engine theory, or the start of one.

   ```mm0
   --| @syntax elided
   term snil: seq;
   term scomma (s t: seq): seq;
   infixl scomma: $,$ prec 10;
   ```

3. **The letters** — ordinary declarations, one per letter the language
   offers. A term with no notation is spelled by its name, so nothing
   else is needed:

   ```mm0
   term F (s: seq): wff;
   term G (s: seq): wff;
   term f (s: seq): tm;
   ```

   The vocabulary is finite — MM0's nature. Declare the alphabet if the
   book offers it all; an exercise's symbolization key can equally append
   just the letters it means.

4. **Connectives** — one `term` plus one notation per accepted spelling,
   display glyph last (it becomes canonical). Precedence rungs are the
   textbook's: Calgary shares one rung for ∧/∨ (grouping is positional),
   the `prop` system separates them.

5. **Quantifiers** — binding terms (`{x: var} (p: wff x)`) with prefix
   notations. Give them the same precedence as negation, so `∀x~F(x)` and
   `~∀xF(x)` both read without brackets, and identity a *higher* one, so a
   quantifier's scope covers a whole atomic identity (`∀x∀yf(x,y)=f(y,x)`)
   but stops before any connective.

6. **Juxtaposition, if the book glues** — one annotation on the sequence
   combiner (`--| @syntax juxtaposed` on `scomma`): adjacency at `seq`
   then denotes it, and `Rxy` parses. Nothing is said per letter.

7. **Sugar by definition.** `a ≠ b` is a `def` whose definiens is the
   negated identity — the tree holds `neq`, consumers may unfold, and the
   printer uses its own canonical token. Prefer a def over an elab rule
   whenever the sugar is *semantic*.

8. **Refusals and display** — `assoc-none`, `lint`, and `display` lines,
   conventionally at the top of the file.

One caution: a token that is both a notation and a letter (Calgary's `A`,
at once ∀ and a predicate) parses fine — the surface parser backtracks —
but inside the *engine's* math strings the notation owns the token, so
formulas using that letter as an atom cannot round-trip through the
engine while the ASCII alias notation is in the engine-facing theory.

## Testing a spec

Parse and print are enough to pin a dialect's behavior:

```ts
const { spec, diagnostics } = parseSpec(source);   // expect [] diagnostics
const language = new SurfaceLanguage(spec);
const result = language.parse("AxF(x) -> G(a)");   // term or diagnostics
printTerm(language, result.term, "display");        // "∀xF(x) → G(a)"
printTerm(language, result.term, "engine");         // for the compiler
```

The round-trip laws worth asserting for any new spec: display output
re-parses to the same tree and prints stably; engine output re-parses
(`{ lints: false }`) to the same tree; and — the strongest check — the
Aufbau compiler accepts engine output against the stripped spec, which
`tests/engine-align.test.ts` shows how to do with the `iff_refl` trick.

## What the engine sees

`stripSyntaxAnnotations(source)` is the exact text to hand the compiler —
the engine rejects unknown annotations, and `@syntax` is ours, not its.
The lexicon needs nothing further: the letters are real declarations and
`@vars` is the engine's own. Add `boundVariableBinders(terms)` on the
theorem statement for the variables (bound or free — names included) the
formulas mention.
