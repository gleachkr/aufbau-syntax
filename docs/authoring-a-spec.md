# Authoring a language spec

A spec is one `.mm0` file: ordinary MM0 declarations carrying the
signature and notations, plus [`@syntax` annotations](syntax-annotations.md)
for what MM0 cannot say. The three shipped specs are worked examples:

- `specs/forallx-calgary-2019.mm0` — parenthesized predicates, shared
  connective rungs, chain refusal, bracket discipline, closed sentences.
- `specs/forallx-magnus.mm0` — juxtaposed variadic atoms (`Rxy`), open
  formulas, permissive brackets.
- `specs/carnap-prop.mm0` — a propositional language: five separate
  rungs, ASCII only, bare-digit subscripts.

## The shape of a first-order spec

1. **Sorts and coercions.** The two-variable-sort pattern from Aufbau's
   own forallx theory: `var` (bindable) and `name` (constants), both
   coercing into `tm`, and `tm` into `seq`:

   ```mm0
   provable sort wff;
   --| @syntax family var s-z subscripts
   sort var;
   sort name;
   sort tm;
   sort seq;
   term v2t (x: var): tm;
   coercion v2t: var > tm;
   ...
   ```

2. **The argument-sequence trick.** Predicates take one `seq`, built by an
   infix comma, so one predicate letter is variadic — `F(a)` and `R(a,b,c)`
   share a shape. This is the same encoding Aufbau's zach.mm0 uses for its
   proof theory, which is the point: the surface spec *is* an engine
   theory, or the start of one.

   ```mm0
   term scomma (s t: seq): seq;
   infixl scomma: $,$ prec 10;
   ```

3. **Letter families**, argument-taking before nullary when ranges
   overlap. Templates are placeholder terms (`_pred`, `_const`) that each
   used letter elaborates.

4. **Connectives** — one `term` plus one notation per accepted spelling,
   display glyph last (it becomes canonical). Precedence rungs are the
   textbook's: Calgary shares one rung for ∧/∨ (grouping is positional),
   the `prop` system separates them.

5. **Quantifiers** — binding terms (`{x: var} (p: wff x)`) with prefix
   notations. Give them the same precedence as negation, so `∀x~F(x)` and
   `~∀xF(x)` both read without brackets, and identity a *higher* one, so a
   quantifier's scope covers a whole atomic identity (`∀x∀yf(x,y)=f(y,x)`)
   but stops before any connective.

6. **Sugar by definition.** `a ≠ b` is a `def` whose definiens is the
   negated identity — the tree holds `neq`, consumers may unfold, and the
   printer uses its own canonical token. Prefer a def over a rewrite rule
   whenever the sugar is *semantic*.

7. **Refusals and display** — `assoc-none`, `lint`, and `display` lines,
   conventionally at the top of the file.

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
Add `elaboratedDeclarations(language, terms)` for the letters your
formulas used, and `boundVariableBinders(terms)` on the theorem statement.
