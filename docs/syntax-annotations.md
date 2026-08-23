# The `@syntax` annotation reference

`@syntax` annotations ride MM0's `--|` doc-comment channel — the same one
Aufbau uses for `@acui`, `@congr`, `@view` and the rest. One annotation per
line, attached to the statement that follows it. Anything that is not
`@syntax` is *foreign*: preserved as data, never interpreted here. Before a
spec is handed to the Aufbau engine (which rejects annotations it does not
know), strip the `@syntax` lines with `stripSyntaxAnnotations`.

Attachment rules:

| Annotation | Attaches to |
|---|---|
| `family` | a `sort`, or a placeholder `term` |
| `role` | a `term` or `def` |
| everything else | any statement — the effect is spec-wide |

## What needs no annotation at all

Three surface conventions fall out of ordinary MM0 declarations:

- **Alias spellings.** Declare several notations for one constructor; all
  parse, and the **last declared is canonical** — it is what the printer
  writes. Put the ASCII forms first and the display glyph last.
- **Spacing.** The display printer spaces *sentential connectives* (infix
  over the provable sort: `P ∧ Q`) and sets everything else tight (`¬P`,
  `∀x`, `a=b`, `R(a,b)`). This is derived from the declarations, not
  configured.
- **Display parenthesization.** Connective compounds are always
  parenthesized (the textbook full-paren convention), everything else is
  bare; see `display drop-outer-parens` below for the outermost pair.

## `family <class> <letters…> [flags]`

```text
--| @syntax family var s-z subscripts
sort var;

--| @syntax family pred A-Z subscripts
term _pred (s: seq): wff;
```

Declares a letter family: the schema behind textbook lexicons, where any
of `A`–`Z` is a predicate letter. `<letters…>` is one or more words, each a
code-point range (`a-r`) or a literal run (`stuvwxyz`).

- On a **sort**: the letters are variables of that sort — bindable by
  quantifier notations, leaves in terms.
- On a **term** (the *template*, conventionally named `_class`): each
  letter elaborates to a copy of the template. A nullary template gives
  constants or sentence letters; a template over an argument sort gives
  predicates or function symbols. `elaboratedDeclarations` writes the
  `term` statements the engine needs for whatever letters a formula used.

Flags, in any order at the end:

- `subscripts` — underscore subscripts (`x_1`, `F_12`); the underscore
  joins only when digits follow.
- `bare-subscripts` — bare digits (`P0`, `R12`).
- `juxtaposed` — arguments glue straight on (`Fxy`), the pre-2019 forallx
  shape. The parser consumes leaf letters greedily while they coerce into
  the template's argument sort, folding several through the binary
  combiner it finds by shape in the spec (Calgary's `scomma`). This is a
  *parser* behavior, deliberately not a rewrite rule: `AxFx` versus `Axy`
  can only be settled by trying the quantifier reading first and falling
  back — Carnap's ordered alternatives, reproduced.

Families are tried in declaration order; declare argument-taking families
before nullary ones sharing letters, so `f(a)` is a function application
and bare `f` falls through to the constant.

## `brackets <open> <close> [<open> <close>…]`

```text
--| @syntax brackets ( ) [ ]
```

Variant grouping pairs. `( )` is always available; a group must close with
the partner of the bracket that opened it. A grouping token may not also
be a notation token (validated).

## `assoc-none <prec>`

```text
--| @syntax assoc-none 20
```

The named precedence level refuses to chain — `P → Q → R` is an error, per
forallx — regardless of the associativity the notations there declare for
the engine's benefit.

## `lint <name>`

The closed set of refusal conventions:

- `parenthesize-binary-only` — brackets may enclose only a compound whose
  main operator is a sentential connective; `(P)`, `(~P)`, `(a = b)` are
  mistakes, not noise (forallx). Argument parentheses — `R(a,b)` — are
  application syntax and exempt.
- `closed-sentences` — a free variable is an error, reported at its own
  position.

`parse(text, { lints: false })` reads text without them.

## `display <option>`

- `drop-outer-parens` — remove the one redundant pair the full-paren
  convention leaves around the whole formula.
- `rotate-brackets <pairs…>` — reserved: accepted and carried on the spec,
  not yet honored by the printer.

## `rewrite $ <pattern> $ => $ <template> $ [input-only]`

```text
--| @syntax rewrite $ ( ?x:var ) $ => $ ∀ ?x $
```

A bidirectional token-rewrite rule. The pattern is a sequence of literal
tokens and captures `?name:class` (optionally `+` one-or-more or `?`
optional); the template is literal tokens and references `?name`, where
`?name<sep>*` joins a `+` capture's repeats with a separator token.

A capture's class is a **family class name**, or a **sort** — matching any
leaf letter whose sort coerces into it (`?t:tm` takes constants and
variables alike). Captures match single letter tokens; the layer is
deliberately regular, and nesting facts (bracket matching, precedence)
belong to the parser.

Forward, each rule makes **one left-to-right pass** in declaration order,
resuming after each replacement — no fixpoints, termination by
construction. An origin map carries every offset back to the source, so
diagnostics and term spans point at what the writer typed.

Backward, the invertible rules run over display output in reverse order:
template as pattern, pattern as replacement. A linear rule read backward
*is* the display convention — the Quine rule above prints `∀x` as `(x)`.
A rule that drops or duplicates a capture must be marked `input-only`
(validated), and is skipped when printing.

## `role <name>`

```text
--| @syntax role conditional
term imp (p q: wff): wff;
```

Passthrough metadata naming what a constructor *means* to a consumer — a
truth-table evaluator looks for `conjunction`, a model checker for
`forall`. The library records roles on `TermInfo` and interprets none of
them.
