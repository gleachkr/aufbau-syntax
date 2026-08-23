# The `@syntax` annotation reference

`@syntax` annotations ride MM0's `--|` doc-comment channel — the same one
Aufbau uses for `@acui`, `@congr`, `@rewrite`, `@vars` and the rest. One annotation per
line, attached to the statement that follows it. Anything that is not
`@syntax` is *foreign*: preserved as data, never interpreted here — with
one deliberate exception, `@vars`, which is read *and* preserved (see
below). Before a spec is handed to the Aufbau engine (which rejects
annotations it does not know), strip the `@syntax` lines with
`stripSyntaxAnnotations`; everything else in the file is already the
engine's language.

Attachment rules:

| Annotation | Attaches to |
|---|---|
| `juxtaposed` | a binary term whose arguments and result share one sort |
| `elided` | a nullary term |
| `role` | a `term` or `def` |
| everything else | any statement — the effect is spec-wide |

## The lexicon needs no `@syntax` at all

The letters of a textbook language are ordinary MM0 declarations, and the
variables are the engine's own `@vars` pools:

```text
--| @vars s t u v w x y z
sort var;

term F (s: seq): wff;
term f (s: seq): tm;
```

- **Variables and constants** are `@vars` tokens: a token in a sort's pool
  is a leaf identifier of that sort. Whether a quantifier can bind it
  falls out of the quantifiers' binder sorts (`all {x: var}` binds `var`,
  not `name`), so Calgary-style names are just `@vars` on `name` — the
  same treatment the proof theories already give them. `@vars` is an
  engine annotation; it is never stripped, and a token in a pool may not
  also be a declared term (validated).
- **Predicates, function symbols, and sentence letters** are declared
  terms. A term *with* a notation is spelled by its notation; a term
  without one is spelled by its name — MM0's own application rule, read
  character-level, so `F(a,b)` is application syntax with no machinery
  behind it. The argument-sequence trick (one `seq` argument, built by an
  infix comma) makes one letter variadic; `elided` (below) makes its
  nullary use — the sentence letter, the constant — the same declaration.
- **Alias spellings** are extra notations on one constructor; all parse,
  and the **last declared is canonical** — it is what the printer writes.
  Put the ASCII forms first and the display glyph last.
- **Spacing** is derived: the display printer spaces sentential
  connectives (infix over the provable sort: `P ∧ Q`) and sets everything
  else tight (`¬P`, `∀x`, `a=b`, `R(a,b)`).
- **Display parenthesization** is derived: connective compounds are always
  parenthesized (the textbook full-paren convention), everything else
  bare; see `display drop-outer-parens` for the outermost pair.

The vocabulary is finite — MM0's nature. There is no subscript scheme; a
book that leans on `x_1` can declare a few such names explicitly (they
are valid MM0 identifiers).

## `elided`

```text
--| @syntax elided
term snil: seq;
```

This term may go unwritten. Parsing, a declared name expecting an
argument of `snil`'s sort that finds none gets `snil` supplied — bare `P`
parses as `P(snil)`, the 0-ary use of the predicate letter. Printing,
display drops it again (bare `P`), and engine mode writes it out in full
(`P (snil)`). One nullary term per sort (validated).

## `juxtaposed`

```text
--| @syntax juxtaposed
term scomma (s t: seq): seq;
```

Adjacency of this combiner's sort denotes it. Declared on the sequence
combiner, it makes a predicate's arguments glue — `Rxy` is `R` applied to
the sequence `x·y` — the pre-2019 forallx shape. The annotated term must
be binary and homogeneous (`S × S → S`), must also carry a notation (the
engine cannot read invisibility — engine mode prints `x , y`), and is
unique per sort (all validated).

What glues: self-delimiting single-token operands — `@vars` tokens,
nullary declared names, and nullary notations (an `∅`-style constant) —
whose sort coerces into the combiner's, consumed greedily. Nested
juxtaposed applications (`Ffxy`) are deliberately not operands yet:
under variadic sequences they are ambiguous, and that extension is
deferred. So is free-standing adjacency (`ab` for `a*b` in a group-theory
spec) — the annotation's meaning is written to cover it, the parser does
not implement it yet.

This is a *parser* behavior, deliberately not an elab rule: `AxFx`
versus `Axy` can only be settled by trying the quantifier reading first
and falling back — Carnap's ordered alternatives, reproduced.

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
  position. Only variables of sorts some quantifier binds count; a
  `@vars` constant (Calgary's names) cannot be "free".

`parse(text, { lints: false })` reads text without them.

## `display <option>`

- `drop-outer-parens` — remove the one redundant pair the full-paren
  convention leaves around the whole formula.
- `rotate-brackets <pairs…>` — reserved: accepted and carried on the spec,
  not yet honored by the printer.

## `elab $ <pattern> $ => $ <template> $ [input-only]`

```text
--| @syntax elab $ ( ?x:var ) $ => $ ∀ ?x $
```

A bidirectional token rule, named for the direction it runs on input:
elaboration, surface spelling to canonical tokens, with the reverse pass
delaborating canonical output back into the textbook's spelling. (The
engine's own `@rewrite` is a different thing entirely — directed rules
over *terms*, used for normalization during proof search. This layer never
sees a term.)

The pattern is a sequence of literal tokens and captures `?name:sort`
(optionally `+` one-or-more or `?` optional); the template is literal
tokens and references `?name`, where `?name<sep>*` joins a `+` capture's
repeats with a separator token.

A capture's class is a **sort**: it matches any single lexicon name — a
`@vars` token or a nullary declared term — whose sort coerces into it
(`?t:tm` takes constants and variables alike). The layer is deliberately
regular, and nesting facts (bracket matching, precedence) belong to the
parser.

Forward, each rule makes **one left-to-right pass** in declaration order,
resuming after each replacement — no fixpoints, termination by
construction. An origin map carries every offset back to the source, so
diagnostics and term spans point at what the writer typed.

Backward — delaboration — the invertible rules run over display output in
reverse order: template as pattern, pattern as replacement. A linear rule
read backward *is* the display convention — the Quine rule above prints
`∀x` as `(x)`. A rule that drops or duplicates a capture has no
delaborator, so it must be marked `input-only` (validated) and is skipped
when printing.

## `role <name>`

```text
--| @syntax role conditional
term imp (p q: wff): wff;
```

Passthrough metadata naming what a constructor *means* to a consumer — a
truth-table evaluator looks for `conjunction`, a model checker for
`forall`. The library records roles on `TermInfo` and interprets none of
them. Lexicon letters need no roles: a predicate *is* a term returning
the provable sort, a function one returning a term sort — derivable from
shape.
