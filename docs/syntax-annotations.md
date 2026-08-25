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
| `role` | a `sort`, a `term`, or a `def` |
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
  connectives (infix over the sentence sort: `P ∧ Q`) and sets everything
  else tight (`¬P`, `∀x`, `a=b`, `R(a,b)`).
- **Display parenthesization** is derived: connective compounds are always
  parenthesized (the textbook full-paren convention), everything else
  bare; see `display drop-outer-parens` for the outermost pair.

The vocabulary is finite — MM0's nature. There is no subscript scheme; a
book that leans on `x_1` can declare a few such names explicitly (they
are valid MM0 identifiers).

## `delimiter $ <entries…> $`

```text
--| @syntax delimiter $ A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $
--| @syntax delimiter $ a b c d e f g h i j k l m n o p q r s t u v w x y z $
--| @syntax delimiter $ ( ) [ ] , $
--| @syntax delimiter $ -> => ⊃ → <-> <=> ≡ ↔ $
```

Where one chunk of student input ends and the next begins. This is the
most consequential line in a spec, because segmentation runs *before*
anything is looked up: the delimiters — not the term table, not the
notations — decide that `AxF(x)` is `A x F ( x )`. Only once a chunk's
boundaries are fixed is it classified, as a notation token, as a lexicon
name, or as both.

The shape and the meaning are MM0's own `delimiter` statement, and the
entries are **unioned** with it: whatever the file's `delimiter $ … $;`
declares for the engine stays in force for student input too. Both of
MM0's forms are accepted — one math string means both sides,

```text
--| @syntax delimiter $ ( ) , $
```

and two give the left and the right lists separately:

```text
--| @syntax delimiter $ ( $ $ ) $
```

The rule the two sides name is the engine's (`MathCursor.readToken` in
Aufbau's `src/trusted/parse.zig`): consume, then break **after** a *left*
delimiter and **before** whitespace or a *right* delimiter. An entry in
both lists therefore always stands alone as its own chunk, which is what
the one-list form gives you and what every spec in `specs/` uses. A
left-only entry closes the chunk it ends but does not break a run that
arrives at it, and a right-only entry does the reverse. Where two entries
could match at one position, the longest spelling wins, so `<->` is one
chunk and not `<`, `-`, `>`.

One generalization beyond MM0: an entry may be **any string**, not a
single byte. That is the whole reason this annotation exists rather than
the plain statement — the engine's delimiter table is a `[256]bool`
indexed by byte, so it cannot hold `∧` (several bytes) or `->` (several
characters), and it does not need to, since engine math strings are
whitespace-separated. Student input is not.

### The quiet default

A spec that declares no `@syntax delimiter` is read under the theory's own
delimiters alone. There, tokens are separated by whitespace and brackets
and nothing else, so `~~P` is one chunk and does not parse. **Tight
textbook notation is an explicit opt-in** — a spec never acquires it by
accident, and adding a notation or a letter never grants it.

### What the reader checks

Only when the spec declares at least one `@syntax delimiter`; without one
none of this can bite.

- `delimiter_unknown` (error) — an entry that is neither a notation
  token, a grouping bracket, nor a lexicon name. It would cut input into
  a piece the parser must then reject: a boundary with nothing behind it.
- `delimiter_token_not_delimited` (warning) — a notation token that is
  not itself a delimiter. Advice, not breakage: the token still reads
  wherever something else bounds it, so with the letters declared `P->Q`
  is fine even if `->` is not. What it warns about is two such tokens
  meeting — `->~` is one chunk unless one of them delimits.
- `delimiter_unreachable_name` (error) — a lexicon name the delimiters
  split, reported with the pieces. No bracketing recovers it, because
  segmentation happened before anything knew the name existed. `elided`
  terms are exempt: they are supplied by the parser and dropped by the
  printer, never typed.

### What it buys

Boundaries fixed before any lookup are what make **declaring vocabulary
unable to change how existing input is cut up.** Under the character-level
maximal munch this replaced, appending `term ab: tm;` to the Magnus spec
silently turned `Fab` from `F` of `a` and `b` into `F` of the single name
`ab` — and since the printer spelled the new tree back as `Fab`, every
round trip stayed clean and nothing downstream could tell. Now a new
declaration has exactly two ways to go: the name survives segmentation and
existing input reads exactly as it did, or the delimiters split it and the
*spec* is refused, at authoring time, naming the pieces. There is no third
outcome in which a student's formula quietly means something else.
`tests/monotonicity.test.ts` holds the property to a corpus.

Only widening the delimiter set can move a boundary — which is why the set
is one visible declaration at the top of the file rather than something
that accumulates as the vocabulary grows.

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

What glues: single-chunk operands — `@vars` tokens, nullary declared
names, and nullary notations (an `∅`-style constant) — whose sort coerces
into the combiner's, consumed greedily. Glue is not this annotation's to
grant, though: `Rxy` is three operands only if the delimiters already cut
it into three chunks. A spec that glues declares its letters (see
`delimiter` above); one that does not gets `R x y`, spaced. Nested
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

`parse(text, { lints: false })` reads text without them — for input that
is grammatical but not surface-idiomatic. `parse(text, { mode: "engine" })`
reads this library's own engine-mode output instead: the theory's
delimiters rather than the surface set, no elaboration, and lints off
unless asked for.

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
the sentence sort, a function one returning a term sort — derivable from
shape.

A role may also sit on a **sort**, where it is recorded on `SortInfo`:

```text
--| @syntax role sentence
sort wff;
```

Of these the library interprets exactly one — `sentence`, because parsing
must have a target sort. `SurfaceLanguage.sentenceSort` is the sort so
marked, and it decides three things: what student input is read at (and
coerced to, hence which terms are refused as `term_not_sentence`), which
constructors count as connectives for forallx's bracket convention and the
printer's spacing, and what the `closed-sentences` lint ranges over.

Without the annotation `sentenceSort` falls back to the first sort
carrying MM0's `provable` modifier, which is what every spec here relies
on. Declaring it matters when a file has **more than one** provable sort:
a theory that states its judgements as `Γ ⊢ φ` in a sort of their own is
saying two different things are assertable, and only the spec knows which
of them a student may be asked to write.
