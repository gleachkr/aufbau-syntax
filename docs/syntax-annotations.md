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
  connectives (infix closed over a `provable` sort: `P ∧ Q`) and sets
  everything else tight (`¬P`, `∀x`, `a=b`, `R(a,b)`).
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

## `juxtaposed [compound]`

```text
--| @syntax juxtaposed
term scomma (s t: seq): seq;
```

Adjacency of this combiner's sort denotes it, anywhere. The annotated
term must be binary and homogeneous (`S × S → S`), must carry an *infix*
notation — adjacency inherits its precedence and associativity, and the
engine cannot read invisibility either way (engine mode prints `x , y`)
— and is unique per sort (all validated).

The reading has two faces. In **argument position**, a declared name's
arguments glue — `Rxy` is `R` applied to the sequence `x·y`, the
pre-2019 forallx shape. What glues there: single-chunk operands —
`@vars` tokens, nullary declared names, and nullary notations (an
`∅`-style constant) — whose sort coerces into the combiner's, consumed
greedily. **Free-standing**, adjacency of any two expressions of the
sort is the combiner itself, written as nothing: with a juxtaposed
product `mul` at `infixl … prec 70`, `ab` is `a*b`, `abc` folds left,
and `a(bc)` nests right, exactly as the visible operator would. The arc
never reaches across a written infix, and it is only ever an offer: a
right-hand side that fails to parse, or to coerce into the combiner's
sort, simply ends the expression.

Because adjacency *is* the combiner's notation, the notation's
precedence must sit where a written term-level infix would: **above**
the predicates over its sort. A product at `prec 70` under an `=` at
`prec 60` reads `ab=c` as `(ab)=c`; number them the other way around and
`ab=c` has no parse at all, since the glue slot swallows `b=c` and then
cannot coerce it.

`@syntax juxtaposed compound` additionally admits a parenthesized group
as a glue operand in argument position — `F(x)(y)`, `Fa(b)`,
`(lambda x)a` — folding through the combiner like any other leaf. This
is opt-in rather than inferred because under a variadic sequence with an
elided unit (Magnus's `seq`) the group is already spoken for: `P(Q)` is
parenthesized application, and a second reading of the same text is
exactly the ambiguity this parser exists to refuse.

Glue is not this annotation's to grant, though: `Rxy` is three operands
only if the delimiters already cut it into three chunks. A spec that
glues declares its letters (see `delimiter` above); one that does not
gets `R x y`, spaced.

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

## `forbid <relation>…`

```text
--| @syntax role conditional
--| @syntax forbid chain mix nest
term imp (ph ps: wff): wff;
```

Which unbracketed operands this connective refuses. The annotation sits on
the `term` and lists the relations an operand may not stand in to it:

| relation | forbids an unbracketed operand that is… | example |
| --- | --- | --- |
| `chain` | the same term, repeated | `A ∧ B ∧ C` |
| `mix` | a different term on the same rung | `A ∧ B ∨ C` |
| `nest` | a term on a tighter rung | `A → B ∧ C` |

The three are exhaustive. Precedence climbing parses an operand of an
operator at `p` with `min ≥ p` and admits only operators at `prec ≥ min`,
so an unbracketed operand's own operator is never *looser* than its
parent's; and a same-rung operand can only fall on the associative side,
since the other side parses at `p + 1`. There is no fourth case to name.

An unlisted relation is permitted, so an unmarked term refuses nothing,
which is the ordinary reading and the default. Repeating the annotation
accumulates. It is per-operator, so forbidding something of the
conditionals says nothing about conjunction. Only a two-place term with an
infix notation may carry it (validated) — anywhere else it would sit and do
nothing.

They constrain the *surface* only. Precedence and `infixl`/`infixr` are
shared with the engine, which will not accept two associativities on one
rung, so a refusal is stated here rather than by moving a notation to
another level — and setting one never re-reads a formula that already
parsed.

Some conventions, for orientation:

- forallx Calgary 2019 gives `imp` and `iff` `forbid chain mix nest` and
  leaves `and`/`or` alone: `(P ∧ Q) → R` wants its brackets, `P ∧ Q ∨ R`
  does not.
- Carnap's default table is `forbid chain mix`, so `P ∧ Q → R` passes while
  `P → Q → R` does not.
- `forbid mix` on `and`/`or` is "∧ and ∨ never abut unbracketed", leaving
  each free to repeat.

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

`parse(text, { sort })` names the sort the result is read at: the text
must parse to that sort or coerce into it, or it is refused
(`term_not_sentence`, which carries both the sort it got and the one it
wanted). The default is `provableSort` — the first sort the file marks
`provable`, MM0's own way of saying "assertable" — which is the whole
story for a file with one such sort. A file with several has a real
choice to make, and the caller is who knows: from one merged
theory-and-language artifact, a translation exercise reads at the formula
sort and a proof widget at the judgement sort. The library privileges
neither; see `role` below for keeping the choice in the spec.

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

A literal is **any single chunk**, with no requirement that it appear in
the spec's vocabulary. That is the point of the layer: it exists to accept
surface forms the MM0 grammar rejects, and the Quine rule above already
makes `(x)` mean something no declaration mentions — so constraining the
pieces while the whole is unconstrained would buy nothing. The one
requirement is *single chunk*: matching compares a literal against the
chunk at the scan point, and the surface delimiters fixed that chunk's
boundaries before anything was looked up. A literal the delimiters would
split is reported at read time (`elab_literal_split`) rather than left to
match nothing; write it as separate elements, as the rules here already
write `$ ( ?x:var ) $`. A literal containing `?` is reported too
(`elab_literal_looks_like_capture`) — a capture is its own element, and
the pattern is split on whitespace, so `$ (?x:var) $` is one literal and
never what was meant.

**A consequence worth stating.** Once literals need not be declared, the
spec's declarations are no longer the complete account of what a student
may type: whatever an elab literal absorbs is gone before the parser runs.
Tooling that enumerates a language's surface vocabulary — a symbol
palette, an "expected one of…" message — must read `spec.elabRules` as
well as the notations and the lexicon.

Forward, each rule makes **one left-to-right pass** in declaration order,
resuming after each replacement — no fixpoints, termination by
construction. An origin map carries every offset back to the source, so
diagnostics and term spans point at what the writer typed.

**What that commits you to.** Three properties, none of which the parser
has — the parser backtracks over ambiguity, but only over what reaches it,
and this layer decides what does:

- *Leftmost* — the first match at the earliest scan point wins, and the
  span it consumed is replaced and never re-examined.
- *Greedy* — a `+` capture takes the maximum it can, and never gives one
  back so that the rest of the pattern can match.
- *One sweep per rule*, in declaration order — a later rule sees what
  earlier rules emitted, never the reverse.

So a rule can eat a span that had another reading. Prefer patterns
**anchored by a leading literal**, a spelling you chose, over
capture-initial ones, which fire wherever the sorts line up. Anchoring
lowers the odds; it does not prove the span had no other parse, and
nothing at read time can. The dialect where it genuinely breaks is one
with **both letter-spelled quantifiers and juxtaposed predication**, where
`Ax` really is both `∀x` and A-applied-to-x: there juxtaposition has to be
a parser behavior (`@syntax juxtaposed`), as it is for Magnus. Calgary has
the first and not the second, Magnus the second and not the first.

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

Passthrough metadata naming what a declaration *means* to a consumer — a
truth-table evaluator looks for `conjunction`, a model checker for
`forall`. The library records roles and **interprets none of them**.
Lexicon letters need no roles: a predicate *is* a term returning a
provable sort, a function one returning a term sort — derivable from
shape.

A role may sit on a **sort** as readily as on a term, recorded the same
way, on `SortInfo.roles`:

```text
--| @syntax role sentence
sort wff;
```

Still uninterpreted here — but this is the shape to reach for when an
application has to pick a sort out of a file that declares several. The
sort student input is read at is a `parse` argument, not a property of
the spec (see below); a consumer that would rather not hard-code `"wff"`
against a language id can read it off the spec instead:

```ts
const sentence = [...spec.sorts.values()].find((s) =>
  s.roles.includes("sentence"),
)?.name;
language.parse(text, { sort: sentence ?? undefined });
```

That keeps the choice where it belongs — in the spec, which is data —
without the library privileging one sort name.
