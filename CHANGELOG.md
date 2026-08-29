# Changelog

## 0.0.5

**Free-standing adjacency.** `@syntax juxtaposed` is now read in its full
generality: adjacency of two expressions of the combiner's sort denotes
the combiner *anywhere*, not only in argument position of a declared name.
With a juxtaposed product `mul` spelled `infixl … prec 70`, `ab` is `a*b`,
`abc` folds left, and `a(bc)` nests right — the arc is the combiner's
canonical infix notation written as nothing, at the same precedence and
associativity, which is why that notation is now required to be infix
(previously any notation satisfied the validator). The arc never reaches
across a written operator, and it is only an offer: a right-hand side
that fails to parse or to coerce simply ends the expression, without
disturbing the diagnostics. Consequence for spec authors: the combiner's
precedence must sit above the predicates over its sort (`*` at 70 over
`=` at 60), just as any written term-level infix must.

Display mode prints the combiner invisibly when the glued form would
reparse to the same tree, parenthesizes an operand whose own notation
rebinds below its slot — nesting against the associativity (`a*(bc)`),
or a loose prefix whose body would swallow what follows (`(λxx)·y`) —
and falls back to the visible token otherwise; engine mode writes the
operator out in full, as before.

**`@syntax juxtaposed compound`.** An opt-in flag admitting parenthesized
groups as glue operands in argument position — `F(x)(y)`, `(lambda x)a` —
folding through the combiner like any other leaf. Opt-in rather than
inferred, because under a variadic sequence with an elided unit (Magnus's
`seq`) a group is already parenthesized application, and a second reading
of the same text is exactly the ambiguity this parser exists to refuse.
`TermInfo` gains a `juxtaposedCompound` field.

**A connective says which unbracketed operands it refuses.** A new per-term
`@syntax forbid <relation>…` annotation, replacing `@syntax assoc-none
<prec>`, which is gone. An operand that is itself an
infix connective and carries no brackets of its own stands in exactly one
of three relations to the operator above it, and each is refused
separately:

| relation | forbids an unbracketed operand that is… | example |
| --- | --- | --- |
| `chain` | the same term, repeated | `A ∧ B ∧ C` |
| `mix` | a different term on the same rung | `A ∧ B ∨ C` |
| `nest` | a term on a tighter rung | `A → B ∧ C` |

The list is closed. Precedence climbing parses an operand of an operator
at `p` with `min ≥ p` and admits only operators at `prec ≥ min`, so an
unbracketed operand's own operator is never *looser* than its parent's,
and a same-rung operand can only fall on the associative side. There is no
fourth case to name.

The old form could say only "this whole rung refuses to chain", which is
at once too coarse and too weak. Too coarse: it cannot forbid `A ∧ B ∨ C`
while allowing `A ∧ B ∧ C`, because a rung has one setting for every
operator on it. Too weak: it cannot state forallx Calgary at all.
`calgary2019OpTable` puts all four connectives on one level with the
conditionals non-associative, so it refuses `P ∧ Q → R` and `P → Q ∧ R`
as well as `P → Q → R`; under the old form the first two parsed happily,
∧ and → being on different rungs.

Saying it by renumbering rungs was not open to us: precedence and
`infixl`/`infixr` are shared with the engine, which refuses two
associativities on one rung (`precedence_mixed_associativity` here,
`PrecedenceAssocMismatch` there), and moving a connective to another rung
would silently re-read the theory's own math strings. So the refusal sits
on the term and is decided on the parse tree — nothing that parsed before
parses differently now, and the accepted set only ever shrinks.

`Spec.assocNone` gives way to `TermInfo.refuses`, a set of the new
`OperandRelation` type. `chain_refused` keeps its name and its
`{operator}` parameter; `mix_refused` and `nest_refused` are new and carry
`{inner, outer}`. The annotation may only sit on a two-place term with an
infix notation — anywhere else it would do nothing — which is validated.

`specs/forallx-calgary-2019.mm0` gives `imp` and `iff` `forbid chain mix
nest` and leaves `and`/`or` untouched, so `P ∧ Q ∨ R` still reads as `(P ∧ Q) ∨ R`
while `P ∧ Q → R` now wants its brackets, as the textbook does.

## 0.0.4 — 2026-08-26

**A parse can be given the enclosing theorem's binder scope.**
`parse(text, { scope })` takes a `Map` of name to sort. A name in scope
reads as a variable of that sort and *stops* reading as whatever the
lexicon declares it to be — which is what the engine's own math parser
does, a theorem's binders shadowing the file's declarations for the length
of that theorem. Nothing is shadowed by default, so no existing call
behaves differently.

Without it, text belonging to a schematic theorem cannot be read at all,
and fails in the worse of the two possible ways. `theorem mp (a b: wff)`
stated as `P → Q` does not refuse against a spec that spells `P` as a
predicate letter — it parses, to `(P snil) → (Q snil)`, and every
downstream artifact is silently about the wrong thing. The *sort* is not
what makes a collision dangerous: `{f: tm}` reads as the function letter
applied to the empty sequence on exactly the same terms.

Scope reaches **elab literals** too. A rule like `$ A ?x:var $ => $ ∀ ?x $`
is how a spec spells a quantifier with a letter that is also a predicate
letter, and its literal matches the raw chunk — so without this a bound `A`
was eaten before it was ever classified, and no scope could reach it. Elab
is a surface convenience the engine never sees, so a binder displaces it on
the same grounds it displaces the lexicon. The consequence is worth stating:
inside a theorem binding `A`, the `A x` spelling of `∀ x` is gone, and `Ax
Fx` refuses rather than silently quantifying.

Two things scope deliberately does not do. It does not shadow **notation** —
a declared token keeps its meaning, because that is what MM0 does with a
math constant however the enclosing theorem binds its variables. (A spec may
therefore still have a letter that is at once a token and a binder name, and
backtracking settles which reading an occurrence wants; a spec that spells
its quantifiers through elab instead, as a merged theory-and-language file
must, does not.) And it does not reach `delaborate`, the display-printing
direction — engine mode does not delaborate, which is the whole output path
a schematic theorem's text takes.

A scoped name is also *bound* for `closed-sentences`: a line of a proof of
`theorem unimp {x: var} …` may mention `x`, because the theorem binds it.

`tests/engine-align.test.ts` now runs two schematic cases through the real
Aufbau compiler, so the claim that our scoped emission is what the engine
reads inside those binders is checked against the engine rather than
asserted.

## 0.0.3 — 2026-08-25

**The sort input is read at is a `parse` argument.**
`parse(text, { sort })` names it; the text must parse to that sort or
coerce into it. The default is unchanged — `provableSort`, the first sort
the file marks `provable` — so no existing call behaves differently. What
this is for is a file that declares several provable sorts, which is what
a merged theory-and-language artifact does when its judgements are
`Γ ⊢ φ`: the caller knows whether it wants a formula or a sequent, and
declaration order is not an answer. `term_not_sentence` now carries the
sort it wanted as well as the sort it got.

**`@syntax role` may sit on a sort** (`SortInfo.roles`, symmetric with
`TermInfo`), and is still **interpreted nowhere**. It is the recommended
place for an application to record which sort *it* means to read at, so
that stays in the spec — which is data — instead of hard-coded per
language id in the caller. The library reading such a role itself was
considered and rejected: a general-purpose parser should not privilege
one sort name.

**`isConnective` no longer keys on a distinguished sort.** A connective is
now an infix constructor *closed over* a `provable` sort — two arguments
of that sort and a result of the same one. `∧` qualifies; `=` over terms
does not (its arguments are of another sort); a turnstile from two
formulas to a judgement does not (it does not return what it takes); the
argument comma does not (`seq` is not provable). A judgement-level
conjunction now gets the same spacing and bracketing as a formula-level
one, which it should. The `parenthesize-binary-only` lint goes through the
same predicate rather than its own copy of it.

**An elab pattern literal is any chunk, declared or not.** It used to have
to be a declared notation token, which it enforced by not matching: a rule
whose literal was a lexicon name read clean and quietly did nothing. The
guard was also only half-applied (template literals were never checked)
and it was not what held chunk anchoring — the delimiters do that. So it
is gone. This is what lets a merged theory-and-language file spell a
quantifier `A` while `A` is also a predicate letter: MM0 gives a math
token one meaning, so the notation has to go, and elab puts the spelling
back.

Two read-time diagnostics take its place, both aimed at rules that would
otherwise be silently dead: `elab_literal_split` for a literal the surface
delimiters cut in two (write it as separate elements), and
`elab_literal_looks_like_capture` for a literal containing `?`, which is a
mis-spaced capture — patterns split on whitespace, so `$ (?x:var) $` is
one literal. Template literals are checked as well for any rule that is
not `input-only`, since delaboration matches them.

`docs/syntax-annotations.md` now also states the three commitments the
layer makes — leftmost, greedy, one sweep per rule — and the shape of rule
to prefer, since a rule can eat a span that had another reading.

## 0.0.2 — 2026-08-24

**Breaking: student input is segmented by declared delimiters, not by the
vocabulary.** 0.0.1 cut input up with character-level maximal munch over
the declared tokens and lexicon names, which made segmentation depend on
what the spec happened to contain — so declaring a term could silently
re-read a string that already parsed. Appending `term ab: tm;` to the
Magnus spec turned `Fab` from `F` of `a` and `b` into `F` of `ab`, and the
printer spelled the new tree back as `Fab`, so no round trip could see it.
Segmentation is now MM0's own tokenizer rule over a delimiter set the spec
declares, fixed before anything is looked up.

**What a 0.0.1 spec must add.** Tight textbook notation is now an explicit
opt-in: a spec that declares no `@syntax delimiter` is read under the
theory's own `delimiter` statement alone, where input is whitespace- and
bracket-separated, so `~~P` and `AxF(x)` stop parsing. Declare the letters
and the operator spellings the language glues — the three specs in
`specs/` show the shape, and `docs/authoring-a-spec.md` covers the choice
this forces (a spec with letter delimiters has one-character letters; a
spec without them has multi-character names and spaced adjacency; no spec
has both).

- `@syntax delimiter` (`docs/syntax-annotations.md`) declares the surface
  set, in both of MM0's forms, unioned with the file's own `delimiter`
  statement, and generalized so that an entry may be any string — `∧`,
  `<->` — where the engine's `[256]bool` table holds only single bytes.
- Three authoring-time checks: `delimiter_unknown` and
  `delimiter_unreachable_name` are errors, `delimiter_token_not_delimited`
  is advice. `Diagnostic` therefore gained a `severity`, and a caller that
  treated every diagnostic as fatal should now filter on it.
- A chunk nothing can be classified as is reported whole — the new
  `unrecognized_chunk` diagnostic — rather than by its first character.
- The property the rewrite exists to buy is under test
  (`tests/monotonicity.test.ts`): vocabulary growth either leaves every
  existing reading identical or is refused at the declaration, never both
  parses and means something else. One consequence worth knowing: a spec
  that declares all 52 letters and spends all 52 as lexicon names — as all
  three examples do — is closed to any further name containing a letter.

Also: a Nix development shell (`nix develop`, or `direnv allow`), carrying
the toolchain CI runs with.

## 0.0.1 — 2026-08-24

Initial development. The layer stack is complete and tested end to end:

- MM0 statement reader (`parseSpec`) with `@syntax` annotations and spec
  validation.
- Character-level scanner: no-whitespace textbook input, declared-name
  and `@vars` lexicon tokens, alternative readings.
- Surface parser: a port of MM0's dynamic math parser with declared
  extensions only (grouping pairs, assoc-none levels, a closed lint set,
  per-term `elided` and `juxtaposed`), coercion insertion, and
  backtracking disambiguation.
- Printer: display mode (canonical-last spellings, full-paren-drop-outer,
  derived spacing, elision, juxtaposed atoms) and engine mode, with
  round-trip laws under test.
- Bidirectional token-elaboration layer (`@syntax elab`) with source-span
  origin mapping.
- Engine helpers: `stripSyntaxAnnotations`, `boundVariableBinders`;
  alignment with the real Aufbau compiler is proven in
  `tests/engine-align.test.ts`.
- Example specs: `forallx-calgary-2019`, `forallx-magnus`, `carnap-prop`.
- Packaging and CI: the published package is code only — `dist/` — with the
  specs in this repository demoted to examples and fixtures, since a spec
  encodes a textbook's conventions and belongs to the application teaching
  from it. A `tsc` build to `dist/` (JavaScript plus declarations),
  a Node smoke test of the built artifact, and the two GitHub Actions
  workflows Aufbau uses — tests on every push and pull request, canary
  publishes from `main`, stable publishes from a `v1.2.3` tag, both with npm
  provenance. See `docs/releasing.md`.

Replaced before this first release: the original `@syntax family`
letter-schema mechanism (letter ranges, subscript lexing, template
elaboration, combiner discovery by shape). The lexicon is now ordinary
MM0 — declared terms plus the engine's `@vars` pools — with two per-term
annotations, `elided` and `juxtaposed`, carrying what the declarations
cannot say. Deliberate casualties: subscripted atoms (`x_1`, `P0`; the
vocabulary is finite) and one-letter-two-kinds (bare `P` is now the
seq-taking declaration applied to the elided empty sequence, so trees read
`P(snil)`).

Also renamed before this first release: `@syntax rewrite` is now `@syntax
elab`. The engine's `@rewrite` marks directed rules over *terms* for
proof-search normalization, and theories carrying both annotations read
badly; this layer only ever rewrites tokens, elaborating surface spelling
on the way in and delaborating on the way out.
