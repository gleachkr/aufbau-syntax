# Changelog

## Unreleased

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
