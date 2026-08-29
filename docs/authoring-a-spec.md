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
  connective rungs, refused operands, bracket discipline, closed sentences.
- `specs/forallx-magnus.mm0` — juxtaposed variadic atoms (`Rxy`), open
  formulas, permissive brackets.
- `specs/carnap-prop.mm0` — a propositional language: five separate
  rungs, ASCII only, nullary atoms.

## Lexicon granularity

Before the sorts and the letters, a spec answers one question: **what
counts as one chunk of student input?** The answer is the [`@syntax
delimiter`](syntax-annotations.md) block at the top of the file, and it is
not a local decision. Segmentation runs before anything is looked up, so
that block fixes how everything the spec goes on to declare will be cut
up. There are two coherent answers, and a spec picks one.

**Declare the letters as delimiters.** Tight textbook notation then works —
`AxF(x)`, `~~P`, `Fxy` — because `A`, `x` and `F` each break a chunk on
both sides. The price is that every letter is one character long, since a
two-character name would be split by the very declaration that makes the
glue possible.

```mm0
--| @syntax delimiter $ A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $
--| @syntax delimiter $ a b c d e f g h i j k l m n o p q r s t u v w x y z $
```

**Leave them undeclared.** Multi-character names then survive — `lambda`,
`succ`, `Cons` — and a spec for a language whose vocabulary is words
rather than letters wants this. The price is that adjacency needs
whitespace or brackets: `F x y`, `F(x,y)`, and `~ ~ P` unless `~` is a
delimiter in its own right.

You cannot have both in one spec, and the reason is worth stating plainly:
a delimiter is a property of a *string*, not of the declaration nearest
it. If `F`, `x` and `y` split, so do the `l`, `a`, `m`, `b`, `d`, `a` of
`lambda`. The reader says so rather than letting you find out from a
student: a lexicon name the delimiters split is
`delimiter_unreachable_name`, an error, reported at its declaration with
the pieces named.

### What the constraint does and does not reach

It bites only on terms spelled **by their own name** — the letters. A term
is surface lexicon only if it has no notation, binds nothing, and is not a
coercion; everything else keeps whatever MM0 name reads best, however
long. In `forallx-calgary-2019`, under a delimiter set that splits every
letter, `imp`, `all`, `v2t`, `snil` and `scomma` are all multi-character
and all fine — `imp` and `all` and `scomma` are spelled by their
notations, `v2t` is a coercion, and `snil` is `elided`.

`elided` is the load-bearing exemption. The empty sequence is supplied by
the parser and dropped by the display printer, so it is never typed; only
engine mode writes it out, and engine text is read back under the
*theory's* delimiters (`( ) [ ] ,`), where `snil` is one chunk again. Hence
the rule of thumb:

> Anything the parser reads must be delimiter-bounded; anything only the
> printer writes need not be.

Operands, notation tokens, grouping brackets and elab literals — pattern
and template alike, since delaboration matches the template — are read, so
they must be bounded. The elided unit is not.

### A letter lexicon closes itself

Follow the first style all the way and the spec becomes closed to new
names, which is worth knowing before it surprises you. All three specs in
`specs/` declare all 52 Roman letters as delimiters *and* spend all 52 as
lexicon names. No name containing a letter can be added to any of them —
not `ab`, not `foo`, not `P1` — because every one of them splits. Since
MM0 identifiers are `[a-zA-Z_][a-zA-Z0-9_]*`, the only shape left is one
with no letters in it at all, like `_0`.

That is the design working, not a wall to route around. It is the same
check that refuses `term ab: tm;` against the Magnus spec, and refusing it
is what keeps `Fab` reading as `F` of `a` and `b` — which the maximal-munch
scanner this replaced would have quietly re-read as `F` of `ab`. If a
language really needs a larger lexicon, that is the second style asking
for its turn: undeclare the letters and spell adjacency out.

## The shape of a first-order spec

1. **Delimiters, first.** The letters the language glues and the
   operator spellings it accepts, so `AxF(x)` and `P->Q` read without
   spaces. Nothing listed may be a string the vocabulary cannot answer
   to, and no letter may be split by it; the reader checks both. Omit
   this and the spec is read under the theory's delimiters alone, where
   input is whitespace-separated.

   ```mm0
   --| @syntax delimiter $ A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $
   --| @syntax delimiter $ a b c d e f g h i j k l m n o p q r s t u v w x y z $
   --| @syntax delimiter $ ( ) [ ] , $
   --| @syntax delimiter $ - ~ ¬ /\ ^ & ∧ \/ | ∨ $
   delimiter $ ( ) [ ] , $;
   ```

2. **Sorts, variables, and coercions.** Variables ride the engine's own
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

   `parse` reads at the first `provable` sort unless the caller names
   another. One provable sort — as here — and there is nothing to decide.
   A file with several, which is what a theory that states its judgements
   as `Γ ⊢ φ` has, is a file whose callers should be passing
   `{ sort }` explicitly rather than relying on declaration order.

3. **The argument-sequence trick, with elision.** Predicates take one
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

4. **The letters** — ordinary declarations, one per letter the language
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

5. **Connectives** — one `term` plus one notation per accepted spelling,
   display glyph last (it becomes canonical). Precedence rungs are the
   textbook's: Calgary shares one rung for ∧/∨ (grouping is positional),
   the `prop` system separates them.

6. **Quantifiers** — binding terms (`{x: var} (p: wff x)`) with prefix
   notations. Give them the same precedence as negation, so `∀x~F(x)` and
   `~∀xF(x)` both read without brackets, and identity a *higher* one, so a
   quantifier's scope covers a whole atomic identity (`∀x∀yf(x,y)=f(y,x)`)
   but stops before any connective.

7. **Juxtaposition, if the book glues** — one annotation on the sequence
   combiner (`--| @syntax juxtaposed` on `scomma`): adjacency at `seq`
   then denotes it, and `Rxy` parses — as does free-standing adjacency
   anywhere an expression of the sort stands (`ab` for `a*b` in an
   algebra spec), at the combiner's own infix precedence, which must
   therefore sit *above* the predicates over its sort. Nothing is said
   per letter — but the letters must be delimiters, or there is no
   adjacency to read: it takes step 1 and step 7 together.

8. **Sugar by definition.** `a ≠ b` is a `def` whose definiens is the
   negated identity — the tree holds `neq`, consumers may unfold, and the
   printer uses its own canonical token. Prefer a def over an elab rule
   whenever the sugar is *semantic*.

9. **Refusals and display** — `lint` and `display` lines, conventionally at
   the top of the file under the delimiter block; and `forbid` on whichever
   connectives want brackets around an operand, beside the `role` that
   names them.

One caution: a token that is both a notation and a letter (Calgary's `A`,
at once ∀ and a predicate) parses fine — the surface parser backtracks —
but inside the *engine's* math strings the notation owns the token, so
formulas using that letter as an atom cannot round-trip through the
engine while the ASCII alias notation is in the engine-facing theory.

When the language and the theory are one file, that stops being a caution
and becomes a choice: keep `prefix all: $A$` and the *term* `A` is
unwritable in the theory's own axioms. Drop the notation and give the
spelling to elab instead:

```mm0
--| @syntax elab $ A ?x:var $ => $ ∀ ?x $ input-only
```

An elab literal need not be declared vocabulary, so `A` may stay a plain
predicate letter. Read the commitments in `syntax-annotations.md` before
reaching for this: it is a rule that eats `A` followed by a variable
before the parser sees either, which is safe in Calgary only because a
predicate there must take parentheses, so `Ax` has no competing reading.

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
(`{ mode: "engine" }`, which reads it under the theory's own delimiters
rather than the surface set) to the same tree; and — the strongest check —
the Aufbau compiler accepts engine output against the stripped spec, which
`tests/engine-align.test.ts` shows how to do with the `iff_refl` trick.

One more is worth copying if the spec is going to be taught from for
years: `tests/monotonicity.test.ts` appends a declaration to each shipped
spec and asserts that every entry of a behavioral corpus either yields the
identical tree or newly parses — never a different tree. It is cheap, and
it is the assertion that a spec's meaning does not drift as its vocabulary
grows.

## What the engine sees

`stripSyntaxAnnotations(source)` is the exact text to hand the compiler —
the engine rejects unknown annotations, and `@syntax` is ours, not its.
The lexicon needs nothing further: the letters are real declarations and
`@vars` is the engine's own. Add `boundVariableBinders(terms)` on the
theorem statement for the variables (bound or free — names included) the
formulas mention.
