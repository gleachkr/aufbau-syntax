import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { Spec, Term } from "../src/index";
import { parseSpec, SurfaceLanguage } from "../src/index";

/**
 * The behavioral corpus, transcribed from the incumbent parsers this
 * library is built to replace:
 *
 *   - carnap-server `tests/first-order-syntax.test.ts` (forallx Calgary
 *     2019, `src/worker/exercises/first-order/`), and
 *   - carnap-server `tests/truth-table-logic.test.ts` (Carnap's `prop`,
 *     `src/worker/exercises/truth-table/logic/formula.ts`).
 *
 * Deliberate deviations, marked below: `a != b` parses to the `neq` def
 * (whose definiens is the negated identity) rather than eagerly to
 * `not(ideq(...))` — MM0's way of saying "sugar" is a definition; and
 * subscripted atoms (`F_12`, `P0`) are gone — the lexicon is MM0's finite
 * vocabulary of declared names. A bare letter is its seq-taking
 * declaration applied to the elided empty sequence, so the trees below
 * read `(P snil)` where the incumbents had an atom node.
 */

async function load(name: string): Promise<{
  language: SurfaceLanguage;
  spec: Spec;
}> {
  const path = new URL(`../specs/${name}.mm0`, import.meta.url).pathname;
  const { spec, diagnostics } = parseSpec(await readFile(path, "utf8"));

  expect(diagnostics).toEqual([]);

  return { language: new SurfaceLanguage(spec), spec };
}

const calgaryReady = load("forallx-calgary-2019");
const propReady = load("carnap-prop");

/**
 * A term as a compact s-expression, with coercion wrappers elided — they
 * are systematic and would bury what a case is about.
 */
function sexpr(term: Term, coercions: ReadonlySet<string>): string {
  if (term.kind === "variable") {
    return term.name;
  }

  if (term.args.length === 1 && coercions.has(term.term)) {
    const inner = term.args[0];

    if (inner !== undefined) {
      return sexpr(inner, coercions);
    }
  }

  if (term.args.length === 0) {
    return term.term;
  }

  const args = term.args.map((arg) => sexpr(arg, coercions)).join(" ");

  return `(${term.term} ${args})`;
}

async function calgary(source: string): Promise<string> {
  const { language, spec } = await calgaryReady;
  const result = language.parse(source);

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return sexpr(result.term, new Set(spec.coercions.map((c) => c.name)));
}

async function calgaryFails(source: string) {
  const { language } = await calgaryReady;
  const result = language.parse(source);

  if (result.ok) {
    throw new Error(`Expected '${source}' to fail.`);
  }

  const first = result.diagnostics[0];

  if (first === undefined) {
    throw new Error(`Expected '${source}' to report a diagnostic.`);
  }

  return first;
}

async function prop(source: string): Promise<string> {
  const { language } = await propReady;
  const result = language.parse(source);

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return sexpr(result.term, new Set());
}

async function propFails(source: string) {
  const { language } = await propReady;
  const result = language.parse(source);

  if (result.ok) {
    throw new Error(`Expected '${source}' to fail.`);
  }

  const first = result.diagnostics[0];

  if (first === undefined) {
    throw new Error(`Expected '${source}' to report a diagnostic.`);
  }

  return first;
}

describe("segmentation comes before classification", () => {
  test("chunk boundaries are the declared delimiters, nothing else", async () => {
    const { language } = await calgaryReady;

    expect(language.scanner.chunks("AxEy~R(x,y)")).toEqual([
      "A",
      "x",
      "E",
      "y",
      "~",
      "R",
      "(",
      "x",
      ",",
      "y",
      ")",
    ]);
    // The longest spelling wins, and only where it was declared: `<->` is
    // one delimiter, `_12` is one chunk the vocabulary cannot answer to.
    expect(language.scanner.chunks("P<->Q")).toEqual(["P", "<->", "Q"]);
    expect(language.scanner.chunks("F_12(a)")).toEqual([
      "F",
      "_12",
      "(",
      "a",
      ")",
    ]);
  });

  test("a spec that declares no delimiters reads only spaced input", async () => {
    // The quiet default: `surfaceDelimiters` falls back to the theory's own
    // `delimiter` statement, so tight textbook input is an opt-in a spec
    // makes deliberately, never something it acquires by accident.
    const { spec, diagnostics } = parseSpec(`
delimiter $ ( ) $;
provable sort wff;
term P: wff;
term Q: wff;
term not (p: wff): wff;
prefix not: $~$ prec 50;
term and (p q: wff): wff;
infixl and: $/\\$ prec 40;
`);

    expect(diagnostics).toEqual([]);

    const language = new SurfaceLanguage(spec);

    expect(language.scanner.chunks("~P /\\ Q")).toEqual(["~P", "/\\", "Q"]);
    expect(language.parse("~ P /\\ Q").ok).toBe(true);
    expect(language.parse("~P /\\ Q").ok).toBe(false);
  });

  test("engine text is read under the theory's own delimiters", async () => {
    const { language } = await calgaryReady;
    // `snil` is a name the surface set has no way to keep whole — its
    // letters all delimit — which is precisely why engine mode exists.
    const emitted = "((P (snil)) ∧ (Q (snil)))";

    expect(language.scanner.chunks("snil")).toEqual(["s", "n", "i", "l"]);
    expect(language.engineScanner.chunks("snil")).toEqual(["snil"]);
    expect(language.parse(emitted, { lints: false }).ok).toBe(false);
    expect(language.parse(emitted, { mode: "engine" }).ok).toBe(true);
  });
});

describe("forallx Calgary 2019: atoms and terms", () => {
  test("a bare predicate letter is the elided empty sequence", async () => {
    expect(await calgary("P")).toBe("(P snil)");
  });

  test("predicates take parenthesized arguments", async () => {
    expect(await calgary("R(a,b)")).toBe("(R (scomma (a snil) (b snil)))");
  });

  test("subscripts are no longer part of the lexicon", async () => {
    // A deliberate deviation: the incumbent lexed `F_12` as one atom. The
    // lexicon is now MM0's finite vocabulary, and `_12` is nothing — the
    // delimiters cut it off whole, so the whole of it is what is named.
    const error = await calgaryFails("F_12(a)");

    expect(error.id).toBe("unrecognized_chunk");
    expect(error.params).toEqual({ chunk: "_12" });
    expect(error.span).toEqual({ start: 1, end: 4 });
  });

  test("a lowercase letter is a function only when arguments follow", async () => {
    expect(await calgary("f(a) = b")).toBe("(ideq (f (a snil)) (b snil))");
    expect(await calgary("f = b")).toBe("(ideq (f snil) (b snil))");
  });

  test("functions nest", async () => {
    expect(await calgary("f(g(a),b) = c")).toBe(
      "(ideq (f (scomma (g (a snil)) (b snil))) (c snil))",
    );
  });

  test("inequality is the neq definition (sugar by def, not by parse)", async () => {
    expect(await calgary("a != b")).toBe("(neq (a snil) (b snil))");
    expect(await calgary("a ≠ b")).toBe("(neq (a snil) (b snil))");
  });

  test("boolean constants are sentences", async () => {
    expect(await calgary("⊥")).toBe("bot");
    expect(await calgary("_|_")).toBe("bot");
    expect(await calgary("!?")).toBe("bot");
    expect(await calgary("⊤")).toBe("top");
  });
});

describe("forallx Calgary 2019: quantifiers", () => {
  test("A and E bind the variable that follows them", async () => {
    expect(await calgary("AxF(x)")).toBe("(all x (F x))");
    expect(await calgary("ExF(x)")).toBe("(ex x (F x))");
  });

  test("the ASCII and unicode quantifier glyphs agree", async () => {
    for (const source of ["∀xF(x)", "@xF(x)"]) {
      expect(await calgary(source)).toBe("(all x (F x))");
    }

    for (const source of ["∃xF(x)", "3xF(x)"]) {
      expect(await calgary(source)).toBe("(ex x (F x))");
    }
  });

  test("a quantifier letter with no variable after it is a sentence letter", async () => {
    expect(await calgary("A")).toBe("(A snil)");
    expect(await calgary("A /\\ E")).toBe("(and (A snil) (E snil))");
    expect(await calgary("ExE(x)")).toBe("(ex x (E x))");
  });

  test("a quantifier's scope is the primary that follows it", async () => {
    expect(await calgary("AxF(x) -> G(a)")).toBe(
      "(imp (all x (F x)) (G (a snil)))",
    );
    expect(await calgary("Ax(F(x) -> G(a))")).toBe(
      "(all x (imp (F x) (G (a snil))))",
    );
  });

  test("a quantifier's scope still covers a whole identity", async () => {
    // forallx: an atomic identity is one formula, so no brackets are
    // needed — the identity sign binds tighter than the quantifier rung.
    expect(await calgary("AxAyf(x,y) = f(y,x)")).toBe(
      "(all x (all y (ideq (f (scomma x y)) (f (scomma y x)))))",
    );
    expect(await calgary("ExEy~x = y")).toBe(
      "(ex x (ex y (not (ideq x y))))",
    );
  });

  test("quantifiers and negations stack without parentheses", async () => {
    expect(await calgary("AxEy~R(x,y)")).toBe(
      "(all x (ex y (not (R (scomma x y)))))",
    );
    expect(await calgary("~~P")).toBe("(not (not (P snil)))");
    expect(await calgary("~AxF(x)")).toBe("(not (all x (F x)))");
  });

  test("negation scopes over a primary only", async () => {
    expect(await calgary("~P /\\ Q")).toBe("(and (not (P snil)) (Q snil))");
  });

  test("a variable must follow the quantifier symbol", async () => {
    // A deliberate improvement over the incumbent, which fell back to the
    // sentence-letter reading of `A` and reported only "Unexpected 'a'":
    // the quantifier trial got further into the input, so its more
    // specific diagnostic wins for both glyphs.
    expect((await calgaryFails("AaF(a)")).id).toBe("expected_variable");
    expect((await calgaryFails("∀aF(a)")).id).toBe("expected_variable");
  });
});

describe("forallx Calgary 2019: free variables", () => {
  test("an unbound variable is rejected, with its own position", async () => {
    const error = await calgaryFails("F(x)");

    expect(error.id).toBe("free_variable");
    expect(error.params).toEqual({ name: "x" });
    expect(error.span.start).toBe(2);
  });

  test("a variable is free outside the quantifier that binds it", async () => {
    expect((await calgaryFails("AxF(x) /\\ G(x)")).id).toBe("free_variable");
    expect(await calgary("AxF(x) /\\ AxG(x)")).toBe(
      "(and (all x (F x)) (all x (G x)))",
    );
  });
});

describe("forallx Calgary 2019: precedence and association", () => {
  test("conjunction and disjunction share one rung, left-associatively", async () => {
    expect(await calgary("P /\\ Q \\/ R")).toBe(
      "(or (and (P snil) (Q snil)) (R snil))",
    );
    expect(await calgary("P \\/ Q /\\ R")).toBe(
      "(and (or (P snil) (Q snil)) (R snil))",
    );
    expect(await calgary("P /\\ Q /\\ R")).toBe(
      "(and (and (P snil) (Q snil)) (R snil))",
    );
  });

  test("negation binds tighter than any two-place connective", async () => {
    expect(await calgary("~P \\/ Q")).toBe("(or (not (P snil)) (Q snil))");
  });

  test("a conditional binds looser than conjunction", async () => {
    // The rung is still the rung: a conditional takes the whole
    // conjunction, not the letter beside it. Calgary only makes you write
    // the brackets, which is what the three tests below are about.
    expect(await calgary("(P /\\ Q) -> R")).toBe(
      "(imp (and (P snil) (Q snil)) (R snil))",
    );
    expect(await calgary("P -> (Q /\\ R)")).toBe(
      "(imp (P snil) (and (Q snil) (R snil)))",
    );
  });

  // `calgary2019OpTable` puts all four connectives on one level with the
  // two conditionals non-associative, so a conditional takes no unbracketed
  // connective operand at all. Our three refusals name the three ways that
  // can happen, and each is checked separately: a rule that fired on only
  // one of them would still pass a test written against `P -> Q -> R`.
  test("a conditional refuses to chain with itself", async () => {
    const error = await calgaryFails("P -> Q -> R");

    expect(error.id).toBe("chain_refused");
    expect(error.params).toEqual({ operator: "->" });
    expect((await calgaryFails("P <-> Q <-> R")).params).toEqual({
      operator: "<->",
    });
    expect(await calgary("P -> (Q -> R)")).toBe(
      "(imp (P snil) (imp (Q snil) (R snil)))",
    );
  });

  test("a conditional refuses to mix with a biconditional", async () => {
    const error = await calgaryFails("P -> Q <-> R");

    expect(error.id).toBe("mix_refused");
    expect(error.params).toEqual({ inner: "<->", outer: "->" });
    expect(await calgary("P -> (Q <-> R)")).toBe(
      "(imp (P snil) (iff (Q snil) (R snil)))",
    );
  });

  test("a conditional refuses a conjunction nested on either side", async () => {
    const error = await calgaryFails("P /\\ Q -> R");

    expect(error.id).toBe("nest_refused");
    expect(error.params).toEqual({ inner: "/\\", outer: "->" });
    expect((await calgaryFails("P -> Q /\\ R")).id).toBe("nest_refused");
    expect((await calgaryFails("P <-> Q \\/ R")).id).toBe("nest_refused");
  });

  test("nothing was said about conjunction, so it refuses nothing", async () => {
    // The marks are per-operator: `and` and `or` carry none, so they keep
    // the default and go on chaining and mixing with each other. Only the
    // conditionals were told to be strict.
    expect(await calgary("P /\\ Q /\\ R")).toBe(
      "(and (and (P snil) (Q snil)) (R snil))",
    );
    expect(await calgary("P /\\ Q \\/ R")).toBe(
      "(or (and (P snil) (Q snil)) (R snil))",
    );
  });
});

describe("forallx Calgary 2019: parenthesization", () => {
  test("brackets may enclose a two-place compound", async () => {
    expect(await calgary("(P /\\ Q)")).toBe("(and (P snil) (Q snil))");
    expect(await calgary("[P /\\ Q]")).toBe("(and (P snil) (Q snil))");
  });

  test("brackets around anything else are a mistake, not noise", async () => {
    for (const source of ["(P)", "(~P)", "(AxF(x))", "(a = b)", "(⊥)"]) {
      expect((await calgaryFails(source)).id).toBe("group_binary_only");
    }
  });

  test("the mistake is reported at the opening bracket", async () => {
    expect((await calgaryFails("P /\\ (Q)")).span.start).toBe(5);
  });

  test("a group must close with the bracket that opened it", async () => {
    const error = await calgaryFails("(P /\\ Q]");

    expect(error.id).toBe("expected_bracket");
    expect(error.params).toEqual({ bracket: ")" });
  });

  test("argument lists are not subject to the binary-only rule", async () => {
    expect(await calgary("R(a,b)")).toBe("(R (scomma (a snil) (b snil)))");
    expect(await calgary("Ax(R(x,a) -> F(x))")).toBe(
      "(all x (imp (R (scomma x (a snil))) (F x)))",
    );
  });
});

describe("forallx Calgary 2019: errors a writer will actually hit", () => {
  test("an empty formula reports rather than throwing", async () => {
    expect((await calgaryFails("")).id).toBe("expected_formula");
    expect((await calgaryFails("   ")).id).toBe("expected_formula");
  });

  test("an unclosed argument list names the bracket it wanted", async () => {
    const error = await calgaryFails("F(a");

    expect(error.id).toBe("expected_bracket");
    expect(error.params).toEqual({ bracket: ")" });
  });

  test("a missing operand is reported at the end of the source", async () => {
    const error = await calgaryFails("P /\\");

    expect(error.id).toBe("expected_formula");
    expect(error.span.start).toBe(4);
  });

  test("a term where a formula belongs is a sort error", async () => {
    expect((await calgaryFails("a")).id).toBe("term_not_sentence");
  });

  test("an unknown chunk is named", async () => {
    const error = await calgaryFails("P # Q");

    expect(error.id).toBe("unrecognized_chunk");
    expect(error.params).toEqual({ chunk: "#" });
    expect(error.span.start).toBe(2);
  });

  test("the dropped spellings fail rather than mis-parsing", async () => {
    for (const source of ["P and Q", "P or Q", "not P", "F^2(a,b)"]) {
      const { language } = await calgaryReady;

      expect(language.parse(source).ok, source).toBe(false);
    }
  });

  test("juxtaposed predicate arguments are not silently accepted", async () => {
    expect((await calgaryFails("Fx")).id).toBe("unexpected_token");
  });
});

describe("Carnap prop: atoms", () => {
  test("single letters of either case", async () => {
    expect(await prop("P")).toBe("P");
    expect(await prop("p")).toBe("p");
  });

  test("bare digit subscripts are gone — a deliberate deviation", async () => {
    // The incumbent lexed `P0` as one atom; the lexicon is now MM0's
    // finite vocabulary of declared names, and a digit is nothing.
    expect((await propFails("P0")).id).toBe("unrecognized_chunk");
  });
});

describe("Carnap prop: precedence", () => {
  test("conjunction binds tighter than disjunction — separate rungs", async () => {
    // The rung structure Calgary deliberately does not have: `P \/ Q /\ R`
    // groups around the conjunction here, positionally in Calgary.
    expect(await prop("P /\\ Q \\/ R")).toBe("(or (and P Q) R)");
    expect(await prop("P \\/ Q /\\ R")).toBe("(or P (and Q R))");
  });

  test("the conditional chains right, the others left", async () => {
    expect(await prop("P -> Q -> R")).toBe("(imp P (imp Q R))");
    expect(await prop("P <-> Q <-> R")).toBe("(iff (iff P Q) R)");
    expect(await prop("P /\\ Q /\\ R")).toBe("(and (and P Q) R)");
  });

  test("negation is tightest and stacks", async () => {
    expect(await prop("~~~P")).toBe("(not (not (not P)))");
    expect(await prop("~P /\\ Q")).toBe("(and (not P) Q)");
  });

  test("parentheses group anything — no binary-only rule here", async () => {
    expect(await prop("(P)")).toBe("P");
    expect(await prop("(~P) -> (Q)")).toBe("(imp (not P) Q)");
  });
});

describe("Carnap prop: refusals", () => {
  test("unicode connectives are not part of this language", async () => {
    expect((await propFails("P ∧ Q")).id).toBe("unrecognized_chunk");
  });

  test("stray input after a formula is reported", async () => {
    expect((await propFails("P Q")).id).toBe("unexpected_token");
  });

  test("a missing operand is reported", async () => {
    expect((await propFails("P /\\")).id).toBe("expected_formula");
  });
});

describe("the sort input is read at", () => {
  // A theory that keeps its judgements in a provable sort of their own:
  // `⊢` is what may be asserted, a formula is what a student writes. Which
  // of the two a given call wants is the caller's to say; the library
  // defaults to the first provable sort and privileges no sort anywhere
  // else.
  const SEQUENT = `
delimiter $ ( ) $;
provable sort wff;
provable sort judgement;
term P: wff;
term Q: wff;
term and (p q: wff): wff;
infixl and: $&$ prec 40;
term nd (p q: wff): judgement;
infixl nd: $|-$ prec 10;
term jand (p q: judgement): judgement;
infixl jand: $;$ prec 5;
`;

  function language(source: string): SurfaceLanguage {
    const { spec, diagnostics } = parseSpec(source);

    expect(diagnostics).toEqual([]);

    return new SurfaceLanguage(spec);
  }

  test("the default target is the first provable sort", () => {
    const lang = language(SEQUENT);

    expect(lang.provableSort).toBe("wff");
    expect(lang.parse("P & Q").ok).toBe(true);
    // A sequent is not a wff and does not coerce into one.
    expect(lang.parse("P |- Q").ok).toBe(false);
  });

  test("a caller names the sort it wants", () => {
    const lang = language(SEQUENT);
    const sequent = lang.parse("P |- Q", { sort: "judgement" });

    expect(sequent.ok).toBe(true);

    if (sequent.ok) {
      expect(sexpr(sequent.term, new Set())).toBe("(nd P Q)");
    }

    // And the refusal names what it got, at whichever sort was asked for.
    const wrong = lang.parse("P & Q", { sort: "judgement" });

    expect(wrong.ok).toBe(false);

    if (!wrong.ok) {
      expect(wrong.diagnostics[0]?.id).toBe("term_not_sentence");
    }
  });

  test("connectives are closed over a provable sort, whichever it is", () => {
    const lang = language(SEQUENT);

    // Closed over wff, and closed over judgement: both are connectives.
    expect(lang.isConnective("and")).toBe(true);
    expect(lang.isConnective("jand")).toBe(true);
    // The turnstile takes two formulas and returns a judgement, so it is
    // not closed over either — a connective is not merely binary infix.
    expect(lang.isConnective("nd")).toBe(false);
  });

  test("a sort that is not provable is not connective territory", async () => {
    const { language } = await calgaryReady;

    // The argument comma is binary infix and homogeneous, but `seq` is not
    // provable — which is what keeps `R(a,b)` from printing `R((a , b))`.
    expect(language.isConnective("scomma")).toBe(false);
    expect(language.isConnective("and")).toBe(true);
    // Identity returns a wff but takes terms: not closed, so set tight.
    expect(language.isConnective("ideq")).toBe(false);
  });

  test("no provable sort at all leaves the default target open", () => {
    const lang = language("sort tm;\nterm a: tm;");

    expect(lang.provableSort).toBe(null);
    expect(lang.parse("a").ok).toBe(true);
    // Naming the sort still works, and still refuses what does not fit.
    expect(lang.parse("a", { sort: "tm" }).ok).toBe(true);
  });
});
