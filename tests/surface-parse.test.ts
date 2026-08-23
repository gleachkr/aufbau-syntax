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
 * One deliberate deviation, marked below: `a != b` parses to the `neq`
 * def (whose definiens is the negated identity) rather than eagerly to
 * `not(ideq(...))` — MM0's way of saying "sugar" is a definition.
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

describe("forallx Calgary 2019: atoms and terms", () => {
  test("a bare predicate letter is a sentence letter", async () => {
    expect(await calgary("P")).toBe("P");
  });

  test("predicates take parenthesized arguments", async () => {
    expect(await calgary("R(a,b)")).toBe("(R (scomma a b))");
    expect(await calgary("Ax_1R(x_1,a)")).toBe(
      "(all x_1 (R (scomma x_1 a)))",
    );
  });

  test("a subscript needs digits and joins the symbol's name", async () => {
    expect(await calgary("F_12(a)")).toBe("(F_12 a)");
    expect((await calgaryFails("F_")).id).toBe("unrecognized_character");
  });

  test("a lowercase letter is a function only when arguments follow", async () => {
    expect(await calgary("f(a) = b")).toBe("(ideq (f a) b)");
    expect(await calgary("f = b")).toBe("(ideq f b)");
  });

  test("functions nest", async () => {
    expect(await calgary("f(g(a),b) = c")).toBe(
      "(ideq (f (scomma (g a) b)) c)",
    );
  });

  test("inequality is the neq definition (sugar by def, not by parse)", async () => {
    expect(await calgary("a != b")).toBe("(neq a b)");
    expect(await calgary("a ≠ b")).toBe("(neq a b)");
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
    expect(await calgary("A")).toBe("A");
    expect(await calgary("A /\\ E")).toBe("(and A E)");
    expect(await calgary("A_1(b)")).toBe("(A_1 b)");
    expect(await calgary("ExE(x)")).toBe("(ex x (E x))");
  });

  test("a quantifier's scope is the primary that follows it", async () => {
    expect(await calgary("AxF(x) -> G(a)")).toBe("(imp (all x (F x)) (G a))");
    expect(await calgary("Ax(F(x) -> G(a))")).toBe(
      "(all x (imp (F x) (G a)))",
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
    expect(await calgary("~~P")).toBe("(not (not P))");
    expect(await calgary("~AxF(x)")).toBe("(not (all x (F x)))");
  });

  test("negation scopes over a primary only", async () => {
    expect(await calgary("~P /\\ Q")).toBe("(and (not P) Q)");
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
    expect(await calgary("P /\\ Q \\/ R")).toBe("(or (and P Q) R)");
    expect(await calgary("P \\/ Q /\\ R")).toBe("(and (or P Q) R)");
    expect(await calgary("P /\\ Q /\\ R")).toBe("(and (and P Q) R)");
  });

  test("negation binds tighter than any two-place connective", async () => {
    expect(await calgary("~P \\/ Q")).toBe("(or (not P) Q)");
  });

  test("a conditional binds looser than conjunction", async () => {
    expect(await calgary("P /\\ Q -> R")).toBe("(imp (and P Q) R)");
  });

  test("conditionals and biconditionals refuse to chain", async () => {
    const error = await calgaryFails("P -> Q -> R");

    expect(error.id).toBe("chain_refused");
    expect(error.params).toEqual({ operator: "->" });
    expect(await calgary("P -> (Q -> R)")).toBe("(imp P (imp Q R))");
    expect((await calgaryFails("P <-> Q <-> R")).params).toEqual({
      operator: "<->",
    });
    expect((await calgaryFails("P -> Q <-> R")).params).toEqual({
      operator: "<->",
    });
  });
});

describe("forallx Calgary 2019: parenthesization", () => {
  test("brackets may enclose a two-place compound", async () => {
    expect(await calgary("(P /\\ Q)")).toBe("(and P Q)");
    expect(await calgary("[P /\\ Q]")).toBe("(and P Q)");
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
    expect(await calgary("R(a,b)")).toBe("(R (scomma a b))");
    expect(await calgary("Ax(R(x,a) -> F(x))")).toBe(
      "(all x (imp (R (scomma x a)) (F x)))",
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

  test("an unknown character is named", async () => {
    const error = await calgaryFails("P # Q");

    expect(error.id).toBe("unrecognized_character");
    expect(error.params).toEqual({ character: "#" });
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
  test("either case, with bare digit subscripts", async () => {
    expect(await prop("P")).toBe("P");
    expect(await prop("p")).toBe("p");
    expect(await prop("P0")).toBe("P0");
    expect(await prop("R12 /\\ q3")).toBe("(and R12 q3)");
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
    expect((await propFails("P ∧ Q")).id).toBe("unrecognized_character");
  });

  test("stray input after a formula is reported", async () => {
    expect((await propFails("P Q")).id).toBe("unexpected_token");
  });

  test("a missing operand is reported", async () => {
    expect((await propFails("P /\\")).id).toBe("expected_formula");
  });
});
