import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { Spec, Term } from "../src/index";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";

/**
 * Free-standing adjacency — `@syntax juxtaposed` read in full generality.
 * Adjacency of two expressions of the combiner's sort denotes the
 * combiner anywhere, not just in argument position of an applying term:
 * group theory's `ab` for `a*b`, composition's `gf` for `g∘f`. The arc
 * borrows precedence and associativity from the combiner's canonical
 * infix notation, so the invisible operator binds exactly as the written
 * one; `@syntax juxtaposed compound` additionally admits parenthesized
 * groups as glue operands in argument position (`P(f)(g)`).
 *
 * The one piece of spec-authoring discipline these cases pin: the
 * combiner must sit at a *higher* precedence than the predicates over
 * its sort (`*` at 70 above `=` at 60), just as a written term-level
 * infix must — otherwise `ab=c` tries to read `b=c` into the glue slot
 * and the sentence has no parse at all.
 */

/** Group theory: constants, a juxtaposed product, a prefix inverse. */
const GROUP = `--| @syntax delimiter $ a b c x y z ( ) * = ⁻¹ $
delimiter $ ( ) * = $;

provable sort eqn;
--| @vars x y z
sort g;

term a: g;
term b: g;
term c: g;

--| @syntax juxtaposed
term mul (s t: g): g;
infixl mul: $*$ prec 70;

term inv (s: g): g;
prefix inv: $⁻¹$ prec 90;

term eq (s t: g): eqn;
infixl eq: $=$ prec 60;
`;

/**
 * A small sequent calculus: contexts are juxtaposed formula lists, so
 * `P Q ⊢ R` is `P, Q ⊢ R` unwritten. The combiner sits *between* its
 * neighbours — above the turnstile over its sort (`,` at 20 over `⊢` at
 * 10) and below the wff connectives (`∧` at 35) — and every glue leaf is
 * a wff arriving through the `wff > ctx` coercion rather than at the
 * combiner's own sort.
 */
const SEQUENT = `--| @syntax delimiter $ P Q R ( ) , ∧ ⊢ $
delimiter $ ( ) , $;

provable sort jdg;
sort wff;
sort ctx;

term P: wff;
term Q: wff;
term R: wff;

term c (p: wff): ctx;
coercion c: wff > ctx;

--| @syntax juxtaposed
term cat (g d: ctx): ctx;
infixl cat: $,$ prec 20;

term and (p q: wff): wff;
infixl and: $∧$ prec 35;

term entails (g: ctx) (p: wff): jdg;
infixl entails: $⊢$ prec 10;
`;

/**
 * Untyped lambda calculus: application is adjacency at a high precedence,
 * abstraction a loose prefix binder — so a body extends as far to the
 * right as it can (`λx xy` is `λx.(x y)`), and applying an abstraction
 * needs the parentheses the textbooks write (`(λx x)y`). The task's own
 * motivating case: the left operand of an application as a parsed group.
 */
const LAMBDA = `--| @syntax delimiter $ x y z K S ( ) · λ = $
delimiter $ ( ) = $;

provable sort eqn;
sort tm;
--| @vars x y z
sort var;

term v (x: var): tm;
coercion v: var > tm;

--| @syntax juxtaposed
term ap (s t: tm): tm;
infixl ap: $·$ prec 100;

term K: tm;
term S: tm;

term lam {x: var} (b: tm x): tm;
prefix lam: $λ$ prec 30;

term equal (s t: tm): eqn;
infixl equal: $=$ prec 50;
`;

/**
 * The same calculus with a dotted binder: `λx.b` as a general notation in
 * place of the bare prefix, plus `.` in the delimiter sets. A
 * *replacement*, not a reordering — the head token `λ` carries exactly
 * one parse rule (`token_conflict`), so the two spellings cannot
 * coexist. Everything else, adjacency included, is untouched.
 */
const LAMBDA_DOT = LAMBDA.replace(
  "prefix lam: $λ$ prec 30;",
  "notation lam {x: var} (b: tm x): tm = ($λ$:30) x ($.$:0) b;",
)
  .replace("· λ = $", "· λ = . $")
  .replace("delimiter $ ( ) = $;", "delimiter $ ( ) = . $;");

/** One-sort composition, with compound glue operands opted in. */
const COMPOSITION = `--| @syntax delimiter $ f g h P ( ) ∘ ≡ $
delimiter $ ( ) $;

provable sort ident;
sort fn;

term f: fn;
term g: fn;
term h: fn;

--| @syntax juxtaposed compound
term comp (s t: fn): fn;
infixl comp: $∘$ prec 50;

term same (s t: fn): ident;
infixl same: $≡$ prec 40;

term P (s: fn): ident;
`;

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics).toEqual([]);

  return new SurfaceLanguage(spec);
}

const group = language(GROUP);
const sequent = language(SEQUENT);
const lambda = language(LAMBDA);
const dotted = language(LAMBDA_DOT);
const composition = language(COMPOSITION);

const magnusReady = (async (): Promise<{
  language: SurfaceLanguage;
  spec: Spec;
}> => {
  const path = new URL("../specs/forallx-magnus.mm0", import.meta.url)
    .pathname;
  const { spec, diagnostics } = parseSpec(await readFile(path, "utf8"));

  expect(diagnostics).toEqual([]);

  return { language: new SurfaceLanguage(spec), spec };
})();

/** A term as a compact s-expression, coercion wrappers elided. */
function sexpr(term: Term, lang: SurfaceLanguage): string {
  if (term.kind === "variable") {
    return term.name;
  }

  if (term.args.length === 1 && lang.coercionNames.has(term.term)) {
    const inner = term.args[0];

    if (inner !== undefined) {
      return sexpr(inner, lang);
    }
  }

  if (term.args.length === 0) {
    return term.term;
  }

  const args = term.args.map((arg) => sexpr(arg, lang)).join(" ");

  return `(${term.term} ${args})`;
}

function parsed(
  lang: SurfaceLanguage,
  source: string,
  sort?: string,
): string {
  const result = lang.parse(source, sort === undefined ? {} : { sort });

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return sexpr(result.term, lang);
}

function refused(lang: SurfaceLanguage, source: string, sort?: string) {
  const result = lang.parse(source, sort === undefined ? {} : { sort });

  expect(result.ok, source).toBe(false);

  return result.ok ? [] : result.diagnostics;
}

describe("free-standing adjacency in the group spec", () => {
  test("adjacency is the product, at the product's precedence", () => {
    expect(parsed(group, "ab=c")).toBe("(eq (mul a b) c)");
    expect(parsed(group, "a*b=c")).toBe("(eq (mul a b) c)");
    expect(parsed(group, "ab", "g")).toBe("(mul a b)");
  });

  test("adjacency folds left, as the canonical infixl does", () => {
    expect(parsed(group, "abc", "g")).toBe("(mul (mul a b) c)");
    expect(parsed(group, "abc=c")).toBe("(eq (mul (mul a b) c) c)");
  });

  test("a parenthesized group is an operand on either side", () => {
    expect(parsed(group, "a(bc)", "g")).toBe("(mul a (mul b c))");
    expect(parsed(group, "(ab)c=a")).toBe("(eq (mul (mul a b) c) a)");
  });

  test("a tighter prefix keeps its operand from the glue", () => {
    // ⁻¹ at 90 outbinds adjacency at 70, exactly as it outbinds `*`.
    expect(parsed(group, "⁻¹ab=c")).toBe("(eq (mul (inv a) b) c)");
    expect(parsed(group, "⁻¹(ab)=c")).toBe("(eq (inv (mul a b)) c)");
  });

  test("variables glue like constants", () => {
    expect(parsed(group, "xy=z")).toBe("(eq (mul x y) z)");
    expect(parsed(group, "ax", "g")).toBe("(mul a x)");
  });

  test("adjacency does not manufacture an assertion", () => {
    // `ab` is a perfectly good g; it is still not an eqn, and the
    // complaint says so instead of surfacing a glue trial's debris.
    const diagnostics = refused(group, "ab");

    expect(diagnostics[0]?.id).toBe("term_not_sentence");
  });

  test("adjacency never reaches across a written operator", () => {
    // `=` is readable where a glue operand would have to start, so the
    // arc stands down and the parse fails on the real problem.
    const diagnostics = refused(group, "a==b");

    expect(diagnostics[0]?.id).not.toBe("term_not_sentence");
  });
});

describe("sequent contexts glue through a coercion", () => {
  test("adjacent formulas make a context, spelled or unspelled", () => {
    expect(parsed(sequent, "P Q ⊢ R")).toBe("(entails (cat P Q) R)");
    expect(parsed(sequent, "P, Q ⊢ R")).toBe("(entails (cat P Q) R)");
    expect(parsed(sequent, "P ⊢ Q")).toBe("(entails P Q)");
  });

  test("the wff connectives outbind the context comma either way", () => {
    // ∧ at 35 over `,` at 20: a conjunction is one context entry whether
    // it stands first or last, exactly as it would with the comma written.
    expect(parsed(sequent, "P ∧ Q R ⊢ R")).toBe(
      "(entails (cat (and P Q) R) R)",
    );
    expect(parsed(sequent, "P Q ∧ R ⊢ P")).toBe(
      "(entails (cat P (and Q R)) P)",
    );
  });

  test("a glued context is still not a judgement", () => {
    // `P Q` glues happily at ctx; without a turnstile there is no jdg,
    // and the complaint is about the sort, not about the gluing.
    const diagnostics = refused(sequent, "P Q");

    expect(diagnostics[0]?.id).toBe("term_not_sentence");
  });

  test("sequent display round-trips through the glued form", () => {
    // Dense, but every one reparses to its own tree: the connective's
    // precedence reassembles `P∧Q` before the arc can glue, on either
    // side of the invisible comma.
    const shown = (source: string): string => {
      const result = sequent.parse(source);

      if (!result.ok) {
        throw new Error(`Expected '${source}' to parse.`);
      }

      return printTerm(sequent, result.term, "display");
    };

    expect(shown("P Q ⊢ R")).toBe("PQ⊢R");
    expect(shown("P ∧ Q R ⊢ R")).toBe("P∧QR⊢R");
    expect(shown("P Q ∧ R ⊢ P")).toBe("PQ∧R⊢P");

    for (const source of ["P Q ⊢ R", "P ∧ Q R ⊢ R", "P Q ∧ R ⊢ P"]) {
      const result = sequent.parse(source);

      expect(result.ok, source).toBe(true);

      if (result.ok) {
        const shown = printTerm(sequent, result.term, "display");
        const reparsed = sequent.parse(shown);

        expect(reparsed.ok, shown).toBe(true);

        if (reparsed.ok) {
          expect(printTerm(sequent, reparsed.term, "display")).toBe(shown);
          expect(sexpr(reparsed.term, sequent)).toBe(
            sexpr(result.term, sequent),
          );
        }
      }
    }
  });
});

describe("lambda calculus: application is adjacency", () => {
  test("application glues left, combinators and variables alike", () => {
    expect(parsed(lambda, "xy", "tm")).toBe("(ap x y)");
    expect(parsed(lambda, "xyz", "tm")).toBe("(ap (ap x y) z)");
    expect(parsed(lambda, "SKK", "tm")).toBe("(ap (ap S K) K)");
    expect(parsed(lambda, "x·y", "tm")).toBe("(ap x y)");
  });

  test("an abstraction's body extends as far right as it can", () => {
    // λ at 30 under application at 100: the arc keeps gluing inside the
    // body, so `λx xy` is λx.(x y), the textbook default.
    expect(parsed(lambda, "λx xy", "tm")).toBe("(lam x (ap x y))");
    expect(parsed(lambda, "λxλy xy", "tm")).toBe("(lam x (lam y (ap x y)))");
  });

  test("applying an abstraction takes the parentheses the books write", () => {
    expect(parsed(lambda, "(λx x)y", "tm")).toBe("(ap (lam x x) y)");
    // The chain continues past a parenthesized link, still folding left.
    expect(parsed(lambda, "x(λy y)z", "tm")).toBe("(ap (ap x (lam y y)) z)");
    expect(parsed(lambda, "(λx xx)(λx xx)", "tm")).toBe(
      "(ap (lam x (ap x x)) (lam x (ap x x)))",
    );
    // Unparenthesized, the λ binds too loosely for the right-hand slot;
    // the arc declines, and the abstraction is trailing input.
    expect(lambda.parse("x λy y", { sort: "tm" }).ok).toBe(false);
  });

  test("application outbinds the equality judgement", () => {
    expect(parsed(lambda, "Kxy = x")).toBe("(equal (ap (ap K x) y) x)");
    expect(parsed(lambda, "(λx x)y = y")).toBe("(equal (ap (lam x x) y) y)");
  });

  test("display parenthesizes a loose prefix instead of losing it", () => {
    const shown = (source: string): string => {
      const result = lambda.parse(source, { sort: "tm" });

      if (!result.ok) {
        throw new Error(`Expected '${source}' to parse.`);
      }

      return printTerm(lambda, result.term, "display");
    };

    // Bare `λxxy` would reparse with `y` swallowed into the body: the
    // printer sees λ's precedence fall below the application slot and
    // brackets the abstraction, exactly as the writer must.
    expect(shown("(λx x)y")).toBe("(λxx)·y");
    expect(shown("λx xy")).toBe("λxxy");
    expect(shown("SKK")).toBe("SKK");

    for (const source of [
      "xy",
      "xyz",
      "SKK",
      "λx xy",
      "(λx x)y",
      "x(λy y)",
      "x(λy y)z",
    ]) {
      const result = lambda.parse(source, { sort: "tm" });

      expect(result.ok, source).toBe(true);

      if (result.ok) {
        const printed = printTerm(lambda, result.term, "display");
        const reparsed = lambda.parse(printed, { sort: "tm" });

        expect(reparsed.ok, printed).toBe(true);

        if (reparsed.ok) {
          expect(printTerm(lambda, reparsed.term, "display")).toBe(printed);
          expect(sexpr(reparsed.term, lambda)).toBe(
            sexpr(result.term, lambda),
          );
        }
      }
    }
  });
});

describe("a dotted binder is one notation swap", () => {
  test("the general notation parses, and the dot is required", () => {
    expect(parsed(dotted, "λx.xy", "tm")).toBe("(lam x (ap x y))");
    expect(parsed(dotted, "λx.λy.xy", "tm")).toBe("(lam x (lam y (ap x y)))");
    expect(parsed(dotted, "(λx.x)y", "tm")).toBe("(ap (lam x x) y)");
    expect(parsed(dotted, "x(λy.y)z", "tm")).toBe("(ap (ap x (lam y y)) z)");

    const bare = dotted.parse("λx xy", { sort: "tm" });

    expect(bare.ok).toBe(false);

    if (!bare.ok) {
      expect(bare.diagnostics[0]?.id).toBe("expected_bracket");
    }
  });

  test("display writes the dot, and still brackets a loose binder", () => {
    const shown = (source: string): string => {
      const result = dotted.parse(source, { sort: "tm" });

      if (!result.ok) {
        throw new Error(`Expected '${source}' to parse.`);
      }

      return printTerm(dotted, result.term, "display");
    };

    expect(shown("λx.xy")).toBe("λx.xy");
    // The general notation's head precedence (30) feeds the same slot
    // check the prefix spelling did, so an applied abstraction keeps its
    // brackets rather than swallowing the operand into the body.
    expect(shown("(λx.x)y")).toBe("(λx.x)·y");
    expect(shown("x(λy.y)z")).toBe("x·(λy.y)·z");
  });
});

describe("adjacency in the composition spec", () => {
  test("composition glues free-standing, groups included", () => {
    expect(parsed(composition, "gf ≡ fg")).toBe(
      "(same (comp g f) (comp f g))",
    );
    expect(parsed(composition, "(gf)h ≡ g(fh)")).toBe(
      "(same (comp (comp g f) h) (comp g (comp f h)))",
    );
  });

  test("compound lets groups glue in argument position", () => {
    expect(parsed(composition, "P(f)(g)")).toBe("(P (comp f g))");
    expect(parsed(composition, "Pf(g)h")).toBe("(P (comp (comp f g) h))");
    expect(parsed(composition, "P(fg)")).toBe("(P (comp f g))");
  });
});

describe("sorts that must not glue", () => {
  test("two sentences stay two sentences", async () => {
    // Magnus has a seq combiner and nothing at wff: a stray second
    // formula is trailing input, not an invisible conjunction.
    const { language: magnus } = await magnusReady;
    const result = magnus.parse("AxFx Gx");

    expect(result.ok).toBe(false);
  });

  test("Magnus argument gluing is unchanged, and still token-only", async () => {
    const { language: magnus } = await magnusReady;
    const glued = magnus.parse("Rxy");

    expect(glued.ok).toBe(true);

    // seq is not compound: a second group after a parenthesized argument
    // is not another operand.
    expect(magnus.parse("F(x)(y)").ok).toBe(false);
  });

  test("the arc reaches Magnus seq positions the glue loop could not", async () => {
    const { language: magnus } = await magnusReady;
    const result = magnus.parse("F(x y)");

    expect(result.ok).toBe(true);

    if (result.ok) {
      const { language: lang } = await magnusReady;

      expect(sexpr(result.term, lang)).toBe("(F (scomma x y))");
    }
  });
});

describe("printing glued terms", () => {
  test("display glues what reparses, and falls back where it would not", () => {
    const shown = (source: string, sort?: string): string => {
      const result = group.parse(source, sort === undefined ? {} : { sort });

      if (!result.ok) {
        throw new Error(`Expected '${source}' to parse.`);
      }

      return printTerm(group, result.term, "display");
    };

    expect(shown("ab=c")).toBe("ab=c");
    expect(shown("a*b=c")).toBe("ab=c");
    expect(shown("abc", "g")).toBe("abc");
    // Right-nested under an infixl combiner: gluing bare would reparse
    // left-folded, so the visible token returns with the nesting held.
    expect(shown("a(bc)", "g")).toBe("a*(bc)");
    // A tighter prefix glues whole: `⁻¹a` rebinds identically, since the
    // arc at 70 cannot reach into an operand parsed at 90.
    expect(shown("⁻¹ab=c")).toBe("⁻¹ab=c");
  });

  test("the display form is itself legal input, and stable", () => {
    for (const [source, sort] of [
      ["ab=c", undefined],
      ["abc=c", undefined],
      ["a(bc)=c", undefined],
      ["⁻¹ab=c", undefined],
      ["xy=z", undefined],
      ["a(bc)", "g"],
    ] as const) {
      const result = group.parse(source, sort === undefined ? {} : { sort });

      expect(result.ok, source).toBe(true);

      if (result.ok) {
        const shown = printTerm(group, result.term, "display");
        const reparsed = group.parse(
          shown,
          sort === undefined ? {} : { sort },
        );

        expect(reparsed.ok, shown).toBe(true);

        if (reparsed.ok) {
          expect(printTerm(group, reparsed.term, "display")).toBe(shown);
          expect(sexpr(reparsed.term, group)).toBe(sexpr(result.term, group));
        }
      }
    }
  });

  test("engine mode writes the operator out, and round-trips", () => {
    const result = group.parse("ab=c");

    expect(result.ok).toBe(true);

    if (result.ok) {
      const emitted = printTerm(group, result.term, "engine");

      expect(emitted).toBe("((a * b) = c)");

      const reparsed = group.parse(emitted, { mode: "engine" });

      expect(reparsed.ok, emitted).toBe(true);

      if (reparsed.ok) {
        expect(printTerm(group, reparsed.term, "engine")).toBe(emitted);
      }
    }
  });

  test("composition displays glued through application and adjacency", () => {
    const result = composition.parse("P(f)(g)");

    expect(result.ok).toBe(true);

    if (result.ok) {
      expect(printTerm(composition, result.term, "display")).toBe("Pfg");
    }
  });
});
