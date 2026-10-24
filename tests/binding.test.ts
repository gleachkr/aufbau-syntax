import { describe, expect, test } from "bun:test";
import type { Term } from "../src/index";
import {
  bindingSites,
  freeVariables,
  parseSpec,
  printTerm,
  SurfaceLanguage,
  substitute,
  walkTerm,
} from "../src/index";

/**
 * Which occurrences a term binds, read as mm0.md reads it: a `{x}` binder
 * binds only when the return sort does not depend on x, and then in exactly
 * the arguments whose types depend on x — not "the arguments after it".
 * `foo` and `v` pass x through free; `sb` binds x in `p` but not in `t`,
 * which comes after the binder and does not depend on it.
 */

const THEORY = `--| @vars x y
sort var;
sort tm;
provable sort wff;
delimiter $ ( ) $;
term vt (x: var): tm;
coercion vt: var > tm;
term F (t: tm): wff;
term G (t: tm): wff;
term and (p q: wff): wff;
infixl and: $&$ prec 20;
term all {x: var} (p: wff x): wff;
prefix all: $A$ prec 40;
term ex {x: var} (p: wff x): wff;
prefix ex: $E$ prec 40;
term foo {x: var} (p: wff x): wff x;
term v {x: var}: tm x;
term sb {x: var} (t: tm) (p: wff x): wff;
`;

function language(lints: readonly string[] = []): SurfaceLanguage {
  const source = `${lints.map((lint) => `--| @syntax lint ${lint}\n`).join("")}${THEORY}`;
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics).toEqual([]);

  return new SurfaceLanguage(spec);
}

const plain = language();

function engine(text: string): Term {
  const result = plain.parse(text, { mode: "engine" });

  if (!result.ok) {
    throw new Error(`${text}: ${result.diagnostics[0]?.message}`);
  }

  return result.term;
}

describe("a binder binds by dependency", () => {
  test("the spec records the return dependencies and the bindings", () => {
    const terms = plain.spec.terms;

    expect(terms.get("all")?.bindings).toEqual([{ binder: 0, scope: [1] }]);
    expect(terms.get("sb")?.bindings).toEqual([{ binder: 0, scope: [2] }]);
    expect(terms.get("foo")?.returnDependencies).toEqual(["x"]);
    expect(terms.get("foo")?.bindings).toEqual([]);
    expect(terms.get("v")?.bindings).toEqual([]);
  });

  test("x passes through foo and v free", () => {
    for (const text of ["foo x (F x)", "F (v x)"]) {
      const term = engine(text);

      expect([...freeVariables(term)]).toEqual(["x"]);
      expect(bindingSites(term).every((site) => site.binder === null)).toBe(
        true,
      );
    }
  });

  test("a pass-through slot holds a variable, but not a binding one", () => {
    const term = engine("foo x (F x)");

    expect(term.kind === "app" && term.args[0]).toMatchObject({
      binder: false,
      kind: "variable",
    });
    expect(() => plain.app("foo", [engine("F x"), engine("F x")])).toThrow();
  });

  test("substitution replaces a passed-through x", () => {
    const term = engine("F (v x)");
    const replaced = substitute(term, new Map([["x", plain.variable("y")]]));

    expect(printTerm(plain, replaced, "engine")).toBe("F (v y)");
  });

  test("sb binds x in p, not in the t that follows the binder", () => {
    const term = engine("sb x x (F x)");

    expect([...freeVariables(term)]).toEqual(["x"]);
    expect(bindingSites(term)).toEqual([
      { binder: null, path: [1, 0] },
      { binder: [0], path: [2, 0, 0] },
    ]);
  });

  test("walkTerm scopes the same way", () => {
    const bound: string[] = [];

    walkTerm(engine("sb x x (F x)"), (node, scope) => {
      if (node.kind === "variable" && !node.binder) {
        bound.push(scope.has(node.name) ? "bound" : "free");
      }
    });

    expect(bound).toEqual(["free", "bound"]);
  });

  test("the term builder marks only a binding slot as binding", () => {
    const x = plain.variable("x");
    const all = plain.app("all", [x, engine("F x")]);
    const foo = plain.app("foo", [{ ...x, binder: true }, engine("F x")]);

    expect(all.args[0]).toMatchObject({ binder: true });
    expect(foo.args[0]).toMatchObject({ binder: false });
    expect([...freeVariables(all)]).toEqual([]);
    expect([...freeVariables(foo)]).toEqual(["x"]);
  });
});

describe("bindable sorts", () => {
  const PASS_THROUGH = `--| @syntax lint closed-sentences
--| @vars x
sort var;
sort tm;
provable sort wff;
delimiter $ ( ) $;
term v {x: var}: tm x;
term F (t: tm): wff;
`;

  const read = (source: string) => {
    const { spec, diagnostics } = parseSpec(source);

    expect(diagnostics).toEqual([]);

    return new SurfaceLanguage(spec);
  };

  test("a sort only a binder that binds nothing takes is not bindable", () => {
    const lang = read(PASS_THROUGH);

    expect(lang.bindableSorts.has("var")).toBe(false);
    expect(lang.parse("F (v x)", { lints: true, mode: "engine" }).ok).toBe(
      true,
    );
  });

  test("one quantifier over it makes its free variables refusable", () => {
    const lang = read(`${PASS_THROUGH}term all {x: var} (p: wff x): wff;\n`);
    const result = lang.parse("F (v x)", { lints: true, mode: "engine" });

    expect(lang.bindableSorts.has("var")).toBe(true);
    expect(result.ok ? [] : result.diagnostics.map((d) => d.id)).toEqual([
      "free_variable",
    ]);
  });
});

describe("bindingSites", () => {
  test("links each occurrence to its quantifier, by printPieces paths", () => {
    const term = engine("all x (ex y (and (F x) (G y)))");

    expect(bindingSites(term)).toEqual([
      { binder: [0], path: [1, 1, 0, 0, 0] },
      { binder: [1, 0], path: [1, 1, 1, 0, 0] },
    ]);
  });

  test("a shadowed variable links to the innermost quantifier", () => {
    const term = engine("all x (and (F x) (all x (G x)))");

    expect(bindingSites(term)).toEqual([
      { binder: [0], path: [1, 0, 0, 0] },
      { binder: [1, 1, 0], path: [1, 1, 1, 0, 0] },
    ]);
  });

  test("lists free occurrences with no binder, and never a binding one", () => {
    expect(bindingSites(engine("all x (F y)"))).toEqual([
      { binder: null, path: [1, 0, 0] },
    ]);
  });
});

describe("the binder lints", () => {
  const ids = (lang: SurfaceLanguage, text: string): string[] => {
    const result = lang.parse(text);

    return result.ok
      ? []
      : result.diagnostics.map((d) => `${d.id}@${d.span.start}`);
  };

  test("are off unless the spec asks for them", () => {
    expect(ids(plain, "A x (F(x) & E x G(x))")).toEqual([]);
    expect(ids(plain, "A x F(y)")).toEqual([]);
  });

  test("distinct-binders refuses a quantifier inside one on the same variable, at the inner one", () => {
    const lang = language(["distinct-binders"]);

    expect(ids(lang, "A x (F(x) & E x G(x))")).toEqual([
      "rebound_variable@14",
    ]);
    expect(ids(lang, "A x E y (F(x) & G(y))")).toEqual([]);
    expect(ids(lang, "A x F(x) & E x G(x)")).toEqual([]);
    expect(ids(lang, "A x F(y)")).toEqual([]);
  });

  test("non-vacuous-binders refuses a quantifier that binds nothing, at its variable", () => {
    const lang = language(["non-vacuous-binders"]);

    expect(ids(lang, "A x F(y)")).toEqual(["vacuous_binder@2"]);
    expect(ids(lang, "A x E y F(x)")).toEqual(["vacuous_binder@6"]);
    expect(ids(lang, "A x (F(x) & E x G(x))")).toEqual([]);
    expect(ids(lang, "A x E y (F(x) & G(y))")).toEqual([]);
  });

  test("together, a re-bound variable leaves the outer quantifier vacuous too", () => {
    const lang = language(["distinct-binders", "non-vacuous-binders"]);

    expect(ids(lang, "A x E x F(x)").sort()).toEqual([
      "rebound_variable@6",
      "vacuous_binder@2",
    ]);
  });

  test("engine text is read without them", () => {
    const lang = language(["distinct-binders", "non-vacuous-binders"]);

    expect(lang.parse("all x (ex x (F y))", { mode: "engine" }).ok).toBe(
      true,
    );
  });
});
