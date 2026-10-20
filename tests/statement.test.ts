import { describe, expect, test } from "bun:test";
import type { AssertStatement, DefStatement, Term } from "../src/index";
import {
  binderShadows,
  parseSpec,
  parseStatement,
  SurfaceLanguage,
  statementScope,
} from "../src/index";
import { corpusFiles, corpusSource } from "./helpers/mm0-corpus";

/**
 * Reading an assertion's own formulas in its own scope, and the lint that
 * says which of its binders push a meaning of the language aside.
 */

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

function assertion(lang: SurfaceLanguage, name: string): AssertStatement {
  for (const statement of lang.spec.statements) {
    if (
      (statement.kind === "axiom" || statement.kind === "theorem") &&
      statement.name === name
    ) {
      return statement;
    }
  }

  throw new Error(`no assertion ${name}`);
}

function shape(term: Term): string {
  return term.kind === "variable"
    ? term.name
    : term.args.length === 0
      ? term.term
      : `(${term.term} ${term.args.map(shape).join(" ")})`;
}

const PROP = `provable sort wff;
--| @vars x y
sort var;
term imp (a b: wff): wff;
infixr imp: $->$ prec 20;
term a: wff;
`;

describe("statementScope", () => {
  test("binds each named sort binder, and no hypothesis or anonymous one", () => {
    const lang = language(
      `${PROP}axiom ax {x: var} (p q: wff) (h: $ p $) (_: wff): $ q $;`,
    );

    expect([...statementScope(assertion(lang, "ax"))]).toEqual([
      ["x", "var"],
      ["p", "wff"],
      ["q", "wff"],
    ]);
  });

  test("a def's dot-dummies are in its scope", () => {
    const lang = language(
      `${PROP}term all {x: var} (p: wff x): wff;\ndef some {.y: var} (p: wff): wff = $ all y p $;`,
    );
    const def = lang.spec.statements.find(
      (statement): statement is DefStatement =>
        statement.kind === "def" && statement.name === "some",
    );

    expect(def).toBeDefined();
    expect(def && [...statementScope(def)]).toEqual([
      ["y", "var"],
      ["p", "wff"],
    ]);
  });
});

describe("parseStatement", () => {
  test("reads every formula in the statement's scope, in citation order", () => {
    const lang = language(
      `${PROP}axiom mp (a b: wff) (h: $ b $): $ a -> b $ > wff > $ a $ > $ b $;`,
    );
    const reading = parseStatement(lang, assertion(lang, "mp"));

    // The binder `a` shadows the term `a`: inside mp it is a variable.
    expect(
      reading.hypotheses.map(({ result }) =>
        result.ok ? shape(result.term) : "refused",
      ),
    ).toEqual(["b", "(imp a b)", "a"]);
    expect(
      reading.hypotheses.map(({ formula }) => formula.text.trim()),
    ).toEqual(["b", "a -> b", "a"]);
    expect(
      reading.conclusion.result.ok && reading.conclusion.result.term,
    ).toMatchObject({ kind: "variable", name: "b" });
    expect(reading.scope.get("a")).toBe("wff");
  });

  test("reads at the first provable sort that takes a formula", () => {
    const lang = language(
      `provable sort wff;\nprovable sort jdg;\nterm t: wff;\nterm j: jdg;\naxiom both: $ t $ > $ j $;`,
    );
    const reading = parseStatement(lang, assertion(lang, "both"));

    expect(reading.hypotheses[0]?.result).toMatchObject({
      ok: true,
      term: { sort: "wff" },
    });
    expect(reading.conclusion.result).toMatchObject({
      ok: true,
      term: { sort: "jdg" },
    });
  });

  test("a named sort refuses a formula of any other", () => {
    const lang = language(
      `provable sort wff;\nprovable sort jdg;\nterm t: wff;\nterm j: jdg;\naxiom both: $ t $ > $ j $;`,
    );
    const reading = parseStatement(lang, assertion(lang, "both"), {
      sort: "jdg",
    });

    expect(reading.hypotheses[0]?.result.ok).toBe(false);
    expect(reading.conclusion.result.ok).toBe(true);
  });

  test("reads every assertion in the MM0 corpus", () => {
    const failures: string[] = [];

    for (const name of corpusFiles()) {
      const lang = new SurfaceLanguage(parseSpec(corpusSource(name)).spec);

      for (const statement of lang.spec.statements) {
        if (statement.kind !== "axiom" && statement.kind !== "theorem") {
          continue;
        }

        const reading = parseStatement(lang, statement);

        for (const { formula, result } of [
          ...reading.hypotheses,
          reading.conclusion,
        ]) {
          if (!result.ok) {
            failures.push(
              `${name} ${statement.name}: ${formula.text.trim()}`,
            );
          }
        }
      }
    }

    expect(failures).toEqual([]);
  });
});

describe("binderShadows", () => {
  const lang = language(`${PROP}--| @vars c
sort name;
--| @syntax elab $ IF $ => $ -> $ input-only
term F (n: name): wff;
`);

  test("says what each binder pushes aside, and nothing for the rest", () => {
    const shadows = binderShadows(
      lang,
      new Map([
        ["->", "wff"],
        ["IF", "wff"],
        ["a", "wff"],
        ["F", "wff"],
        ["c", "var"],
        ["x", "var"],
        ["q", "wff"],
      ]),
    );

    expect(shadows).toEqual([
      { kind: "notation", name: "->", sort: "wff" },
      { kind: "notation", name: "IF", sort: "wff" },
      { kind: "term", name: "a", sort: "wff" },
      { kind: "term", name: "F", sort: "wff" },
      { displacedSort: "name", kind: "variable", name: "c", sort: "var" },
    ]);
  });

  test("a binder of a variable's own sort displaces nothing", () => {
    expect(binderShadows(lang, new Map([["x", "var"]]))).toEqual([]);
  });
});
