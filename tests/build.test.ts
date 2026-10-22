import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Term } from "../src/index";
import {
  freeVariables,
  parseSpec,
  printTerm,
  SurfaceLanguage,
  substitute,
  TermBuildError,
} from "../src/index";
import { seeded, termGenerator } from "./helpers/terms";

/**
 * **A built term is the one the parser would have read.** `lang.app`
 * supplies the return sort, the coercions and the binding flags, so a
 * caller writes only constructors and leaves: rebuilding every generated
 * term from its constructors and variables gives it back exactly. Then
 * the refusals, the pools, and the two tree operations.
 */

function file(path: string): string {
  return readFileSync(new URL(path, import.meta.url).pathname, "utf8");
}

function language(source: string): SurfaceLanguage {
  return new SurfaceLanguage(parseSpec(source).spec);
}

const SOURCES: readonly (readonly [string, string])[] = [
  ["carnap-prop", file("../specs/carnap-prop.mm0")],
  ["forallx-calgary-2019", file("../specs/forallx-calgary-2019.mm0")],
  ["forallx-magnus", file("../specs/forallx-magnus.mm0")],
  ["signed rows", file("./fixtures/signed-rows.mm0")],
  ["forallx-ubc", file("./fixtures/carnap/forallx-ubc.mm0")],
  ["open-logic-tableaux", file("./fixtures/carnap/open-logic-tableaux.mm0")],
];

const calgary = language(file("../specs/forallx-calgary-2019.mm0"));
const ubc = language(file("./fixtures/carnap/forallx-ubc.mm0"));

/** `term` rebuilt from its constructors and variables alone. */
function rebuilt(lang: SurfaceLanguage, term: Term): Term {
  const bare = lang.uncoerced(term);

  return bare.kind === "variable"
    ? lang.variable(bare.name, bare.sort)
    : lang.app(
        bare.term,
        bare.args.map((arg) => rebuilt(lang, arg)),
      );
}

describe("lang.app over generated terms", () => {
  for (const [name, source] of SOURCES) {
    test(`${name}: rebuilding a term gives it back`, () => {
      const lang = language(source);
      const sort = lang.provableSort;

      if (sort === null) {
        throw new Error(`${name} has no provable sort`);
      }

      for (let seed = 1; seed <= 40; seed += 1) {
        const term = termGenerator(lang, seeded(seed))(sort, 4);

        if (term !== null) {
          expect({
            seed,
            term: lang.coerceTerm(rebuilt(lang, term), sort),
          }).toEqual({ seed, term });
        }
      }
    });
  }
});

describe("lang.app", () => {
  const x = calgary.variable("x");
  const a = calgary.app("a", [calgary.app("snil", [])]);

  test("coerces each argument to its binder's sort", () => {
    const built = calgary.app("F", [x]);

    expect(built.args[0]).toMatchObject({
      args: [{ args: [x], term: "v2t" }],
      sort: "seq",
      term: "t2s",
    });
    expect(printTerm(calgary, built, "display")).toBe("F(x)");
  });

  test("marks a variable filling a bound binder as binding", () => {
    const built = calgary.app("all", [x, calgary.app("F", [x])]);

    expect(built.args[0]).toEqual({ ...x, binder: true });
    expect(printTerm(calgary, built, "display")).toBe("∀xF(x)");
  });

  test("clears the flag on a variable in a regular slot", () => {
    const built = calgary.app("F", [{ ...x, binder: true }]);

    expect(calgary.uncoerced(built.args[0] as Term)).toEqual(x);
  });

  test("refuses what the parser could not have read", () => {
    expect(() => calgary.app("nonesuch", [])).toThrow(TermBuildError);
    expect(() => calgary.app("F", [])).toThrow("F takes 1 argument, not 0.");
    expect(() => calgary.app("all", [a, calgary.app("F", [x])])).toThrow(
      TermBuildError,
    );
    expect(() => calgary.app("not", [x])).toThrow(TermBuildError);
  });
});

describe("pools", () => {
  test("sortOfName and variable read a name's sort from its pool", () => {
    expect(ubc.sortOfName("x")).toBe("var");
    expect(ubc.sortOfName("a1")).toBe("name");
    expect(ubc.sortOfName("F")).toBeNull();
    expect(ubc.variable("a1").sort).toBe("name");
    expect(() => ubc.variable("F")).toThrow(TermBuildError);
  });

  test("freshName takes the sort's own pool first", () => {
    expect(ubc.freshName("name", new Set(["a", "b"]))).toMatchObject({
      kind: "variable",
      name: "c",
      sort: "name",
    });
  });

  test("freshName coerces a pool token into a sort with none", () => {
    expect(ubc.freshName("tm", new Set(["x"]))).toMatchObject({
      args: [{ kind: "variable", name: "y", sort: "var" }],
      sort: "tm",
      term: "v2t",
    });
  });

  test("freshName is null once every pool is spent", () => {
    expect(calgary.freshName("var", new Set("stuvwxyz"))).toBeNull();
  });
});

describe("tree operations", () => {
  const read = (text: string): Term => {
    const parsed = calgary.parse(text, { lints: false });

    if (!parsed.ok) {
      throw new Error(`${text} does not read`);
    }

    return parsed.term;
  };

  test("freeVariables leaves out bound and binding occurrences", () => {
    expect([...freeVariables(read("∀x (F(x) ∧ G(y))"))]).toEqual(["y"]);
    expect([...freeVariables(read("F(x) ∧ ∀x G(x)"))]).toEqual(["x"]);
  });

  test("substitute replaces a variable and keeps a binding flag", () => {
    const term = read("∀x F(x)");
    const z = calgary.variable("z");
    const out = substitute(term, new Map([["x", z]]));

    expect(printTerm(calgary, out, "display")).toBe("∀zF(z)");
    expect(out.kind === "app" && out.args[0]).toMatchObject({ binder: true });
  });
});
