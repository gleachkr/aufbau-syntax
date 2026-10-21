import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Term } from "../src/index";
import { abstractContext, parseSpec, SurfaceLanguage } from "../src/index";
import { CORPUS_DIR, shape } from "./helpers/mm0-corpus";

/**
 * The engine's `@abstract` walk with bare-name plugs, one behaviour each:
 * where the hole and the plugs meet, which positions are sites, and the
 * retry through defs (`applyAbstractBinding` in Aufbau's
 * `frontend/derived_bindings.zig`).
 */

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

const LANG = language(`delimiter $ ( ) $;
provable sort wff;
--| @vars x y
sort var;
--| @vars a b c
sort name;
sort tm;
term v2t (x: var): tm;
coercion v2t: var > tm;
term n2t (a: name): tm;
coercion n2t: name > tm;
term k0: tm;
term k1: tm;
term F (t: tm): wff;
term R (s t: tm): wff;
term and (p q: wff): wff;
term all {x: var} (p: wff x): wff;
def Fd (t: tm): wff = $ F t $;
`);

function read(text: string, sort = "wff"): Term {
  const result = LANG.parse(text, { mode: "engine", sort });

  if (!result.ok) {
    throw new Error(`${text}: ${result.diagnostics[0]?.message}`);
  }

  return result.term;
}

/** A variable of `sort` named `name`, as a binder's value is. */
function variable(name: string, sort: string): Term {
  return {
    binder: false,
    grouped: false,
    kind: "variable",
    name,
    sort,
    span: { end: 0, start: 0 },
  };
}

function context(
  left: string,
  right: string | undefined,
  plugs: readonly [Term, Term],
  hole = variable("x", "var"),
): string | null {
  const found = abstractContext(LANG, {
    hole,
    left: read(left),
    leftPlug: plugs[0],
    ...(right === undefined ? {} : { right: read(right) }),
    rightPlug: plugs[1],
  });

  return found === null ? null : shape(found);
}

const NAMES = [variable("a", "name"), variable("b", "name")] as const;

describe("the sort the hole and plugs meet at", () => {
  test("names and a variable meet at terms, under their coercions", () => {
    // `a` sits in a term as `n2t a`, and the hole goes in as `v2t x`.
    expect(context("F (n2t a)", "F (n2t b)", NAMES)).toBe("(F (v2t x))");
  });

  test("plugs of the hole's target sort are sites as they are", () => {
    const terms = [read("k0", "tm"), read("k1", "tm")] as const;

    expect(context("R k0 k1", "R k1 k1", terms)).toBe("(R (v2t x) k1)");
  });

  test("no sort all three reach is no context", () => {
    const wffs = [read("F k0"), read("F k1")] as const;

    expect(context("and (F k0) (F k0)", undefined, wffs)).toBeNull();
  });
});

describe("the walk", () => {
  test("a site on one side only is the plugs' business, not a site", () => {
    // Only where the left has `a` and the right `b`: the second `a` stays.
    expect(
      context(
        "and (F (n2t a)) (F (n2t a))",
        "and (F (n2t b)) (F (n2t a))",
        NAMES,
      ),
    ).toBe("(and (F (v2t x)) (F (n2t a)))");
  });

  test("the terms must otherwise agree", () => {
    expect(context("F (n2t a)", "R (n2t b) (n2t b)", NAMES)).toBeNull();
  });

  test("at least one site", () => {
    expect(context("F k0", "F k0", NAMES)).toBeNull();
  });

  test("a bound variable is kept where both sides have it", () => {
    expect(
      context(
        "all x (R (v2t x) (n2t a))",
        "all x (R (v2t x) (n2t b))",
        NAMES,
        variable("y", "var"),
      ),
    ).toBe("(all x (R (v2t x) (v2t y)))");
  });
});

describe("with the right side left open", () => {
  test("every site is the hole", () => {
    expect(context("and (F (n2t a)) (F (n2t a))", undefined, NAMES)).toBe(
      "(and (F (v2t x)) (F (v2t x)))",
    );
  });

  test("the right plug, where the left has it, stays", () => {
    expect(context("R (n2t a) (n2t b)", undefined, NAMES)).toBe(
      "(R (v2t x) (n2t b))",
    );
  });

  test("no site is no context", () => {
    expect(context("F (n2t b)", undefined, NAMES)).toBeNull();
  });
});

describe("the retry", () => {
  test("opens a def the two sides differ by", () => {
    // `Fd` and `F` differ as written; opened, they differ at the site only.
    expect(context("Fd (n2t a)", "F (n2t b)", NAMES)).toBe("(F (v2t x))");
  });
});

describe("the retry's normal forms", () => {
  const leibniz = language(readFileSync(`${CORPUS_DIR}/leibniz.mm0`, "utf8"));
  const real = (text: string): Term => {
    const result = leibniz.parse(text, {
      mode: "engine",
      scope: new Map(["a", "b", "c", "d"].map((name) => [name, "real"])),
      sort: "real",
    });

    if (!result.ok) {
      throw new Error(text);
    }

    return result.term;
  };
  const regular = (dependencies: string[] = []) => ({
    bound: false,
    dependencies,
    sort: "real",
  });
  const sites = {
    hole: { ...variable("x", "real") },
    // `[v | d] c` is `c` where `c` does not depend on `v` (`sb_irrel`).
    left: real("a + ([v | d] c)"),
    leftPlug: real("a"),
    right: real("b + c"),
    rightPlug: real("b"),
  };

  test("check a rewrite's dependencies with the statement's variables", () => {
    const free = new Map([
      ["a", regular()],
      ["b", regular()],
      ["c", regular()],
      ["d", regular()],
    ]);
    const dependent = new Map([...free, ["c", regular(["v"])]]);
    const found = abstractContext(leibniz, sites, { variables: free });

    expect(found === null ? null : shape(found)).toBe("(add x c)");
    expect(
      abstractContext(leibniz, sites, { variables: dependent }),
    ).toBeNull();
  });
});
