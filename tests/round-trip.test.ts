import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Spec, Term } from "../src/index";
import {
  parseSpec,
  printTerm,
  SurfaceLanguage,
  UnprintableTermError,
} from "../src/index";
import {
  corpusFiles,
  corpusFormulas,
  corpusSource,
} from "./helpers/mm0-corpus";
import { seeded, termGenerator } from "./helpers/terms";

/**
 * **Printing then parsing is the identity, and printing is always
 * defined.** For every well-sorted term — not only the ones some parse
 * happened to produce — the printed text parses, in the same mode, back to
 * that term. A printer that falls short of this is worse than one that
 * fails: a stored canonical formula that no longer reads is a grading
 * error found only when a student submits, and one that reads as a
 * *different* formula is not found at all.
 *
 * The terms are generated at random over every built-in spec, every MM0
 * corpus file, and a spec with multi-letter names and no letter
 * delimiters — the shape that once printed `∀x Cube(x)` as `∀xCube(x)`,
 * one chunk `xCube` to its own reader. A theory whose formulas are all
 * schematic (hilbert.mm0 has no closed terms) is built over the names its
 * own theorems bind, read back in that scope. Trees are compared with coercions
 * elided, since both readers re-derive those; lints are off, since they
 * are conventions about student input (a free variable is a perfectly
 * good term to print).
 */

/** Multi-letter names, no letter delimiters: the #352 shape. */
const NAMES_SPEC = `
--| @syntax delimiter $ ( ) , ∀ ∃ ¬ ∧ = $
--| @syntax brackets ( )
--| @syntax display drop-outer-parens
delimiter $ ( ) , $;
provable sort wff;
--| @vars x y z
sort var;
sort tm;
term v2t (x: var): tm;
coercion v2t: var > tm;
sort seq;
term t2s (t: tm): seq;
coercion t2s: tm > seq;
--| @syntax elided
term snil: seq;
term scomma (s t: seq): seq;
infixl scomma: $,$ prec 10;
term a (s: seq): tm;
term Cube (s: seq): wff;
term LeftOf (s: seq): wff;
term succ (s: seq): tm;
term eq (s t: tm): wff;
infixl eq: $=$ prec 60;
term not (p: wff): wff;
prefix not: $¬$ prec 50;
term and (p q: wff): wff;
infixl and: $∧$ prec 40;
term all {x: var} (p: wff x): wff;
notation all (x: var) (p: wff x): wff = ($∀$:50) x p;
term ex {x: var} (p: wff x): wff;
notation ex (x: var) (p: wff x): wff = ($∃$:50) x p;
`;

function specFile(name: string): string {
  return readFileSync(
    new URL(`../specs/${name}.mm0`, import.meta.url).pathname,
    "utf8",
  );
}

const SOURCES: readonly (readonly [string, string])[] = [
  ["carnap-prop", specFile("carnap-prop")],
  ["forallx-calgary-2019", specFile("forallx-calgary-2019")],
  ["forallx-magnus", specFile("forallx-magnus")],
  ["names without letter delimiters", NAMES_SPEC],
  ...corpusFiles().map((file) => [file, corpusSource(file)] as const),
];

/** Terms per source, and the deepest nesting tried. */
const TERMS = 120;
const DEPTH = 5;

/**
 * The names the file's theorems bind, each at its first sort: variables
 * to build schematic terms from, in a theory with no closed ones. A name
 * the language already claims — an `@vars` token, a declared term, a
 * notation token — is left out, since a scope shadows the lexicon and
 * the same text would then read two ways.
 */
function theoremScope(spec: Spec): Map<string, string> {
  const claimed = new Set<string>([
    ...spec.terms.keys(),
    ...[...spec.sorts.values()].flatMap((sort) => sort.vars),
    ...spec.notations.flatMap((notation) =>
      notation.form === "simple"
        ? [notation.token]
        : notation.literals.flatMap((literal) =>
            literal.kind === "constant" ? [literal.token] : [],
          ),
    ),
  ]);
  const scope = new Map<string, string>();

  for (const formula of corpusFormulas(spec)) {
    for (const [name, sort] of formula.scope) {
      if (!claimed.has(name) && !scope.has(name)) {
        scope.set(name, sort);
      }
    }
  }

  return scope;
}

/** The tree, coercions elided — what both readers agree a term is. */
function essence(lang: SurfaceLanguage, term: Term): string {
  if (
    term.kind === "app" &&
    term.args.length === 1 &&
    lang.coercionNames.has(term.term)
  ) {
    const inner = term.args[0];

    if (inner !== undefined) {
      return essence(lang, inner);
    }
  }

  if (term.kind === "variable") {
    return term.name;
  }

  return term.args.length === 0
    ? term.term
    : `(${term.term} ${term.args.map((arg) => essence(lang, arg)).join(" ")})`;
}

describe("print then parse is the identity", () => {
  for (const [name, source] of SOURCES) {
    const { spec, diagnostics } = parseSpec(source);

    // A refused spec builds no language; the corpus has none today.
    if (diagnostics.some((d) => d.severity === "error")) {
      continue;
    }

    test(name, () => {
      const lang = new SurfaceLanguage(spec);
      const scope = theoremScope(spec);
      const generate = termGenerator(lang, seeded(name.length), scope);
      const sorts = [...spec.sorts.keys()];
      const failures: string[] = [];

      let checked = 0;

      for (let i = 0; i < TERMS && sorts.length > 0; i += 1) {
        const sort = sorts[i % sorts.length] ?? "";
        const term = generate(sort, 1 + (i % DEPTH));

        if (term === null) {
          continue;
        }

        checked += 1;
        const expected = essence(lang, term);

        for (const mode of ["display", "engine"] as const) {
          const printed = printTerm(lang, term, mode);
          const read = lang.parse(printed, {
            lints: false,
            mode: mode === "display" ? "surface" : "engine",
            scope,
            sort,
          });
          const actual = read.ok
            ? essence(lang, read.term)
            : `✗ ${read.diagnostics[0]?.message}`;

          if (actual !== expected) {
            failures.push(
              `${mode}: ${expected}\n  printed ${JSON.stringify(printed)}\n  read    ${actual}`,
            );
          }
        }
      }

      // A theory that builds nothing would pass vacuously.
      expect(checked).toBeGreaterThan(TERMS / 4);
      expect(failures).toEqual([]);
    });
  }
});

describe("seams", () => {
  const lang = new SurfaceLanguage(parseSpec(NAMES_SPEC).spec);

  function display(source: string): string {
    const read = lang.parse(source);

    if (!read.ok) {
      throw new Error(`'${source}': ${read.diagnostics[0]?.message}`);
    }

    return printTerm(lang, read.term, "display");
  }

  test("a space only where the delimiters would not cut", () => {
    // `∀` and `(` delimit, so those seams stay tight; `x` against `Cube`
    // would be one chunk, so it gets its space.
    expect(display("∀x Cube(x)")).toBe("∀x Cube(x)");
    expect(display("∀x ∃y LeftOf(x, y)")).toBe("∀x∃y LeftOf(x,y)");
    expect(display("∀x (Cube(x) ∧ ¬Cube(x))")).toBe("∀x(Cube(x) ∧ ¬Cube(x))");
    expect(display("¬ Cube(a)")).toBe("¬Cube(a)");
  });
});

describe("an elided term outside its slot", () => {
  // `F(snil, b)`: well-sorted, but the reader only ever supplies `snil`
  // as a name's whole argument, so display text has no way to write it
  // anywhere else. Calgary cannot read `snil` back, and Magnus would glue
  // its letters into arguments — so display refuses, and engine text,
  // which spells it by name, carries it.
  for (const [name, source] of [
    ["forallx-calgary-2019", "F(a,b)"],
    ["forallx-magnus", "Fab"],
  ] as const) {
    test(name, () => {
      const lang = new SurfaceLanguage(parseSpec(specFile(name)).spec);
      const read = lang.parse(source);

      if (!read.ok || read.term.kind !== "app") {
        throw new Error(`'${source}' should read as an application`);
      }

      const [pair] = read.term.args;

      if (pair?.kind !== "app") {
        throw new Error("expected an argument sequence");
      }

      const snil: Term = { ...pair, term: "snil", args: [], sort: "seq" };
      const term: Term = {
        ...read.term,
        args: [{ ...pair, args: [snil, ...pair.args.slice(1)] }],
      };

      expect(() => printTerm(lang, term, "display")).toThrow(
        UnprintableTermError,
      );

      const engine = printTerm(lang, term, "engine");
      const back = lang.parse(engine, { mode: "engine" });

      expect(back.ok && essence(lang, back.term)).toBe(essence(lang, term));
    });
  }
});
