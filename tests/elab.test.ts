import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { Term } from "../src/index";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";

/**
 * Stage-4 coverage: the pre-2019 forallx (Magnus) spec — juxtaposed
 * variadic atoms as pure data — and the token-elaboration layer's two
 * flagship quantifier surface forms, Quine's `(x)Fx` and Bergmann's
 * `(∀x)Fx`, in both directions.
 *
 * A finding worth keeping, discovered while building this: juxtaposed
 * application can NOT be a blind token elaboration — `AxFx` would be eaten
 * (`A` captured as a predicate before anything knows it is a quantifier
 * here). Only the parser's ordered backtracking can decide, exactly as
 * Carnap's ordered alternatives do — so juxtaposition is a parser
 * behavior, declared on the sequence combiner (`@syntax juxtaposed` on
 * scomma: adjacency at seq denotes it), and the elab layer keeps the
 * patterns that really are local.
 */

async function loadMagnus(): Promise<SurfaceLanguage> {
  const path = new URL("../specs/forallx-magnus.mm0", import.meta.url)
    .pathname;
  const { spec, diagnostics } = parseSpec(await readFile(path, "utf8"));

  expect(diagnostics).toEqual([]);

  return new SurfaceLanguage(spec);
}

const magnusReady = loadMagnus();

function sexpr(term: Term): string {
  if (term.kind === "variable") {
    return term.name;
  }

  if (term.args.length === 1 && ["v2t", "n2t", "t2s"].includes(term.term)) {
    const inner = term.args[0];

    if (inner !== undefined) {
      return sexpr(inner);
    }
  }

  if (term.args.length === 0) {
    return term.term;
  }

  return `(${term.term} ${term.args.map(sexpr).join(" ")})`;
}

async function magnus(source: string): Promise<string> {
  const language = await magnusReady;
  const result = language.parse(source);

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return sexpr(result.term);
}

describe("forallx Magnus: juxtaposed atoms", () => {
  test("predicates glue their arguments straight on", async () => {
    expect(await magnus("Fx -> Gx")).toBe("(imp (F x) (G x))");
    expect(await magnus("Rxy")).toBe("(R (scomma x y))");
    expect(await magnus("Rabc")).toBe("(R (scomma (scomma a b) c))");
  });

  test("a bare capital is a sentence letter — the elided sequence", async () => {
    expect(await magnus("P -> Q")).toBe("(imp (P snil) (Q snil))");
  });

  test("AxFx is a quantifier; Axy is the predicate A", async () => {
    // The ambiguity Carnap resolves by ordered alternatives, and this
    // parser by trying the notation reading first: a variable then a
    // formula makes A a quantifier; two terms make it a predicate.
    expect(await magnus("AxFx")).toBe("(all x (F x))");
    expect(await magnus("Axy")).toBe("(A (scomma x y))");
    expect(await magnus("ExAyRxy")).toBe("(ex x (all y (R (scomma x y))))");
  });

  test("open formulas are legal here", async () => {
    expect(await magnus("Fx")).toBe("(F x)");
  });

  test("identity and mixed terms", async () => {
    expect(await magnus("Fxa /\\ a = b")).toBe(
      "(and (F (scomma x a)) (ideq a b))",
    );
  });

  test("juxtaposed atoms display back without parentheses", async () => {
    const language = await magnusReady;

    for (const source of ["Rxy", "AxFx -> Gb", "Ax(Fx -> Gx)"]) {
      const parsed = language.parse(source);

      expect(parsed.ok, source).toBe(true);

      if (parsed.ok) {
        const shown = printTerm(language, parsed.term, "display");
        const again = language.parse(shown);

        expect(again.ok, shown).toBe(true);

        if (again.ok) {
          expect(sexpr(again.term)).toBe(sexpr(parsed.term));
        }
      }
    }

    const parsed = language.parse("Rxy");

    if (parsed.ok) {
      expect(printTerm(language, parsed.term, "display")).toBe("Rxy");
    }
  });
});

describe("quantifier surface forms via the elab layer", () => {
  /** A Magnus-flavored mini theory plus one elab rule per test. */
  const BASE = `
--| @syntax delimiter $ F G H x y z a b c $
--| @syntax delimiter $ ( ) , -> ∀ ∃ $
delimiter $ ( ) , $;
provable sort wff;
--| @vars x y z
sort var;
--| @vars a b c
sort name;
sort tm;
sort seq;
term v2t (x: var): tm;
coercion v2t: var > tm;
term n2t (a: name): tm;
coercion n2t: name > tm;
term t2s (t: tm): seq;
coercion t2s: tm > seq;
--| @syntax elided
term snil: seq;
--| @syntax juxtaposed
term scomma (s t: seq): seq;
infixl scomma: $,$ prec 10;
term F (s: seq): wff;
term G (s: seq): wff;
term H (s: seq): wff;
term imp (p q: wff): wff;
infixr imp: $->$ prec 30;
term all {x: var} (p: wff x): wff;
prefix all: $∀$ prec 50;
term ex {x: var} (p: wff x): wff;
prefix ex: $∃$ prec 50;
`;

  function language(rules: string): SurfaceLanguage {
    const { spec, diagnostics } = parseSpec(`${rules}\n${BASE}`);

    expect(diagnostics).toEqual([]);

    return new SurfaceLanguage(spec);
  }

  test("Quine: (x)Fx reads and prints as the bare-parens universal", () => {
    const quine = language("--| @syntax elab $ ( ?x:var ) $ => $ ∀ ?x $");
    const parsed = quine.parse("(x)(y)Gxy");

    expect(parsed.ok).toBe(true);

    if (parsed.ok) {
      expect(sexpr(parsed.term)).toBe("(all x (all y (G (scomma x y))))");
      expect(printTerm(quine, parsed.term, "display")).toBe("(x)(y)Gxy");
    }

    // Ordinary grouping is untouched: the capture wants a variable.
    const grouped = quine.parse("(Fa -> Fb)");

    expect(grouped.ok).toBe(true);
  });

  test("Bergmann: (∀x) is accepted and restored", () => {
    const bergmann = language(
      [
        "--| @syntax elab $ ( ∀ ?x:var ) $ => $ ∀ ?x $",
        "--| @syntax elab $ ( ∃ ?x:var ) $ => $ ∃ ?x $",
      ].join("\n"),
    );
    const parsed = bergmann.parse("(∀x)(∃y)Gxy");

    expect(parsed.ok).toBe(true);

    if (parsed.ok) {
      expect(sexpr(parsed.term)).toBe("(all x (ex y (G (scomma x y))))");
      expect(printTerm(bergmann, parsed.term, "display")).toBe("(∀x)(∃y)Gxy");
    }
  });

  test("diagnostics point at the original text, not the elaborated text", () => {
    const quine = language("--| @syntax elab $ ( ?x:var ) $ => $ ∀ ?x $");
    // The `#` sits at offset 6 of the source; elaborating `(x)` to `∀ x`
    // shifts everything, and the origin map must shift it back.
    const failed = quine.parse("(x)Fx #");

    expect(failed.ok).toBe(false);

    if (!failed.ok) {
      expect(failed.diagnostics[0]?.span.start).toBe(6);
    }
  });
});
