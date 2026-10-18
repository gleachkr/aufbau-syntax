import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import type { Spec, Term } from "../src/index";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";

/**
 * Display expectations transcribed from the incumbent
 * `formulaToDisplay`/`formulaToString` suites (carnap-server
 * `tests/first-order-syntax.test.ts`, "how a formula is shown to a
 * reader"), themselves taken from runs of the original Carnap. Two marked
 * deviations: `a != b` displays as `a ≠ b` through the `neq` def's own
 * canonical token, where Carnap unfolded it to `¬a=b`; and identity is
 * spaced, as every notation that changes sort is, where Carnap wrote
 * `a=b`.
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

async function term(source: string): Promise<{
  language: SurfaceLanguage;
  term: Term;
}> {
  const { language } = await calgaryReady;
  const result = language.parse(source);

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return { language, term: result.term };
}

async function display(source: string): Promise<string> {
  const { language, term: parsed } = await term(source);

  return printTerm(language, parsed, "display");
}

async function engine(source: string): Promise<string> {
  const { language, term: parsed } = await term(source);

  return printTerm(language, parsed, "engine");
}

async function propDisplay(source: string): Promise<string> {
  const { language } = await propReady;
  const result = language.parse(source);

  if (!result.ok) {
    throw new Error(`Expected '${source}' to parse.`);
  }

  return printTerm(language, result.term, "display");
}

describe("Calgary display", () => {
  test("connectives and quantifiers are logical symbols, not ascii", async () => {
    expect(await display("~~P")).toBe("¬¬P");
    expect(await display("P <-> Q")).toBe("P ↔ Q");
    expect(await display("AxEy~R(x,y)")).toBe("∀x∃y¬R(x,y)");
    expect(await display("⊥ \\/ ⊤")).toBe("⊥ ∨ ⊤");
  });

  test("every binary compound is parenthesized, except the outermost", async () => {
    expect(await display("P /\\ Q")).toBe("P ∧ Q");
    expect(await display("P /\\ Q \\/ R")).toBe("(P ∧ Q) ∨ R");
    expect(await display("AxF(x) -> G(a)")).toBe("∀xF(x) → G(a)");
    expect(await display("Ax(F(x) -> G(x))")).toBe("∀x(F(x) → G(x))");
    expect(await display("~(P /\\ Q)")).toBe("¬(P ∧ Q)");
  });

  test("a quantifier or a negation is written straight onto what follows", async () => {
    expect(await display("AxAyf(x,y) = f(y,x)")).toBe("∀x∀yf(x,y) = f(y,x)");
    expect(await display("ExEy~x = y")).toBe("∃x∃y¬x = y");
  });

  test("identity is spaced, as a sort-changing infix; inequality keeps its own sign", async () => {
    // Deviation from Carnap, which set identity tight: `=` takes terms to
    // a formula, and a notation that changes sort is spaced.
    expect(await display("a = b")).toBe("a = b");
    // Deviation from Carnap (which unfolded to ¬a=b): the neq def has a
    // canonical token of its own, and prints through it.
    expect(await display("a != b")).toBe("a ≠ b");
  });

  test("predicates keep their parentheses; a sentence letter has none", async () => {
    expect(await display("R(a,b)")).toBe("R(a,b)");
    expect(await display("P")).toBe("P");
    expect(await display("f(a) = b")).toBe("f(a) = b");
  });

  test("the display form is itself legal input, and stable", async () => {
    for (const source of [
      "P /\\ Q \\/ R",
      "Ax(F(x) -> G(x))",
      "~(P /\\ Q)",
      "AxAyf(x,y) = f(y,x)",
      "ExEy~x = y",
      "a != b",
      "Ex(F(x) /\\ x != a)",
      "P -> (Q -> R)",
      "⊥ \\/ ⊤",
    ]) {
      const { language } = await calgaryReady;
      const shown = await display(source);
      const reparsed = language.parse(shown);

      expect(reparsed.ok, shown).toBe(true);

      if (reparsed.ok) {
        expect(printTerm(language, reparsed.term, "display")).toBe(shown);
      }
    }
  });
});

describe("Calgary engine mode", () => {
  test("spaced, fully parenthesized, coercion-free, elision written out", async () => {
    expect(await engine("AxF(x)")).toBe("(∀ x (F (x)))");
    expect(await engine("P /\\ Q")).toBe("((P (snil)) ∧ (Q (snil)))");
    expect(await engine("~P")).toBe("(¬ (P (snil)))");
  });

  test("engine text re-parses to the same tree", async () => {
    for (const source of [
      "AxEy~R(x,y)",
      "(P /\\ Q) -> R",
      "AxAyf(x,y) = f(y,x)",
      "Ex(F(x) /\\ x != a)",
      "~(P \\/ Q) <-> (~P /\\ ~Q)",
      "⊥ \\/ ⊤",
    ]) {
      const { language, term: parsed } = await term(source);
      const emitted = printTerm(language, parsed, "engine");
      // Engine text is engine syntax, not surface idiom: it is read under
      // the theory's own delimiters (so `snil` stays one name where the
      // surface set would split it into four letters), and the surface
      // refusal conventions are switched off with it.
      const reparsed = language.parse(emitted, { mode: "engine" });

      expect(reparsed.ok, emitted).toBe(true);

      if (reparsed.ok) {
        expect(printTerm(language, reparsed.term, "engine")).toBe(emitted);
      }
    }
  });
});

describe("prop display", () => {
  test("ascii spellings, full parentheses kept", async () => {
    expect(await propDisplay("P /\\ Q")).toBe("(P /\\ Q)");
    expect(await propDisplay("~P")).toBe("~P");
    expect(await propDisplay("P /\\ Q \\/ R")).toBe("((P /\\ Q) \\/ R)");
    expect(await propDisplay("~(P -> Q)")).toBe("~(P -> Q)");
  });

  test("prop display round-trips", async () => {
    const { language } = await propReady;

    for (const source of ["P /\\ Q \\/ R", "~(P <-> Q) -> r"]) {
      const parsed = language.parse(source);

      expect(parsed.ok).toBe(true);

      if (parsed.ok) {
        const shown = printTerm(language, parsed.term, "display");
        const again = language.parse(shown);

        expect(again.ok, shown).toBe(true);

        if (again.ok) {
          expect(printTerm(language, again.term, "display")).toBe(shown);
        }
      }
    }
  });
});

describe("display where the sort changes", () => {
  const source = readFileSync(
    new URL("./fixtures/signed-rows.mm0", import.meta.url).pathname,
    "utf8",
  );

  function signed(text: string): SurfaceLanguage {
    const { spec, diagnostics } = parseSpec(text);

    expect(diagnostics).toEqual([]);

    return new SurfaceLanguage(spec);
  }

  const dropped = signed(source);
  const kept = signed(
    source.replace("--| @syntax display drop-outer-parens\n", ""),
  );

  function shown(language: SurfaceLanguage, text: string, sort: string) {
    const result = language.parse(text, { sort });

    if (!result.ok) {
      throw new Error(`Expected '${text}' to parse.`);
    }

    const printed = printTerm(language, result.term, "display");
    const reparsed = language.parse(printed, { sort });

    expect(reparsed.ok, printed).toBe(true);

    if (reparsed.ok) {
      expect(printTerm(language, reparsed.term, "display")).toBe(printed);
    }

    return printed;
  }

  test("a formula under a sign is outermost there, and the sign is spaced", () => {
    expect(shown(dropped, "𝕋 A ∧ B", "row")).toBe("𝕋 A ∧ B");
    expect(shown(dropped, "𝕋 (A ∧ B) → C", "row")).toBe("𝕋 (A ∧ B) → C");
    expect(shown(dropped, "1 @ A ∧ B", "row")).toBe("1 @ A ∧ B");
  });

  test("an operator of the formula's own sort keeps its operand's brackets", () => {
    expect(shown(dropped, "𝔽 ¬(A ∧ B)", "row")).toBe("𝔽 ¬(A ∧ B)");
  });

  test("a sign tighter than the connective keeps them too", () => {
    expect(shown(dropped, "■(A ∧ B)", "row")).toBe("■ (A ∧ B)");
  });

  test("a context's formulas are outermost through the coercion", () => {
    expect(shown(dropped, "𝕋 A ∧ B; 𝔽 C ⊢ 𝕋 A", "jdg")).toBe(
      "𝕋 A ∧ B; 𝔽 C ⊢ 𝕋 A",
    );
  });

  test("a one-sided delimiter hugs the side it breaks at", () => {
    // Every letter is a delimiter, so `R(a,b)` and `a•b` would read back
    // tight; the spacing is the declaration's, not the reader's need.
    expect(shown(dropped, "R(a,b) ∧ a•b = b", "wff")).toBe(
      "R(a, b) ∧ a •b = b",
    );
  });

  test("without drop-outer-parens every connective keeps its pair", () => {
    expect(shown(kept, "𝕋 A ∧ B", "row")).toBe("𝕋 (A ∧ B)");
    expect(shown(kept, "𝕋 A ∧ B; 𝔽 C ⊢ 𝕋 A", "jdg")).toBe(
      "𝕋 (A ∧ B); 𝔽 C ⊢ 𝕋 A",
    );
  });
});
