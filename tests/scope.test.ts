import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { Scope, Spec, Term } from "../src/index";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";

/**
 * A parse's binder scope: the enclosing theorem's binders, shadowing the
 * lexicon.
 *
 * Every case here is a collision — a binder name that the spec also spells
 * — because a binder that collides with nothing needs no scope to read
 * correctly. What the scope has to guarantee is that the *declaration*
 * loses: `theorem mp (a b: wff)` is about metavariables, and a lexicon that
 * has never heard of them must not quietly answer in their place.
 */

async function calgary(): Promise<{ language: SurfaceLanguage; spec: Spec }> {
  const path = new URL("../specs/forallx-calgary-2019.mm0", import.meta.url)
    .pathname;
  const { spec, diagnostics } = parseSpec(await readFile(path, "utf8"));

  expect(diagnostics).toEqual([]);

  return { language: new SurfaceLanguage(spec), spec };
}

const ready = calgary();

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

  return `(${term.term} ${term.args.map((arg) => sexpr(arg, coercions)).join(" ")})`;
}

async function read(
  source: string,
  scope: Scope = new Map(),
): Promise<string> {
  const { language, spec } = await ready;
  const result = language.parse(source, { scope });

  if (!result.ok) {
    throw new Error(
      `Expected '${source}' to parse: ${result.diagnostics[0]?.message}`,
    );
  }

  return sexpr(result.term, new Set(spec.coercions.map((c) => c.name)));
}

async function refusal(
  source: string,
  scope: Scope = new Map(),
): Promise<string> {
  const { language } = await ready;
  const result = language.parse(source, { scope });

  if (result.ok) {
    throw new Error(`Expected '${source}' to fail.`);
  }

  return result.diagnostics[0]?.id ?? "";
}

const wff = (...names: string[]): Scope =>
  new Map(names.map((name) => [name, "wff"]));

describe("a binder shadows the lexicon", () => {
  test("a sentence-letter collision reads as the metavariable", async () => {
    // The bug this exists for: `theorem mp (a b: wff)` stated with the
    // letters most textbooks use. Unscoped, `P` is the predicate letter
    // applied to the elided empty sequence, and the proof it belongs to
    // cannot be closed.
    expect(await read("P -> Q")).toBe("(imp (P snil) (Q snil))");
    expect(await read("P -> Q", wff("P", "Q"))).toBe("(imp P Q)");
  });

  test("the sort is not what makes a collision dangerous", async () => {
    // A function letter is not of a provable sort and collides exactly as
    // hard: `{f: tm}` unscoped is `f` applied to the empty sequence.
    expect(await read("f = f")).toBe("(ideq (f snil) (f snil))");
    expect(await read("f = f", new Map([["f", "tm"]]))).toBe("(ideq f f)");
  });

  test("a scoped name shadows rather than outranks", async () => {
    // Not a fallback: the declared reading is gone for the length of the
    // parse. `P(a)` has no reading at all under a scoped `P`, where
    // unscoped it is the predicate letter applied to a name — which is
    // the honest outcome, since the metavariable takes no arguments.
    expect(await read("P(a)")).toBe("(P (a snil))");
    expect(await refusal("P(a)", wff("P"))).toBe("unexpected_token");
  });

  test("a scoped name is bound where it stands", async () => {
    // `closed-sentences` refuses a free variable, and `theorem unimp
    // {x: var} …` may perfectly well state a line with `x` in it. The
    // theorem binds it; the line does not have to.
    expect(await refusal("F(x)")).toBe("free_variable");
    expect(await read("F(x)", new Map([["x", "var"]]))).toBe("(F x)");
  });
});

describe("a scoped name keeps its notation reading", () => {
  test("Calgary spells ∀ with A, and a theorem may still bind A", async () => {
    // Shadowing is of the *lexicon*, not of the notation table: a theorem
    // that binds `(A: wff)` still has to be able to quantify. Which
    // reading an occurrence wants is settled by the parser's own
    // backtracking, exactly as the unscoped `A`-the-quantifier /
    // `A`-the-predicate-letter ambiguity already is.
    expect(await read("Ax F(x)", wff("A"))).toBe("(all x (F x))");
    expect(await read("A -> A", wff("A"))).toBe("(imp A A)");
  });
});

describe("scope survives the round trip to engine text", () => {
  test("a metavariable prints as its bare name", async () => {
    const { language } = await ready;
    const result = language.parse("~(P & Q) <-> (~P | ~Q)", {
      scope: wff("P", "Q"),
    });

    if (!result.ok) {
      throw new Error(result.diagnostics[0]?.message);
    }

    const engine = printTerm(language, result.term, "engine");

    expect(engine).toBe("((¬ (P ∧ Q)) ↔ ((¬ P) ∨ (¬ Q)))");

    // And engine mode reads its own output back in the same scope.
    const again = language.parse(engine, {
      mode: "engine",
      scope: wff("P", "Q"),
    });

    expect(again.ok).toBe(true);
  });
});
