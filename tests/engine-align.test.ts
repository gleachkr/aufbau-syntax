import { beforeAll, describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import { loadCompiler } from "@aufbau/compiler";
import type { Term } from "../src/index";
import {
  boundVariableBinders,
  parseSpec,
  printTerm,
  SurfaceLanguage,
  stripSyntaxAnnotations,
} from "../src/index";

/**
 * The acceptance gate for the library's whole premise: the Aufbau
 * compiler itself parses our engine-mode output, and parses it to the
 * same tree we built.
 *
 * Mechanism (the notation-identity trick from Aufbau's own manual): a
 * lemma `$ X ↔ Y $ by iff_refl` compiles only if X and Y are the same
 * expression. X is this library's engine-mode emission of a student
 * formula; Y is a hand-written engine spelling of the intended reading.
 * The theory is the Calgary spec file with `@syntax` lines stripped —
 * the exact artifact a server would hand the engine, lexicon included:
 * the letters are ordinary declarations now, so nothing needs elaborating.
 *
 * The cases avoid `A` and `E` as sentence letters: those tokens are also
 * quantifier spellings, which own them inside the engine's math strings —
 * a pre-existing limit of keeping the ASCII quantifier aliases in the
 * engine-facing theory.
 *
 * A case with a `scope` is the same gate run over a *schematic* theorem —
 * one whose binders collide with the lexicon. It is the sharpest form of
 * the claim: the engine shadows those names with the theorem's binders,
 * this library shadows them with the same scope, and `iff_refl` compiles
 * only if the two agree about every letter.
 */

interface Case {
  readonly name: string;
  readonly source: string;
  readonly engineSpelling: string;
  /** The theorem's own binders, name to sort — shadowing the lexicon. */
  readonly scope?: Readonly<Record<string, string>>;
}

const CASES: readonly Case[] = [
  {
    name: "quantifiers_negation",
    source: "AxEy~R(x,y)",
    engineSpelling: "∀ x (∃ y (¬ (R (x , y))))",
  },
  {
    name: "connective_precedence",
    source: "P /\\ Q -> S",
    engineSpelling: "((P snil) ∧ (Q snil)) → (S snil)",
  },
  {
    name: "functions_identity",
    source: "AxAyf(x,y) = f(y,x)",
    engineSpelling: "∀ x (∀ y ((f (x , y)) = (f (y , x))))",
  },
  {
    name: "de_morgan_shape",
    source: "~(P \\/ Q) <-> (~P /\\ ~Q)",
    engineSpelling:
      "(¬ ((P snil) ∨ (Q snil))) ↔ ((¬ (P snil)) ∧ (¬ (Q snil)))",
  },
  {
    name: "inequality_def",
    source: "a != b",
    engineSpelling: "(a snil) ≠ (b snil)",
  },
  {
    // The shape 12 of the 19 forallx rule cases are stated in, and the
    // one a global-vocabulary parse gets silently wrong: unscoped, `P`
    // here is the predicate letter applied to the elided empty sequence,
    // and no proof of this theorem could ever close.
    name: "schematic_de_morgan",
    source: "~(P & Q) <-> (~P | ~Q)",
    engineSpelling: "(¬ (P ∧ Q)) ↔ ((¬ P) ∨ (¬ Q))",
    scope: { P: "wff", Q: "wff" },
  },
  {
    // A collision at a sort no quantifier binds, mixed with a genuine
    // quantifier: `f` is the theorem's own term metavariable, `x` the
    // variable ∀ binds. Both are lexicon names too.
    name: "schematic_function_letter",
    source: "Ax f = x",
    engineSpelling: "∀ x (f = x)",
    scope: { f: "tm" },
  },
];

/** A scope as MM0 binder text: `(P: wff) (Q: wff)`. */
function scopeBinders(scope: Case["scope"]): string {
  return Object.entries(scope ?? {})
    .map(([name, sort]) => `(${name}: ${sort})`)
    .join(" ");
}

let language: SurfaceLanguage;
let specSource: string;
let parsedTerms: Term[];

beforeAll(async () => {
  const path = new URL("../specs/forallx-calgary-2019.mm0", import.meta.url)
    .pathname;

  specSource = await readFile(path, "utf8");

  const { spec, diagnostics } = parseSpec(specSource);

  expect(diagnostics).toEqual([]);
  language = new SurfaceLanguage(spec);

  parsedTerms = CASES.map((testCase) => {
    const result = language.parse(testCase.source, {
      scope: new Map(Object.entries(testCase.scope ?? {})),
    });

    if (!result.ok) {
      throw new Error(
        `'${testCase.source}': ${result.diagnostics[0]?.message}`,
      );
    }

    return result.term;
  });
});

describe("the Aufbau compiler accepts engine-mode output", () => {
  test("every emission equals its hand-written engine spelling", async () => {
    const wasmBytes = await readFile(
      new URL(
        "../node_modules/@aufbau/compiler/compiler.wasm",
        import.meta.url,
      ),
    );
    const compiler = await loadCompiler({ wasmBytes });

    const theorems = CASES.map((testCase, index) => {
      const term = parsedTerms[index];

      if (term === undefined) {
        throw new Error("missing parsed term");
      }

      const binders = [
        boundVariableBinders([term]),
        scopeBinders(testCase.scope),
      ]
        .filter((part) => part !== "")
        .join(" ");
      const ours = printTerm(language, term, "engine");
      const conclusion = `$ (${ours}) ↔ (${testCase.engineSpelling}) $`;

      return {
        statement: `theorem ${testCase.name}${
          binders === "" ? "" : ` ${binders}`
        }: ${conclusion};`,
        proof: `${testCase.name}\n----\nl1: ${conclusion} by iff_refl`,
      };
    });

    const mm0 = [
      stripSyntaxAnnotations(specSource),
      "axiom iff_refl (p: wff): $ p ↔ p $;",
      ...theorems.map((theorem) => theorem.statement),
    ].join("\n");
    const auf = theorems.map((theorem) => theorem.proof).join("\n\n");

    const compiled = compiler.compile(mm0, auf);

    if (!compiled.ok) {
      throw new Error(
        `engine rejected the emission:\n${JSON.stringify(compiled, null, 2)}`,
      );
    }

    expect((compiled.mmbBytes ?? new Uint8Array()).length).toBeGreaterThan(0);
  });
});
