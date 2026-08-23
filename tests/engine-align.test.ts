import { beforeAll, describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import { loadCompiler } from "@aufbau/compiler";
import type { Term } from "../src/index";
import {
  boundVariableBinders,
  elaboratedDeclarations,
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
 * the exact artifact a server would hand the engine — plus the
 * elaborated declarations for the letters the cases use.
 *
 * Letters keep one arity across all cases (R stays binary, S stays a
 * sentence letter): elaboration declares each name once.
 */

interface Case {
  readonly name: string;
  readonly source: string;
  readonly engineSpelling: string;
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
    engineSpelling: "(P ∧ Q) → S",
  },
  {
    name: "functions_identity",
    source: "AxAyf(x,y) = f(y,x)",
    engineSpelling: "∀ x (∀ y ((f (x , y)) = (f (y , x))))",
  },
  {
    name: "de_morgan_shape",
    source: "~(P \\/ Q) <-> (~P /\\ ~Q)",
    engineSpelling: "(¬ (P ∨ Q)) ↔ ((¬ P) ∧ (¬ Q))",
  },
  {
    name: "inequality_def",
    source: "a != b",
    engineSpelling: "a ≠ b",
  },
];

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
    const result = language.parse(testCase.source);

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

      const binders = boundVariableBinders([term]);
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
      elaboratedDeclarations(language, parsedTerms),
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
