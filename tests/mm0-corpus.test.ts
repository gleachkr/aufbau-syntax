import { beforeAll, describe, expect, test } from "bun:test";
import { loadCompiler } from "@aufbau/compiler";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";
import {
  axiomized,
  corpusFiles,
  corpusFormulas,
  corpusSource,
  enginePrinting,
  readCorpusFormula,
  shape,
} from "./helpers/mm0-corpus";

/**
 * The claim this library makes is that it reads a superset of MM0: every
 * `.mm0` file the engine accepts, this reads to the same trees. The
 * corpus under `tests/fixtures/mm0/` is the reference material for that
 * claim — the upstream MM0 examples (peano, set, hol, the self-describing
 * mm0.mm0, x86) and the Aufbau repository's own theories and preludes —
 * and each file is put to three tests:
 *
 *   1. the statement reader takes the file with no error (warnings are
 *      allowed: a dead token the engine also cannot read);
 *   2. every math string in it — hypothesis, conclusion, hypothesis
 *      binder, definiens — parses in engine mode, in its statement's
 *      binder scope, and the engine-mode printing of that parse reads
 *      back to the same tree;
 *   3. the Aufbau compiler agrees: the file with every math string
 *      replaced by this library's printing compiles to byte-identical
 *      MMB with the original (theorems stated as axioms so that no proof
 *      is owed, bodyless defs as terms). The MMB carries every
 *      statement's expression trees, so the bytes agree exactly when the
 *      two readings did.
 */

const files = corpusFiles();

describe("the MM0 corpus reads", () => {
  test("the corpus is present", () => {
    expect(files.length).toBeGreaterThan(50);
  });

  for (const name of files) {
    test(`${name}: every statement and math string, round-tripped`, () => {
      const source = corpusSource(name);
      const { spec, diagnostics } = parseSpec(source);

      expect(
        diagnostics
          .filter((one) => one.severity === "error")
          .map((one) => `${one.id}: ${one.message}`),
      ).toEqual([]);

      const lang = new SurfaceLanguage(spec);
      const formulas = corpusFormulas(spec);
      const failures: string[] = [];

      for (const formula of formulas) {
        const read = readCorpusFormula(lang, formula);

        if (!read.ok) {
          failures.push(
            `${formula.statement}/${formula.role} “${formula.math.text.trim()}”: ${read.diagnostics.map((one) => one.message).join("; ")}`,
          );
          continue;
        }

        const printed = printTerm(lang, read.term, "engine");
        const again = lang.parse(printed, {
          mode: "engine",
          scope: formula.scope,
          sort: read.term.sort,
        });

        if (!again.ok) {
          failures.push(
            `${formula.statement}/${formula.role} printed “${printed}” does not re-read: ${again.diagnostics.map((one) => one.message).join("; ")}`,
          );
        } else if (shape(again.term) !== shape(read.term)) {
          failures.push(
            `${formula.statement}/${formula.role} printed “${printed}” re-reads as ${shape(again.term)}, not ${shape(read.term)}`,
          );
        }
      }

      expect(failures).toEqual([]);
      // string.mm0 states nothing; every other file states something.
      expect(formulas.length).toBeGreaterThanOrEqual(
        name === "string.mm0" ? 0 : 1,
      );
    });
  }
});

describe("the Aufbau compiler reads the corpus the way this library does", () => {
  let compiler: Awaited<ReturnType<typeof loadCompiler>>;

  beforeAll(async () => {
    compiler = await loadCompiler();
  });

  for (const name of files) {
    test(`${name}: identical MMB from the original and the reprinted text`, () => {
      const source = corpusSource(name);
      const { spec } = parseSpec(source);
      const lang = new SurfaceLanguage(spec);

      const original = compiler.compile(axiomized(source, spec), "");

      expect(
        original.ok === true
          ? "ok"
          : `original refused: ${JSON.stringify(original.diagnostics)}`,
      ).toBe("ok");

      const reprinted = compiler.compile(
        axiomized(source, spec, (formula) => enginePrinting(lang, formula)),
        "",
      );

      expect(
        reprinted.ok === true
          ? "ok"
          : `reprinted refused: ${JSON.stringify(reprinted.diagnostics)}`,
      ).toBe("ok");

      expect(Buffer.from(reprinted.mmbBytes ?? [])).toEqual(
        Buffer.from(original.mmbBytes ?? []),
      );
    });
  }
});
