import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { PrintedPiece, Term } from "../src/index";
import {
  parseSpec,
  printPieces,
  printTerm,
  SurfaceLanguage,
} from "../src/index";
import { seeded, termGenerator } from "./helpers/terms";

/**
 * **`printPieces` is `printTerm`, attributed.** Its pieces join to exactly
 * the display text, every piece names a node the term has, and — where no
 * `@syntax elab` rule rewrites the text afterwards — a node's pieces are
 * one unbroken run, so a reader can put one thing under each subterm.
 * Checked over generated terms, as the round trip is, then on the shapes
 * Carnap reads pieces for.
 */

function file(path: string): string {
  return readFileSync(new URL(path, import.meta.url).pathname, "utf8");
}

const SOURCES: readonly (readonly [string, string])[] = [
  ["carnap-prop", file("../specs/carnap-prop.mm0")],
  ["forallx-calgary-2019", file("../specs/forallx-calgary-2019.mm0")],
  ["forallx-magnus", file("../specs/forallx-magnus.mm0")],
  ["signed rows", file("./fixtures/signed-rows.mm0")],
  ["forallx-ubc", file("./fixtures/carnap/forallx-ubc.mm0")],
  ["open-logic-tableaux", file("./fixtures/carnap/open-logic-tableaux.mm0")],
  [
    "open-logic-intuitionistic",
    file("./fixtures/carnap/open-logic-intuitionistic.mm0"),
  ],
];

function language(source: string): SurfaceLanguage {
  return new SurfaceLanguage(parseSpec(source).spec);
}

function nodeAt(term: Term, path: readonly number[]): Term | undefined {
  let at: Term | undefined = term;

  for (const index of path) {
    at = at?.kind === "app" ? at.args[index] : undefined;
  }

  return at;
}

function within(path: readonly number[], node: readonly number[]): boolean {
  return node.every((index, at) => path[at] === index);
}

/** The nodes whose pieces do not form one run, as `0.1` paths. */
function broken(pieces: readonly PrintedPiece[]): string[] {
  const nodes = new Map<string, readonly number[]>();

  for (const piece of pieces) {
    for (let depth = 0; depth <= piece.path.length; depth += 1) {
      const node = piece.path.slice(0, depth);
      nodes.set(node.join("."), node);
    }
  }

  return [...nodes].flatMap(([key, node]) => {
    const inside = pieces.map((piece) => within(piece.path, node));
    const first = inside.indexOf(true);
    const last = inside.lastIndexOf(true);

    return inside.slice(first, last + 1).every(Boolean) ? [] : [key];
  });
}

describe("printPieces over generated terms", () => {
  for (const [name, source] of SOURCES) {
    test(name, () => {
      const lang = language(source);
      const rewritten = lang.spec.elabRules.some((rule) => !rule.inputOnly);
      const generate = termGenerator(lang, seeded(name.length), new Map());
      const sorts = [...lang.spec.sorts.keys()];
      const failures: string[] = [];
      let checked = 0;

      for (let i = 0; i < 120; i += 1) {
        const term = generate(sorts[i % sorts.length] ?? "", 1 + (i % 5));

        if (term === null) {
          continue;
        }

        checked += 1;
        const pieces = printPieces(lang, term);
        const text = printTerm(lang, term);
        const joined = pieces.map((piece) => piece.text).join("");
        const strays = pieces.filter(
          (piece) => nodeAt(term, piece.path) === undefined,
        );
        const runs = rewritten ? [] : broken(pieces);

        if (joined !== text || strays.length > 0 || runs.length > 0) {
          failures.push(
            `${JSON.stringify(text)}: joined ${JSON.stringify(joined)}, ${strays.length} stray, broken ${runs.join(" ")}`,
          );
        }

        expect(pieces.every((piece) => piece.text.length > 0)).toBe(true);
      }

      expect(checked).toBeGreaterThan(30);
      expect(failures).toEqual([]);
    });
  }
});

function shown(
  lang: SurfaceLanguage,
  source: string,
  sort?: string,
): string[] {
  const read = lang.parse(source, sort === undefined ? {} : { sort });

  if (!read.ok) {
    throw new Error(`'${source}': ${read.diagnostics[0]?.message}`);
  }

  return printPieces(lang, read.term).map(
    (piece) => `${piece.kind} ${piece.text} @${piece.path.join(".")}`,
  );
}

describe("what each piece belongs to", () => {
  test("a connective's token and its own pair are its node's", () => {
    const prop = language(file("../specs/carnap-prop.mm0"));

    expect(shown(prop, "~(P /\\ Q) -> R")).toEqual([
      "bracket ( @",
      "token ~ @0",
      "bracket ( @0.0",
      "name P @0.0.0",
      "space   @0.0",
      "token /\\ @0.0",
      "space   @0.0",
      "name Q @0.0.1",
      "bracket ) @0.0",
      "space   @",
      "token -> @",
      "space   @",
      "name R @1",
      "bracket ) @",
    ]);
  });

  test("an application's head and argument brackets are the application's", () => {
    const calgary = language(file("../specs/forallx-calgary-2019.mm0"));
    const pieces = shown(calgary, "∀x F(x)");

    expect(pieces[0]).toBe("token ∀ @");
    expect(pieces).toContain("name F @1");
    expect(pieces).toContain("bracket ( @1");
    expect(pieces.at(-1)).toBe("bracket ) @1");
  });

  test("text an elab rule rewrites keeps its node", () => {
    // UBC's subscripts are elab rules: `a1` prints as `a₁`, one name.
    const ubc = language(file("./fixtures/carnap/forallx-ubc.mm0"));

    expect(shown(ubc, "Fa₁").map((piece) => piece.split(" @")[0])).toEqual([
      "name F",
      "name a₁",
    ]);

    // Intuitionistic prefixes too, and everything after an astral `𝕋`
    // stays where it was.
    const intuitionistic = language(
      file("./fixtures/carnap/open-logic-intuitionistic.mm0"),
    );
    const read = intuitionistic.parse("1.1.2 𝕋 A ∧ B", { sort: "pfm" });

    if (!read.ok) {
      throw new Error(read.diagnostics[0]?.message);
    }

    const pieces = printPieces(intuitionistic, read.term);
    const under = (index: number): string =>
      pieces
        .filter((piece) => piece.path[0] === index)
        .map((piece) => piece.text)
        .join("");

    expect(under(0)).toBe("1.1.2");
    expect(under(1)).toBe("A ∧ B");
    expect(pieces.at(-1)).toEqual({ text: "B", path: [1, 1], kind: "name" });
  });
});
