import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import {
  notationToken,
  parseSpec,
  SurfaceLanguage,
  spellingMeanings,
  spellingsOf,
  splitTopLevel,
} from "../src/index";

/** Spellings both ways, and splitting a list the way its brackets group it. */

async function calgary(): Promise<SurfaceLanguage> {
  const path = new URL("../specs/forallx-calgary-2019.mm0", import.meta.url)
    .pathname;
  const { spec, diagnostics } = parseSpec(await readFile(path, "utf8"));

  expect(diagnostics).toEqual([]);

  return new SurfaceLanguage(spec);
}

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

describe("spellingsOf", () => {
  test("the canonical token first, then the rest in declaration order", async () => {
    const lang = await calgary();

    expect(spellingsOf(lang, "and")).toEqual(["∧", "/\\", "^", "&"]);
    expect(spellingsOf(lang, "ex")).toEqual(["∃", "E", "3"]);
  });

  test("a general notation is known by its first constant", async () => {
    const lang = await calgary();
    const bot = lang.spec.notations.find(
      (notation) => notation.term === "bot",
    );

    expect(bot && notationToken(bot)).toBe("!?");
    expect(spellingsOf(lang, "bot")).toEqual(["⊥", "!?", "_|_"]);
  });

  test("a term spelled by its name has no notation token", async () => {
    expect(spellingsOf(await calgary(), "F")).toEqual([]);
  });
});

describe("spellingMeanings", () => {
  test("one spelling can be a term and a notation at once", async () => {
    // Calgary's `E` is the predicate letter E and a spelling of ∃.
    expect(spellingMeanings(await calgary(), "E")).toEqual({
      terms: ["E", "ex"],
      varSorts: [],
    });
  });

  test("an elab rule's input spelling means what its template writes", () => {
    const lang = language(`provable sort wff;
--| @vars x
sort var;
term all {x: var} (p: wff x): wff;
prefix all: $∀$ prec 40;
--| @syntax elab $ every ?x:var $ => $ ∀ ?x $ input-only
term t: wff;
`);

    expect(spellingMeanings(lang, "every").terms).toEqual(["all"]);
    expect(spellingMeanings(lang, "x")).toEqual({
      terms: [],
      varSorts: ["var"],
    });
    expect(spellingMeanings(lang, "nothing")).toEqual({
      terms: [],
      varSorts: [],
    });
  });
});

describe("splitTopLevel", () => {
  const PREFIX = `provable sort wff;\nsort tm;\n--| @vars a b c\nsort name;\n`;

  test("splits outside the grouping pairs the language declares", async () => {
    const lang = await calgary();

    expect(splitTopLevel(lang, "R(a,b), [F(c) & G(d,e)], P", ",")).toEqual([
      "R(a,b)",
      " [F(c) & G(d,e)]",
      " P",
    ]);
  });

  test("a bracket the language does not declare groups nothing", () => {
    const plain = language(PREFIX);
    const angled = language(`--| @syntax brackets ⟨ ⟩\n${PREFIX}`);

    expect(splitTopLevel(plain, "⟨a, b⟩, c", ",")).toEqual([
      "⟨a",
      " b⟩",
      " c",
    ]);
    expect(splitTopLevel(angled, "⟨a, b⟩, c", ",")).toEqual(["⟨a, b⟩", " c"]);
  });

  test("joining the pieces gives the text back", async () => {
    const lang = await calgary();
    const text = "P,, Q : (R : S)";

    expect(splitTopLevel(lang, text, ",").join(",")).toBe(text);
    expect(splitTopLevel(lang, text, ":")).toEqual(["P,, Q ", " (R : S)"]);
  });

  test("a stray close hides no later separator", async () => {
    expect(splitTopLevel(await calgary(), "a), b(c, d)", ",")).toEqual([
      "a)",
      " b(c, d)",
    ]);
  });
});
