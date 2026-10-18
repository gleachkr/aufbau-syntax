import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Term } from "../src/index";
import {
  parseSpec,
  printTerm,
  SurfaceLanguage,
  unfoldDefinitions,
} from "../src/index";

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

const calgary = language(
  readFileSync(
    new URL("../specs/forallx-calgary-2019.mm0", import.meta.url).pathname,
    "utf8",
  ),
);

/** Binders and dummies: a def over a bound variable, and one with a dummy. */
const BINDING = `
delimiter $ ( ) $;
provable sort wff;
--| @vars x y z w
sort var;
term F (x: var): wff;
term not (p: wff): wff;
prefix not: $¬$ prec 40;
term ex {x: var} (p: wff x): wff;
notation ex {x: var} (p: wff x): wff = ($∃$:40) x p;
def nex {x: var} (p: wff x): wff = $ ¬ ∃ x p $;
def some (p: wff) {.z: var}: wff = $ ∃ z p $;
`;

const binding = language(BINDING);

function read(lang: SurfaceLanguage, text: string, mode = "surface"): Term {
  const result = lang.parse(text, {
    lints: false,
    mode: mode as "surface" | "engine",
  });

  if (!result.ok) {
    throw new Error(`Expected '${text}' to parse.`);
  }

  return result.term;
}

function unfolded(lang: SurfaceLanguage, text: string, mode = "surface") {
  return printTerm(
    lang,
    unfoldDefinitions(lang, read(lang, text, mode)),
    "engine",
  );
}

describe("unfoldDefinitions", () => {
  test("a def is its definiens, with the arguments in its binders", () => {
    expect(unfolded(calgary, "a ≠ b")).toBe(
      printTerm(calgary, read(calgary, "¬a = b"), "engine"),
    );
  });

  test("defs inside a term unfold where they stand", () => {
    expect(unfolded(calgary, "¬a ≠ b ∧ P")).toBe(
      printTerm(calgary, read(calgary, "¬¬a = b ∧ P"), "engine"),
    );
  });

  test("a term with no def in it is the same term", () => {
    const term = read(calgary, "∀x(F(x) → x = a)");

    expect(unfoldDefinitions(calgary, term)).toBe(term);
  });

  test("a bound binder takes the argument's variable", () => {
    expect(unfolded(binding, "nex y (F y)", "engine")).toBe(
      printTerm(binding, read(binding, "¬ ∃ y (F y)", "engine"), "engine"),
    );
  });

  test("a dummy an argument also names is renamed, not captured", () => {
    expect(unfolded(binding, "some (F z)", "engine")).toBe(
      printTerm(binding, read(binding, "∃ x (F z)", "engine"), "engine"),
    );
    expect(unfolded(binding, "some (F y)", "engine")).toBe(
      printTerm(binding, read(binding, "∃ z (F y)", "engine"), "engine"),
    );
  });
});
