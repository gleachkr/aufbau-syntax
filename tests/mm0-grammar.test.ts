import { describe, expect, test } from "bun:test";
import type { Term } from "../src/index";
import { parseSpec, printTerm, SurfaceLanguage } from "../src/index";
import { shape } from "./helpers/mm0-corpus";

/**
 * MM0's own grammar, feature by feature, on small specs — the corpus test
 * says the whole language reads; this says which production each
 * reading comes from, and pins the places where a surface convention is
 * allowed to sit in front of MM0's rule.
 */

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(
    diagnostics
      .filter((one) => one.severity === "error")
      .map((one) => one.message),
  ).toEqual([]);

  return new SurfaceLanguage(spec);
}

function read(lang: SurfaceLanguage, text: string, sort?: string): Term {
  const result = lang.parse(text, {
    mode: "engine",
    ...(sort === undefined ? {} : { sort }),
  });

  expect(
    result.ok
      ? "ok"
      : result.diagnostics.map((one) => one.message).join("; "),
  ).toBe("ok");

  if (!result.ok) {
    throw new Error("unreachable");
  }

  return result.term;
}

function refuse(lang: SurfaceLanguage, text: string): string {
  const result = lang.parse(text, { mode: "engine" });

  expect(result.ok).toBe(false);

  return result.ok ? "" : (result.diagnostics[0]?.message ?? "");
}

const ARITH = `delimiter $ ( ) $;
provable sort wff;
--| @vars x y
sort var;
sort tm;
term v2t (x: var): tm;
coercion v2t: var > tm;
--| @vars a b c
sort name;
term n2t (a: name): tm;
coercion n2t: name > tm;
term Red (x: tm): wff;
term succ (x: tm): tm;
term pair (x y: tm): tm;
term plus (x y: tm): tm;
infixl plus: $+$ prec 60;
term eq (x y: tm): wff;
infixl eq: $=$ prec 50;
term and (p q: wff): wff;
infixl and: $∧$ prec 30;
term all {x: var} (p: wff x): wff;
prefix all: $∀$ prec 40;
`;

describe("constructor application (expression(1024) → FUNC expression(max){n})", () => {
  const lang = language(ARITH);

  test("a bare argument is one expression at max", () => {
    expect(shape(read(lang, "succ a = b"))).toBe(
      "(eq (succ (n2t a)) (n2t b))",
    );
    expect(shape(read(lang, "pair a b = c"))).toBe(
      "(eq (pair (n2t a) (n2t b)) (n2t c))",
    );
  });

  test("bracketed and bare arguments mix, as they do in the engine", () => {
    expect(shape(read(lang, "pair (a) b = c"))).toBe(
      shape(read(lang, "pair a (b) = c")),
    );
    expect(shape(read(lang, "pair(a)(b) = c"))).toBe(
      shape(read(lang, "pair a b = c")),
    );
  });

  test("application sits below max: an argument that is itself an application is bracketed", () => {
    expect(shape(read(lang, "succ (succ a) = b"))).toBe(
      "(eq (succ (succ (n2t a))) (n2t b))",
    );
    expect(refuse(lang, "succ succ a = b")).toBe(
      "“succ” binds too loosely here; parenthesize it.",
    );
    expect(refuse(lang, "Red succ a")).toBe(
      "“succ” binds too loosely here; parenthesize it.",
    );
  });

  test("application is an operand of any infix", () => {
    expect(shape(read(lang, "succ a + b = c"))).toBe(
      "(eq (plus (succ (n2t a)) (n2t b)) (n2t c))",
    );
    expect(shape(read(lang, "a + succ b = c"))).toBe(
      "(eq (plus (n2t a) (succ (n2t b))) (n2t c))",
    );
  });

  test("a notated term is applicable by name, its bound binders positionally", () => {
    expect(shape(read(lang, "and (Red a) (Red b)"))).toBe(
      shape(read(lang, "Red a ∧ Red b")),
    );
    expect(shape(read(lang, "all x (Red x)"))).toBe(
      shape(read(lang, "∀ x Red x")),
    );
    expect(shape(read(lang, "plus a b = c"))).toBe(
      shape(read(lang, "a + b = c")),
    );
  });

  test("a bound slot takes a variable of its sort and nothing else", () => {
    expect(refuse(lang, "all a (Red a)")).toBe(
      "Expected a variable after the quantifier.",
    );
  });

  test("engine printing writes application bracketed, bound variables bare", () => {
    const term = read(lang, "all x (Red (succ x))");

    expect(printTerm(lang, term, "engine")).toBe("(∀ x (Red (succ (x))))");

    const byName = language(ARITH.replace("prefix all: $∀$ prec 40;\n", ""));

    expect(printTerm(byName, read(byName, "all x (Red x)"), "engine")).toBe(
      "all x (Red (x))",
    );
  });
});

describe("a declared surface shape sits in front of MM0's rule", () => {
  test("an elided unit wins over bare application for that sort", () => {
    const lang = language(`delimiter $ ( ) , $;
provable sort wff;
--| @vars a b
sort name;
sort seq;
term n2s (a: name): seq;
coercion n2s: name > seq;
--| @syntax elided
term snil: seq;
term scomma (s t: seq): seq;
infixl scomma: $,$ prec 10;
term P (s: seq): wff;
term and (p q: wff): wff;
infixl and: $∧$ prec 30;
`);

    // `P` alone is the sentence letter — the elision, declared for `seq`.
    expect(shape(read(lang, "P ∧ P"))).toBe("(and (P snil) (P snil))");
    // …so `P a` is not read as application: the bare letter stops, and
    // what follows it is unexpected. Bracketed application still reads.
    expect(refuse(lang, "P a")).toBe("Unexpected “a”.");
    expect(shape(read(lang, "P (a)"))).toBe("(P (n2s a))");
  });
});

describe("statement grammar beyond the surface dialects", () => {
  test("a def takes the arrow sugar and dot-dummies are not arguments", () => {
    const lang = language(`delimiter $ ( ) $;
provable sort wff;
--| @vars x
sort nat;
term ex {x: nat} (p: wff x): wff;
prefix ex: $∃$ prec 40;
term plus: nat > nat > nat;
term eq (a b: nat): wff;
infixl eq: $=$ prec 50;
def le {.k: nat} (a b: nat): wff = $ ∃ k (plus a k = b) $;
infixl le: $≤$ prec 45;
def K: nat > nat > nat;
`);

    expect(shape(read(lang, "plus x x ≤ x"))).toBe("(le (plus x x) x)");
    expect(shape(read(lang, "K x x = x"))).toBe("(eq (K x x) x)");
  });

  test("sorts and terms are separate namespaces", () => {
    const { diagnostics } = parseSpec(`provable sort wff;
sort nat;
def nat (p: wff): nat;
`);

    expect(diagnostics).toEqual([]);
  });

  test("input and output statements read and carry their items", () => {
    const { spec, diagnostics } = parseSpec(`provable sort wff;
term hello: wff;
output string: hello $ hello $;
input ast: $ hello $;
`);

    expect(diagnostics).toEqual([]);
    expect(
      spec.statements
        .filter((one) => one.kind === "input" || one.kind === "output")
        .map((one) =>
          one.kind === "input" || one.kind === "output"
            ? [one.kind, one.ioKind, one.items.length]
            : [],
        ),
    ).toEqual([
      ["output", "string", 2],
      ["input", "ast", 1],
    ]);
  });

  test("a token the delimiters split is dead: warned, and never the printed spelling", () => {
    const source = `delimiter $ ( ) [ / ] $;
--| @vars p q
provable sort wff;
term and (p q: wff): wff;
infixl and: $∧$ prec 30;
infixl and: $/\\$ prec 30;
`;
    const { spec, diagnostics } = parseSpec(source);

    expect(diagnostics.map((one) => [one.id, one.severity])).toEqual([
      ["delimiter_splits_token", "warning"],
    ]);

    const lang = new SurfaceLanguage(spec);

    // The last-declared notation would be canonical; it cannot be read
    // back, so the printer keeps the one that can.
    expect(printTerm(lang, read(lang, "p ∧ q"), "engine")).toBe("(p ∧ q)");
  });

  test("engine text spaces its grouping for a theory that declares no delimiters", () => {
    const lang = language(`--| @vars a
provable sort S;
term F: S > S;
term G (x y: S): S;
`);
    const printed = printTerm(lang, read(lang, "F ( G a a )"), "engine");

    expect(printed).toBe("F ( G ( a ) ( a ) )");
    expect(shape(read(lang, printed))).toBe("(F (G a a))");
  });
});
