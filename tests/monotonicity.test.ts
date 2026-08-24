import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { Diagnostic, Term } from "../src/index";
import { parseSpec, SurfaceLanguage } from "../src/index";

/**
 * The property the delimiter design exists to buy, held to a corpus so it
 * cannot rot: **declaring vocabulary cannot change how existing input is
 * cut up.**
 *
 * Under the maximal-munch scanner this replaced, it could. Appending
 * `term ab: tm;` to Magnus silently turned `Fab` from `F` of `a` and `b`
 * into `F` of the single name `ab` — and because the printer spelled the
 * new tree back as `Fab`, every round trip stayed clean and no test in the
 * suite could see it. Chunk boundaries now come from the delimiter set
 * alone, before anything is looked up, so a new declaration has only two
 * ways to go:
 *
 *   - the name survives segmentation, and existing input reads exactly as
 *     it did — the growth is invisible to everything already written; or
 *   - the delimiters split the name, and the *spec* is refused, at
 *     authoring time, naming the pieces.
 *
 * There is no third outcome where a student's formula quietly means
 * something else. Both halves are asserted below.
 *
 * The assertions are over **trees**, never printed forms: adding a notation
 * legitimately changes canonical spelling, since the last one declared
 * wins.
 */

type SpecName = "carnap-prop" | "forallx-calgary-2019" | "forallx-magnus";

/** A corpus entry's parse: the tree as an s-expression, or null if it failed. */
type Readings = ReadonlyMap<string, string | null>;

type Outcome =
  | {
      readonly kind: "read";
      readonly readings: Readings;
      readonly warnings: readonly Diagnostic[];
    }
  | { readonly kind: "refused"; readonly errors: readonly Diagnostic[] };

async function specSource(name: SpecName): Promise<string> {
  const path = new URL(`../specs/${name}.mm0`, import.meta.url).pathname;

  return await readFile(path, "utf8");
}

/** As in the surface corpus: coercion wrappers elided, everything else literal. */
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

  const args = term.args.map((arg) => sexpr(arg, coercions)).join(" ");

  return `(${term.term} ${args})`;
}

/**
 * Read a spec — optionally with `addition` appended — and parse the whole
 * corpus under it. An error-level diagnostic is a refusal: no language is
 * built, so there is nothing for the corpus to disagree with.
 */
function read(source: string, corpus: readonly string[]): Outcome {
  const { spec, diagnostics } = parseSpec(source);
  const errors = diagnostics.filter((d) => d.severity === "error");

  if (errors.length > 0) {
    return { kind: "refused", errors };
  }

  const language = new SurfaceLanguage(spec);
  const coercions = new Set(spec.coercions.map((c) => c.name));
  const readings = new Map<string, string | null>();

  for (const entry of corpus) {
    const result = language.parse(entry);

    readings.set(entry, result.ok ? sexpr(result.term, coercions) : null);
  }

  return {
    kind: "read",
    readings,
    warnings: diagnostics.filter((d) => d.severity === "warning"),
  };
}

async function baseline(
  name: SpecName,
  corpus: readonly string[],
): Promise<Outcome & { kind: "read" }> {
  const outcome = read(await specSource(name), corpus);

  if (outcome.kind !== "read") {
    throw new Error(
      `${name} does not read: ${outcome.errors[0]?.message ?? ""}`,
    );
  }

  return outcome;
}

async function grown(
  name: SpecName,
  addition: string,
  corpus: readonly string[],
): Promise<Outcome> {
  return read(`${await specSource(name)}\n${addition}\n`, corpus);
}

/**
 * The monotonicity assertion: every entry that parsed before parses to the
 * same tree after. An entry that *failed* before is unconstrained — growth
 * is allowed to admit new input, which is the whole point of it.
 */
function expectMonotone(before: Readings, after: Readings): void {
  for (const [entry, tree] of before) {
    if (tree === null) {
      continue;
    }

    expect(after.get(entry), entry).toBe(tree);
  }
}

/**
 * Corpora broad enough that a moved boundary anywhere shows up: tight
 * input, quantifier prefixes, bracketing, every precedence rung. The last
 * few entries of each are the strings the growths below are supposed to
 * newly admit, so a growth that quietly does nothing fails too.
 */
const CALGARY = [
  "P",
  "~~P",
  "P /\\ Q \\/ R",
  "AxF(x) -> G(a)",
  "Ax(F(x) -> G(x))",
  "AxEy~R(x,y)",
  "AxAyf(x,y) = f(y,x)",
  "a != b",
  "R(a,b)",
  "[P /\\ Q] -> R",
  "⊥ \\/ ⊤",
  "Axy",
  "Z",
  "_0",
  "P ↓ Q",
];

const MAGNUS = [
  "Fab",
  "Fx",
  "Rabc",
  "AxFx",
  "Axy",
  "AxEy~Rxy",
  "AxAy(Fxy -> Fyx)",
  "P -> Q",
  "~(P & Q)",
  "a = b",
  "_0",
];

const PROP = [
  "P",
  "~~P",
  "P /\\ Q \\/ R",
  "P -> (Q -> R)",
  "~(P <-> q)",
  "_0",
];

const CORPORA: ReadonlyMap<SpecName, readonly string[]> = new Map([
  ["carnap-prop", PROP],
  ["forallx-calgary-2019", CALGARY],
  ["forallx-magnus", MAGNUS],
]);

describe("a name the delimiters split is refused, not silently read", () => {
  test("Magnus: `term ab: tm;` cannot re-read Fab, because it cannot be declared", async () => {
    const before = await baseline("forallx-magnus", MAGNUS);

    // What is at stake: the munch scanner made this `(F ab)` instead, and
    // printed it back as `Fab`, so nothing downstream could tell.
    expect(before.readings.get("Fab")).toBe("(F (scomma a b))");

    const after = await grown("forallx-magnus", "term ab: tm;", MAGNUS);

    expect(after.kind).toBe("refused");

    if (after.kind === "refused") {
      expect(after.errors.map((d) => [d.id, d.params])).toEqual([
        ["delimiter_unreachable_name", { chunks: "a b", name: "ab" }],
      ]);
    }
  });

  test("Calgary: a name colliding with a notation spelling is refused too", async () => {
    const before = await baseline("forallx-calgary-2019", CALGARY);

    // Longest-munch would have preferred the new name over the quantifier
    // reading, turning a bound formula into a two-place predicate.
    expect(before.readings.get("AxF(x) -> G(a)")).toBe(
      "(imp (all x (F x)) (G (a snil)))",
    );

    const after = await grown(
      "forallx-calgary-2019",
      "term Ax (s: seq): wff;",
      CALGARY,
    );

    expect(after.kind).toBe("refused");

    if (after.kind === "refused") {
      expect(after.errors.map((d) => [d.id, d.params])).toEqual([
        ["delimiter_unreachable_name", { chunks: "A x", name: "Ax" }],
      ]);
    }
  });

  test("a letter lexicon closes itself: no multi-letter name fits any shipped spec", async () => {
    for (const [name, corpus] of CORPORA) {
      for (const candidate of ["ab", "foo", "P1", "Fx"]) {
        const after = await grown(name, `term ${candidate}: wff;`, corpus);

        expect(after.kind, `${name} + ${candidate}`).toBe("refused");

        if (after.kind === "refused") {
          expect(
            after.errors.map((d) => d.id),
            `${name} + ${candidate}`,
          ).toContain("delimiter_unreachable_name");
        }
      }
    }
  });
});

describe("a name the delimiters admit changes nothing already written", () => {
  test("every shipped spec takes a fresh lexicon name invisibly", async () => {
    // `_0` survives segmentation where `ab` does not: the letters delimit,
    // `_` and `0` do not. That is the only shape a fresh name can have
    // under a lexicon that spends all 52 letters — which is what makes the
    // refusals above the normal case, not an edge one.
    for (const [name, corpus] of CORPORA) {
      const before = await baseline(name, corpus);
      const after = await grown(name, "term _0: wff;", corpus);

      expect(after.kind, name).toBe("read");

      if (after.kind !== "read") {
        continue;
      }

      expect(after.warnings, name).toEqual([]);
      expectMonotone(before.readings, after.readings);

      // Non-vacuity: the vocabulary really did grow.
      expect(before.readings.get("_0"), name).toBeNull();
      expect(after.readings.get("_0"), name).toBe("_0");
    }
  });

  test("a new notation is invisible until its token is written", async () => {
    const before = await baseline("forallx-calgary-2019", CALGARY);
    const after = await grown(
      "forallx-calgary-2019",
      "term nor (p q: wff): wff;\ninfixl nor: $↓$ prec 30;",
      CALGARY,
    );

    expect(after.kind).toBe("read");

    if (after.kind !== "read") {
      return;
    }

    // The reader's advice, not an error: `↓` is not itself a delimiter, so
    // it reads only where something else bounds it. Between letters, which
    // do delimit, it is fine; against another undelimited token it would
    // run together.
    expect(after.warnings.map((d) => [d.id, d.params])).toEqual([
      ["delimiter_token_not_delimited", { token: "↓" }],
    ]);

    expectMonotone(before.readings, after.readings);
    expect(after.readings.get("P ↓ Q")).toBe("(nor (P snil) (Q snil))");
  });

  test("a notation spelled like an existing name resolves by backtracking", async () => {
    // The `A`-as-∀-vs-predicate ambiguity, created on purpose: `Z` now
    // classifies as both a token and a name. Segmentation does not care —
    // the chunk is `Z` either way — and the parser tries the token reading
    // first, falling back to the name when it finds no operand.
    const before = await baseline("forallx-calgary-2019", CALGARY);
    const after = await grown(
      "forallx-calgary-2019",
      "prefix not: $Z$ prec 40;",
      CALGARY,
    );

    expect(after.kind).toBe("read");

    if (after.kind !== "read") {
      return;
    }

    expectMonotone(before.readings, after.readings);
    expect(after.readings.get("Z")).toBe("(Z snil)");
  });
});
