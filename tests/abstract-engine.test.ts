import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Term } from "../src/index";
import {
  abstractContext,
  boundVariableBinders,
  parseSpec,
  printTerm,
  SurfaceLanguage,
} from "../src/index";
import { probeErrors } from "./helpers/engine-probe";
import { CORPUS_DIR, shape } from "./helpers/mm0-corpus";
import { seeded, termGenerator } from "./helpers/terms";

/**
 * The differential check for `abstractContext`: on random pairs, it
 * recovers the context the Aufbau compiler's `@abstract` does.
 *
 * Each theory is extended with a probe rule whose `@view` leaves `r` to its
 * `@abstract r p q x a b` alone (its conclusion is a phantom), and whose
 * conclusion shows `r` and nothing else (`zz_show x r`, with no rewrites).
 * Cited from `A = B` and `P ~ Q`, a line `zz_show x R` checks where the
 * walk recovered `R`. Where the walk recovers nothing, binding inference
 * fills `r` from the line, and any `R` checks. So each case is asked twice,
 * with the library's context and with junk (`zz_junk`, which no case
 * has), and the two verdicts say what the engine's walk did.
 *
 * The pairs are `P` with `A` put in at random places of its sort, and `Q`
 * that with every `A` made `B`, some of them, none, or one subterm
 * changed. `leibniz.mm0` has no coercions and computes substitutions, so
 * the retry normalizes; the small theory has names and variables that
 * meet at terms, as Carnap's forallx theories do, and a def to open.
 */

const TRIALS = Number(process.env.TRIALS ?? 240);
const SPAN = { end: 0, start: 0 } as const;
/** The hole: the probe's `x`, given explicitly, so both sides name it alike. */
const HOLE = "zz_hole";

interface Setup {
  readonly name: string;
  readonly source: string;
  /** The probe rule, and how its two premises are written. */
  readonly rule: string;
  readonly premise: (a: string, b: string) => string;
  readonly pair: (p: string, q: string) => string;
  /** The theorem's regular variables, by sort. */
  readonly atoms: ReadonlyMap<string, string>;
  readonly plug: string;
  readonly row: string;
  readonly hole: string;
}

const LEIBNIZ: Setup = {
  atoms: new Map(["a", "b", "c", "d"].map((name) => [name, "real"])),
  hole: "real",
  name: "leibniz: one sort",
  pair: (p, q) => `${p} = ${q}`,
  plug: "real",
  premise: (a, b) => `${a} = ${b}`,
  row: "real",
  rule: "zz_probe",
  source: `${readFileSync(`${CORPUS_DIR}/leibniz.mm0`, "utf8")}
term zz_junk: real;
term zz_show {x: real} (r: real x): wff;
--| @view {x: real} (a b p q: real) (r: real x) (c: wff): $ a = b $ > $ p = q $ > $ c $
--| @abstract r p q x a b
axiom zz_probe {x: real} (a b p q: real) (r: real x):
  $ a = b $ > $ p = q $ > $ zz_show x r $;
`,
};

const SORTS = `delimiter $ ( ) $;
provable sort wff;
--| @vars x y
sort var;
sort name;
sort tm;
term v2t (x: var): tm;
coercion v2t: var > tm;
term n2t (a: name): tm;
coercion n2t: name > tm;
term k0: tm;
term k1: tm;
term F (t: tm): wff;
term R (s t: tm): wff;
term neg (p: wff): wff;
term and (p q: wff): wff;
term all {x: var} (p: wff x): wff;
def Fd (t: tm): wff = $ F t $;
term same (p q: wff): wff;
term eqn (a b: name): wff;
term teq (s t: tm): wff;
term zz_junk: wff;
term zz_show {x: var} (r: wff x): wff;
--| @view {x: var} (a b: name) (p q: wff) (r: wff x) (c: wff): $ eqn a b $ > $ same p q $ > $ c $
--| @abstract r p q x a b
axiom zz_names {x: var} (a b: name) (p q: wff) (r: wff x):
  $ eqn a b $ > $ same p q $ > $ zz_show x r $;
--| @view {x: var} (a b: tm) (p q: wff) (r: wff x) (c: wff): $ teq a b $ > $ same p q $ > $ c $
--| @abstract r p q x a b
axiom zz_terms {x: var} (a b: tm) (p q: wff) (r: wff x):
  $ teq a b $ > $ same p q $ > $ zz_show x r $;
`;

const NAMES: Setup = {
  atoms: new Map(["a", "b", "c"].map((name) => [name, "name"])),
  hole: "var",
  name: "names and a variable, meeting at terms",
  pair: (p, q) => `same (${p}) (${q})`,
  plug: "name",
  premise: (a, b) => `eqn (${a}) (${b})`,
  row: "wff",
  rule: "zz_names",
  source: SORTS,
};

const TERMS: Setup = {
  ...NAMES,
  name: "terms and a variable, meeting at terms",
  plug: "tm",
  premise: (a, b) => `teq (${a}) (${b})`,
  rule: "zz_terms",
};

function language(setup: Setup): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(setup.source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

function variable(name: string, sort: string): Term {
  return {
    binder: false,
    grouped: false,
    kind: "variable",
    name,
    sort,
    span: SPAN,
  };
}

/** Every position of a subterm of `sort`, as the path of argument indices to it. */
function positions(term: Term, sort: string, at: number[] = []): number[][] {
  return [
    ...(term.sort === sort ? [at] : []),
    ...(term.kind === "app"
      ? term.args.flatMap((arg, index) =>
          arg.kind === "variable" && arg.binder
            ? []
            : positions(arg, sort, [...at, index]),
        )
      : []),
  ];
}

/** `term` with the subterm at `path` made `by`. */
function put(term: Term, path: readonly number[], by: Term): Term {
  const [first, ...rest] = path;

  if (first === undefined || term.kind !== "app") {
    return first === undefined ? by : term;
  }

  return {
    ...term,
    args: term.args.map((arg, index) =>
      index === first ? put(arg, rest, by) : arg,
    ),
  };
}

/** `term` with each subterm the same as `from` made `to` where `choose` says so. */
function swap(term: Term, from: Term, to: Term, choose: () => boolean): Term {
  if (shape(term) === shape(from) && choose()) {
    return to;
  }

  return term.kind === "app"
    ? {
        ...term,
        args: term.args.map((arg) =>
          arg.kind === "variable" && arg.binder
            ? arg
            : swap(arg, from, to, choose),
        ),
      }
    : term;
}

/**
 * Whether a term binds an atom, which is no bound variable; has a bound
 * variable free, which the probe's `r` could not depend on; or holds a
 * probe's own term.
 */
function unfit(
  setup: Setup,
  term: Term,
  bound: ReadonlySet<string> = new Set(),
): boolean {
  if (term.kind === "variable") {
    return !setup.atoms.has(term.name) && !bound.has(term.name);
  }

  if (term.term.startsWith("zz_")) {
    return true;
  }

  let scope = bound;

  return term.args.some((arg) => {
    if (arg.kind === "variable" && arg.binder) {
      scope = new Set([...scope, arg.name]);
      return setup.atoms.has(arg.name);
    }

    return unfit(setup, arg, scope);
  });
}

interface Case {
  readonly a: Term;
  readonly b: Term;
  readonly p: Term;
  readonly q: Term;
  readonly kind: string;
}

function cases(setup: Setup, lang: SurfaceLanguage): Case[] {
  const random = seeded(484);
  const generate = termGenerator(lang, random, setup.atoms);
  const pick = <T>(items: readonly T[]): T | undefined =>
    items[Math.floor(random() * items.length)];
  const found: Case[] = [];
  const kinds = ["every", "some", "none", "changed"] as const;

  while (found.length < TRIALS) {
    const a = generate(setup.plug, random() < 0.7 ? 0 : 1);
    const b = generate(setup.plug, random() < 0.7 ? 0 : 1);
    let p = generate(setup.row, 3);

    if (a === null || b === null || p === null) {
      continue;
    }

    for (let times = Math.floor(random() * 3); times > 0; times -= 1) {
      const site: number[] | undefined = pick(positions(p, setup.plug));
      p = site === undefined ? p : put(p, site, a);
    }

    const kind = kinds[found.length % kinds.length] as (typeof kinds)[number];
    const other = generate(setup.plug, 1);
    const place = pick(positions(p, setup.plug));
    const q =
      kind === "every"
        ? swap(p, a, b, () => true)
        : kind === "some"
          ? swap(p, a, b, () => random() < 0.5)
          : kind === "none"
            ? p
            : other === null || place === undefined
              ? p
              : put(
                  swap(p, a, b, () => true),
                  place,
                  other,
                );

    if (![a, b, p, q].some((term) => unfit(setup, term))) {
      found.push({ a, b, kind, p, q });
    }
  }

  return found;
}

/** The engine's error for each line `zz_show x R`, for its case and `R`; null where it checks. */
function verdicts(
  setup: Setup,
  lang: SurfaceLanguage,
  asked: readonly { readonly one: Case; readonly r: string }[],
): Promise<(string | null)[]> {
  const print = (term: Term) => printTerm(lang, term, "engine");
  const atoms = [...new Set(setup.atoms.values())]
    .map(
      (sort) =>
        `(${[...setup.atoms].flatMap(([name, of]) => (of === sort ? [name] : [])).join(" ")}: ${sort})`,
    )
    .join(" ");

  return probeErrors(
    setup.source,
    "",
    asked.map(({ one, r }) => (name) => {
      const bound = boundVariableBinders(
        [one.a, one.b, one.p, one.q],
        new Set(setup.atoms.keys()),
      );
      const line = `$ zz_show ${HOLE} (${r}) $`;
      const premise = setup.premise(print(one.a), print(one.b));
      const pair = setup.pair(print(one.p), print(one.q));

      return {
        proof: `${name}\n----\nl1: ${line} by ${setup.rule} (x := $ ${HOLE} $) [#1, #2]`,
        statement: `theorem ${name} ${atoms} {${HOLE}: ${setup.hole}}${bound === "" ? "" : ` ${bound}`}: $ ${premise} $ > $ ${pair} $ > ${line};`,
      };
    }),
  );
}

describe("abstractContext against the compiler", () => {
  test.each([LEIBNIZ, NAMES, TERMS])(
    "$name",
    async (setup) => {
      const lang = language(setup);
      const all = cases(setup, lang);
      // As the probe theorems declare them: the atoms regular, depending
      // on nothing, and every other variable bound.
      const variables = new Map(
        [...setup.atoms].map(([name, sort]) => [
          name,
          { bound: false, dependencies: [], sort },
        ]),
      );
      const contexts = all.map((one) =>
        abstractContext(
          lang,
          {
            hole: variable(HOLE, setup.hole),
            left: one.p,
            leftPlug: one.a,
            right: one.q,
            rightPlug: one.b,
          },
          { variables },
        ),
      );
      const print = (term: Term) => printTerm(lang, term, "engine");
      const asked = all.flatMap((one, index) => {
        const context = contexts[index] ?? null;

        return [
          { one, r: "zz_junk" },
          ...(context === null ? [] : [{ one, r: print(context) }]),
        ];
      });
      const answers = await verdicts(setup, lang, asked);
      let next = 0;
      const disagreements: string[] = [];
      let walked = 0;
      let unasked = 0;

      for (const [index, one] of all.entries()) {
        const context = contexts[index] ?? null;
        const junk = answers[next++];
        const theirs = context === null ? null : answers[next++];
        const said = `${one.kind}: ${shape(one.a)} ~ ${shape(one.b)} ⊢ ${shape(one.p)} ~ ${shape(one.q)}`;

        // Junk checks only where the engine's walk recovered nothing, and
        // is a conclusion mismatch where it recovered something. Any other
        // refusal comes before the comparison (normalizing a row that has
        // a step with no `@congr`), and says nothing about the walk.
        if (junk !== null && junk !== "ConclusionMismatch") {
          unasked += 1;
          continue;
        }

        walked += context === null ? 0 : 1;

        if ((junk !== null) !== (context !== null)) {
          disagreements.push(
            `${said}: the engine ${junk !== null ? "recovers" : "finds no"} context, we ${context === null ? "find none" : `recover ${shape(context)}`}`,
          );
        } else if (context !== null && theirs !== null) {
          disagreements.push(
            `${said}: the engine recovers another context than ${shape(context)} (${theirs})`,
          );
        }
      }

      expect(disagreements).toEqual([]);
      // Nearly every case is asked, and both outcomes turn up among them,
      // or the check shows nothing.
      expect(unasked).toBeLessThan(TRIALS / 20);
      expect(walked).toBeGreaterThan(TRIALS / 8);
      expect(walked).toBeLessThan(TRIALS - unasked);
    },
    120_000,
  );
});
