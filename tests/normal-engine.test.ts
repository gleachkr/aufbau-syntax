import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import type { Term, VariableInfo, Variables } from "../src/index";
import {
  normalTerm,
  parseSpec,
  printTerm,
  RewriteLimitError,
  SurfaceLanguage,
  sameTerm,
  termKey,
  unfoldDefinitions,
  walkTerm,
} from "../src/index";
import type { ProbePair } from "./helpers/engine-probe";
import {
  engineSame,
  mutate,
  probedSorts,
  scramble,
} from "./helpers/engine-probe";
import { CORPUS_DIR } from "./helpers/mm0-corpus";
import { seeded, termGenerator } from "./helpers/terms";

/**
 * The differential check: on random terms of each theory, `sameTerm` says
 * what the Aufbau compiler says (`./helpers/engine-probe.ts` asks it).
 *
 * The pairs are a term against its normal form, its bags scrambled, its
 * defs unfolded, one subterm changed, a stranger of its sort, and any
 * other term that happened to get its key. Some of each pair's variables
 * are regular, depending on some of the bound ones, so the dependency
 * checks are tried both ways. Carnap's theories and the corpus agree
 * exactly, but for the pairs a theory lists as `known`, which must still
 * turn up.
 */

/** The one pair the engine's semantic search decides (see `martin_lof` below). */
const KNOWN_MARTIN_LOF =
  "we accept at tm: id_sym (Id (Π ih : Bool . Nat) (suc_fn) (⟦ n / w ⟧ p)) (w) (transport (Id (Nat) (false) (zero)) x (Π m : Nat . Nat) (false) (true) (n) (w)) (m)  vs  J u v q (Id (Π ih : Bool . Nat) (λ k : Nat . (suc (k))) (p)) (Id (Id (Π ih : Bool . Nat) (λ k : Nat . (suc (k))) (p)) (v) (u)) (refl (Id (Π ih : Bool . Nat) (λ k : Nat . (suc (k))) (p)) (u)) (w) ((J x y q (Id (Nat) (false) (zero)) (Π z : (Π m : Nat . Nat) . ([ x / y ] (Π m : Nat . Nat))) (λ z : (Π m : Nat . Nat) . z) (false) (true) (n)) · w) (m)";

const CARNAP = new URL("./fixtures/carnap/", import.meta.url).pathname;

interface Theory {
  readonly name: string;
  /** Its files, joined in order: a Carnap system can be a base and fragments. */
  readonly parts: readonly string[];
  /** Disagreements that are understood, as the test prints them. */
  readonly known?: readonly string[];
}

const THEORIES: readonly Theory[] = [
  ...[
    "forallx-ubc",
    "forallx-calgary",
    "forallx-magnus",
    "gentzen-lk",
    "open-logic-tableaux",
    "open-logic-intuitionistic",
    "open-logic-modal-k",
    "open-logic-simple-s5",
  ].map((name) => ({ name, parts: [`${CARNAP}${name}.mm0`] })),
  // Carnap's `-plus` systems and the modal logics past K, put together as
  // Carnap's `theories/index.ts` puts them.
  ...["forallx-calgary", "forallx-magnus"].map((name) => ({
    name: `${name}-plus`,
    parts: [`${CARNAP}${name}.mm0`, `${CARNAP}derived/${name}.mm0`],
  })),
  ...Object.entries({
    "open-logic-modal-b": ["t", "b"],
    "open-logic-modal-d": ["d"],
    "open-logic-modal-s5": ["t", "4", "4r"],
  }).map(([name, fragments]) => ({
    name,
    parts: [
      `${CARNAP}open-logic-modal-k.mm0`,
      ...fragments.map((fragment) => `${CARNAP}modal/${fragment}.mm0`),
    ],
  })),
  ...[
    "aufbau-fol",
    "aufbau-lam",
    "barcan",
    "cardano",
    "commutative_ring",
    "diaconescu",
    "euclid",
    "gentzen",
    "girard",
    "hilbert_quant",
    "hoare",
    "leibniz",
    "mac_lane",
    "mltt",
    "peano",
    "pratt",
    "prawitz",
    "radical_ring",
    "reynolds",
    "robinson",
    "smullyan",
    "tait",
    "tseitin",
    "zermelo",
    "zermelo_hilbert",
  ].map((name) => ({ name, parts: [`${CORPUS_DIR}/${name}.mm0`] })),
  {
    // A binder reused inside its own scope (`Π x : (… nat_ind x …)`) makes
    // normalizing the inner term lift through a congruence whose argument
    // may not mention `x`. Both sides poison that rung. The engine's
    // bounded semantic search, which this library does not follow, then
    // opens a def toward the normal form through a rewrite, so its rung
    // succeeds and the line is refused; here the rung finds no common
    // target, and a later one accepts the line.
    known: [KNOWN_MARTIN_LOF],
    name: "martin_lof",
    parts: [`${CORPUS_DIR}/martin_lof.mm0`],
  },
];

const TERMS_PER_SORT = 24;
const DEPTH = 3;

/**
 * A pair's variables in the order the probe declares them: the bound ones
 * first, then about a third of those no quantifier binds made regular,
 * each depending on some of the bound ones (none, in a `free` sort).
 */
function variablesOf(
  lang: SurfaceLanguage,
  a: Term,
  b: Term,
  random: () => number,
): Variables {
  const seen = new Map<string, { sort: string; binds: boolean }>();

  for (const term of [a, b]) {
    walkTerm(term, (node) => {
      if (node.kind === "variable") {
        const found = seen.get(node.name);

        seen.set(node.name, {
          binds: (found?.binds ?? false) || node.binder,
          sort: node.sort,
        });
      }
    });
  }

  const bound: [string, VariableInfo][] = [];
  const regular: [string, string][] = [];

  for (const [name, { binds, sort }] of seen) {
    if (!binds && random() < 1 / 3) {
      regular.push([name, sort]);
    } else {
      bound.push([name, { bound: true, dependencies: [], sort }]);
    }
  }

  return new Map([
    ...bound,
    ...regular.map(([name, sort]): [string, VariableInfo] => [
      name,
      {
        bound: false,
        dependencies: lang.spec.sorts.get(sort)?.modifiers.includes("free")
          ? []
          : bound.map(([one]) => one).filter(() => random() < 1 / 2),
        sort,
      },
    ]),
  ]);
}

function pairsOf(lang: SurfaceLanguage, seed: number): ProbePair[] {
  const random = seeded(seed);
  // Its own stream, so the terms are the ones the seed has always made.
  const choose = seeded(seed + 1);
  const generate = termGenerator(lang, random);
  const pairs: ProbePair[] = [];
  const pair = (a: Term, b: Term, sort: string): ProbePair => ({
    a,
    b,
    sort,
    variables: variablesOf(lang, a, b, choose),
  });

  for (const sort of probedSorts(lang)) {
    const terms: Term[] = [];

    for (let made = 0; made < TERMS_PER_SORT; made += 1) {
      const term = generate(sort, DEPTH);

      if (term !== null) {
        terms.push(term);
      }
    }

    const byKey = new Map<string, Term>();

    for (const [at, term] of terms.entries()) {
      let normal: Term;

      try {
        normal = normalTerm(lang, term);
      } catch (error) {
        if (error instanceof RewriteLimitError) {
          continue;
        }

        throw error;
      }

      const key = termKey(lang, term);
      const twin = byKey.get(key);

      if (twin === undefined) {
        byKey.set(key, term);
      } else {
        pairs.push(pair(twin, term, sort));
      }

      for (const b of [
        normal,
        scramble(lang, term, random),
        scramble(lang, normal, random),
        unfoldDefinitions(lang, normal),
        mutate(term, generate, random),
        mutate(normal, generate, random),
        terms[(at + 1) % terms.length] as Term,
      ]) {
        pairs.push(pair(term, b, sort));
      }
    }
  }

  return pairs;
}

describe("sameTerm agrees with the Aufbau compiler", () => {
  for (const theory of THEORIES) {
    test(theory.name, async () => {
      const source = theory.parts
        .map((part) => readFileSync(part, "utf8"))
        .join("\n");
      const lang = new SurfaceLanguage(parseSpec(source).spec);
      const pairs = pairsOf(lang, 7);
      const engine = await engineSame(lang, source, pairs);
      const known = new Set(theory.known ?? []);
      const wrong: string[] = [];
      const seen = new Set<string>();

      pairs.forEach((pair, at) => {
        const ours = sameTerm(lang, pair.a, pair.b, {
          variables: pair.variables ?? new Map(),
        });

        if (ours === engine[at]) {
          return;
        }

        const line = `${ours ? "we accept" : "we refuse"} at ${pair.sort}: ${printTerm(lang, pair.a, "engine")}  vs  ${printTerm(lang, pair.b, "engine")}`;

        if (known.has(line)) {
          seen.add(line);
        } else {
          wrong.push(line);
        }
      });

      expect(pairs.length).toBeGreaterThan(0);
      expect(wrong).toEqual([]);
      expect([...known].filter((line) => !seen.has(line))).toEqual([]);
    }, 60_000);
  }
});
