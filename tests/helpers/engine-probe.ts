import type { LoadedCompiler } from "@aufbau/compiler";
import { loadCompiler } from "@aufbau/compiler";
import type { SurfaceLanguage, Term, Variables } from "../../src/index";
import {
  boundVariableBinders,
  printTerm,
  stripSyntaxAnnotations,
} from "../../src/index";
import { rewriteSystem } from "../../src/rewrite";

/**
 * Asking the Aufbau compiler whether it takes two terms for the same.
 *
 * The theory is extended with a probe: a provable sort `zz_probe` with its
 * own `@relation`, and for each sort `s` that has one, a term `zz_in_s` with
 * a `@congr` rule and an axiom `zz_i_s (a: s): $ zz_in_s a $`. Then
 *
 *     l1: $ zz_in_s (B) $ by zz_i_s (a := $ A $)
 *
 * checks only if the engine finds `A` and `B` the same: raw, through defs,
 * or in normal form, wherever it can state the proof. Each pair is its own
 * theorem, so one compile answers many; batches stay small, since the
 * compiler stops reporting refusals past a cap.
 *
 * The theory's own theorems stand as axioms. The probe has no proofs for
 * them, and the engine takes up a theorem's annotations (a `@congr`, a
 * `@rewrite`) only once it has checked its proof; the library reads a
 * theory as one whose theorems are proved.
 */

let compiler: LoadedCompiler | null = null;

export async function engine(): Promise<LoadedCompiler> {
  compiler ??= await loadCompiler();

  return compiler;
}

/** The probe declarations, and the sorts they can probe. */
function probe(lang: SurfaceLanguage): { text: string; sorts: string[] } {
  const lines = [
    "provable sort zz_probe;",
    "term zz_peq (a b: zz_probe): zz_probe;",
    "--| @relation zz_probe zz_peq zz_refl zz_trans zz_symm zz_mp",
    "axiom zz_refl (a: zz_probe): $ zz_peq a a $;",
    "axiom zz_trans (a b c: zz_probe): $ zz_peq a b $ > $ zz_peq b c $ > $ zz_peq a c $;",
    "axiom zz_symm (a b: zz_probe): $ zz_peq a b $ > $ zz_peq b a $;",
    "axiom zz_mp (a b: zz_probe): $ zz_peq a b $ > $ a $ > $ b $;",
  ];
  const sorts: string[] = [];

  for (const [sort, relation] of lang.spec.relations) {
    sorts.push(sort);
    lines.push(
      `term zz_in_${sort} (a: ${sort}): zz_probe;`,
      "--| @congr",
      `axiom zz_c_${sort} (a b: ${sort}): $ ${relation.term} a b $ > $ zz_peq (zz_in_${sort} a) (zz_in_${sort} b) $;`,
      `axiom zz_i_${sort} (a: ${sort}): $ zz_in_${sort} a $;`,
    );
  }

  return { sorts, text: lines.join("\n") };
}

/** The sorts a theory's probe can compare terms of. */
export function probedSorts(lang: SurfaceLanguage): string[] {
  return probe(lang).sorts;
}

export interface ProbePair {
  readonly a: Term;
  readonly b: Term;
  readonly sort: string;
  /**
   * The theorem's binders, in order; a variable not named here is bound
   * (`{x: s}`), as `sameTerm` takes it.
   */
  readonly variables?: Variables;
}

/** A probe theorem's binders: the pair's own, then the rest bound. */
function bindersOf({ a, b, variables = new Map() }: ProbePair): string {
  const declared = [...variables].map(([name, info]) =>
    info.bound
      ? `{${name}: ${info.sort}}`
      : `(${[`${name}:`, info.sort, ...info.dependencies].join(" ")})`,
  );

  return [
    ...declared,
    boundVariableBinders([a, b], new Set(variables.keys())),
  ]
    .filter((binder) => binder !== "")
    .join(" ");
}

/** A probe theorem, given the name it is compiled under. */
export interface ProbeTheorem {
  readonly statement: string;
  readonly proof: string;
}

/**
 * Compile `theorems` against `source`, its theorems standing as axioms,
 * with `extension` declared after it: for each, the error the engine
 * refuses it with, or null where it checks. They are compiled a few at a
 * time, named `zz_t0`, `zz_t1`, … in each batch, since the compiler stops
 * reporting refusals past a cap. A refusal that names no theorem is the
 * probe's own mistake, and throws.
 */
export async function probeErrors(
  source: string,
  extension: string,
  theorems: readonly ((name: string) => ProbeTheorem)[],
): Promise<(string | null)[]> {
  const loaded = await engine();
  const found: (string | null)[] = [];
  const BATCH = 25;

  for (let at = 0; at < theorems.length; at += BATCH) {
    const batch = theorems
      .slice(at, at + BATCH)
      .map((theorem, index) => theorem(`zz_t${index}`));
    const result = loaded.compile(
      [
        stripSyntaxAnnotations(source).replace(
          /^(\s*)(pub\s+)?theorem\b/gm,
          "$1axiom",
        ),
        extension,
        ...batch.map((theorem) => theorem.statement),
      ].join("\n"),
      batch.map((theorem) => theorem.proof).join("\n\n"),
    );
    const errors = (
      (result.diagnostics ?? []) as readonly {
        readonly error?: string;
        readonly severity?: string;
        readonly theorem?: string | null;
      }[]
    ).filter((diagnostic) => diagnostic.severity === "error");
    const stray = errors.filter((diagnostic) => !diagnostic.theorem);

    if (stray.length > 0) {
      throw new Error(`the probe theory failed: ${JSON.stringify(stray)}`);
    }

    batch.forEach((_, index) => {
      found.push(
        errors.find((diagnostic) => diagnostic.theorem === `zz_t${index}`)
          ?.error ?? null,
      );
    });
  }

  return found;
}

/** For each pair, whether the engine takes its terms for the same. */
export async function engineSame(
  lang: SurfaceLanguage,
  source: string,
  pairs: readonly ProbePair[],
): Promise<boolean[]> {
  const errors = await probeErrors(
    source,
    probe(lang).text,
    pairs.map((pair) => (name) => {
      const { a, b, sort } = pair;
      const binders = bindersOf(pair);
      const goal = `$ zz_in_${sort} (${printTerm(lang, b, "engine")}) $`;

      return {
        proof: `${name}\n----\nl1: ${goal} by zz_i_${sort} (a := $ ${printTerm(lang, a, "engine")} $)`,
        statement: `theorem ${name}${binders === "" ? "" : ` ${binders}`}: ${goal};`,
      };
    }),
  );

  return errors.map((error) => error === null);
}

const SPAN = { end: 0, start: 0 } as const;

function app(term: string, sort: string, args: Term[]): Term {
  return {
    args,
    fixity: null,
    grouped: false,
    kind: "app",
    prec: null,
    sort,
    span: SPAN,
    term,
    token: null,
  };
}

/**
 * `term` with each bag of an `@acui` combiner shuffled where it commutes,
 * regrouped, given a unit where both unit laws hold, and a repeat where it
 * is idempotent: what the laws say is the same term.
 */
export function scramble(
  lang: SurfaceLanguage,
  term: Term,
  random: () => number,
): Term {
  if (term.kind !== "app") {
    return term;
  }

  const combiner = rewriteSystem(lang).combiners.get(term.term);

  if (combiner === undefined || term.args.length !== 2) {
    return {
      ...term,
      args: term.args.map((arg) => scramble(lang, arg, random)),
    };
  }

  const leaves: Term[] = [];
  const collect = (node: Term): void => {
    if (
      node.kind === "app" &&
      node.term === combiner.term &&
      node.args.length === 2
    ) {
      node.args.forEach(collect);
    } else {
      leaves.push(scramble(lang, node, random));
    }
  };

  collect(term);

  if (combiner.commutative) {
    for (let at = leaves.length - 1; at > 0; at -= 1) {
      const other = Math.floor(random() * (at + 1));
      const [left, right] = [leaves[at] as Term, leaves[other] as Term];

      leaves[at] = right;
      leaves[other] = left;
    }
  }

  if (combiner.leftUnit && combiner.rightUnit && random() < 0.5) {
    leaves.splice(
      Math.floor(random() * (leaves.length + 1)),
      0,
      app(combiner.unit, term.sort, []),
    );
  }

  if (combiner.idempotent && random() < 0.5) {
    leaves.push(leaves[Math.floor(random() * leaves.length)] as Term);
  }

  const build = (items: readonly Term[]): Term => {
    if (items.length === 1) {
      return items[0] as Term;
    }

    const cut = 1 + Math.floor(random() * (items.length - 1));

    return app(combiner.term, term.sort, [
      build(items.slice(0, cut)),
      build(items.slice(cut)),
    ]);
  };

  return build(leaves);
}

/** `term` with one subterm, never a bound slot, replaced by another of its sort. */
export function mutate(
  term: Term,
  generate: (sort: string, depth: number) => Term | null,
  random: () => number,
): Term {
  const nodes: Term[] = [];
  const collect = (node: Term): void => {
    nodes.push(node);

    if (node.kind === "app") {
      for (const arg of node.args) {
        if (!(arg.kind === "variable" && arg.binder)) {
          collect(arg);
        }
      }
    }
  };

  collect(term);

  const target = nodes[Math.floor(random() * nodes.length)] as Term;
  const replacement = generate(target.sort, 1) ?? target;
  const rebuild = (node: Term): Term =>
    node === target
      ? replacement
      : node.kind === "app"
        ? { ...node, args: node.args.map(rebuild) }
        : node;

  return rebuild(term);
}
