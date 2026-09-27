import type { Binder, SurfaceLanguage, Term } from "../../src/index";

/**
 * Well-sorted terms over a spec, generated at random from a seed: the
 * printer's whole domain, not just the trees some parse happens to have
 * produced. Coercions are inserted where a sort needs one, bound slots
 * take a variable from the binder sort's `@vars` pool, and the other
 * variables come from the same pools — or from a `scope`, the names a
 * theorem binds, for a theory whose formulas are all schematic and so
 * has no closed terms at all.
 *
 * An `@syntax elided` term is generated only where it is elided — the
 * sole argument of a name application — since that is the only place it
 * has a spelling (see the round-trip test).
 */

const SPAN = { start: 0, end: 0 } as const;

/** A small deterministic generator, so a failure names its seed. */
export function seeded(seed: number): () => number {
  let state = seed;

  return () => {
    state = (state * 1103515245 + 12345) & 0x7fffffff;
    return state / 0x7fffffff;
  };
}

function variable(name: string, sort: string, binder: boolean): Term {
  return { kind: "variable", name, sort, span: SPAN, grouped: false, binder };
}

function application(term: string, args: Term[], sort: string): Term {
  return {
    kind: "app",
    term,
    args,
    sort,
    span: SPAN,
    grouped: false,
    fixity: null,
    prec: null,
    token: null,
  };
}

function sortOf(binder: Binder): string | null {
  return "sort" in binder.type ? binder.type.sort : null;
}

/** Constructor applications one generated term may spend. */
const NODE_BUDGET = 60;

type Option = { readonly cost: number; readonly build: () => Term };

/**
 * A term generator for `lang`: `generate(sort, depth)` returns a random
 * term of that sort — no deeper than `depth` constructor applications,
 * where the sort allows it — or null when nothing builds the sort at all.
 *
 * Each sort's shallowest possible term is found first, as a fixpoint, so
 * the generator only ever picks an option that can finish: no retries,
 * which in a theory where most constructors need arguments grow
 * exponentially. Once a term has spent {@link NODE_BUDGET} applications it
 * takes the cheapest option everywhere, which keeps it finite in width too.
 */
export function termGenerator(
  lang: SurfaceLanguage,
  random: () => number,
  scope: ReadonlyMap<string, string> = new Map(),
): (sort: string, depth: number) => Term | null {
  const spec = lang.spec;
  const pick = <T>(items: readonly T[]): T | undefined =>
    items[Math.floor(random() * items.length)];
  const pools = new Map<string, string[]>();

  for (const [name, sort] of scope) {
    pools.set(sort, [...(pools.get(sort) ?? []), name]);
  }

  const vars = (sort: string): readonly string[] => [
    ...(spec.sorts.get(sort)?.vars ?? []),
    ...(pools.get(sort) ?? []),
  ];

  // A constructor is buildable when every binder has a sort, and every
  // bound one a variable to fill it.
  const makers = [...spec.terms.values()].filter(
    (info) =>
      !info.elided &&
      !lang.coercionNames.has(info.name) &&
      info.binders.every((binder) => {
        const bound = sortOf(binder);

        return bound !== null && (!binder.binds || vars(bound).length > 0);
      }),
  );
  const regularSorts = (info: (typeof makers)[number]): string[] =>
    info.binders
      .filter((binder) => !binder.binds)
      .map((binder) => sortOf(binder) ?? "");

  // The shallowest term of each sort: a variable or a nullary constructor
  // is depth 0, a constructor one more than its deepest argument's
  // shallowest, a coercion the same as what it wraps.
  const shallowest = new Map<string, number>();
  const least = (sort: string): number =>
    shallowest.get(sort) ?? Number.POSITIVE_INFINITY;
  const costOf = (info: (typeof makers)[number]): number => {
    const args = regularSorts(info);

    return args.length === 0 ? 0 : 1 + Math.max(...args.map(least));
  };

  for (let changed = true; changed; ) {
    changed = false;

    for (const sort of spec.sorts.keys()) {
      let best = vars(sort).length > 0 ? 0 : least(sort);

      for (const info of makers) {
        if (info.returnSort === sort) {
          best = Math.min(best, costOf(info));
        }
      }

      for (const coercion of spec.coercions) {
        if (coercion.to === sort) {
          best = Math.min(best, least(coercion.from));
        }
      }

      if (best < least(sort)) {
        shallowest.set(sort, best);
        changed = true;
      }
    }
  }

  let budget = 0;

  const generate = (
    sort: string,
    depth: number,
    through: ReadonlySet<string>,
  ): Term => {
    budget -= 1;

    const options: Option[] = [];

    for (const name of vars(sort)) {
      options.push({ cost: 0, build: () => variable(name, sort, false) });
    }

    for (const info of makers) {
      if (info.returnSort !== sort) {
        continue;
      }

      const regular = regularSorts(info);

      options.push({
        cost: costOf(info),
        build: () =>
          application(
            info.name,
            info.binders.map((binder) => {
              const bound = sortOf(binder) ?? "";

              if (binder.binds) {
                return variable(pick(vars(bound)) ?? "", bound, true);
              }

              // Where the parser would supply the sort's elided term,
              // write it now and then; that is the one place it is
              // printable.
              const elided = lang.elidedOf.get(bound);

              if (
                elided !== undefined &&
                regular.length === 1 &&
                random() < 0.3
              ) {
                return application(elided.name, [], bound);
              }

              return generate(bound, depth - 1, new Set());
            }),
            sort,
          ),
      });
    }

    for (const coercion of spec.coercions) {
      if (coercion.to === sort && !through.has(coercion.from)) {
        options.push({
          cost: least(coercion.from),
          build: () =>
            application(
              coercion.name,
              [generate(coercion.from, depth, new Set([...through, sort]))],
              sort,
            ),
        });
      }
    }

    // Within the depth, or — once the budget is spent, or the depth is
    // too shallow for this sort — only the cheapest.
    const floor = Math.min(...options.map((option) => option.cost));
    const reach = budget > 0 ? Math.max(depth, floor) : floor;
    const option = pick(
      options.filter((candidate) => candidate.cost <= reach),
    );

    if (option === undefined) {
      throw new Error(`no term of sort ${sort} can be built`);
    }

    return option.build();
  };

  return (sort, depth) => {
    if (!Number.isFinite(least(sort))) {
      return null;
    }

    budget = NODE_BUDGET;
    return generate(sort, depth, new Set());
  };
}
