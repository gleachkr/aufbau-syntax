/**
 * The theory's rewrite system, read once per language: what the engine's
 * normalizer reasons modulo, as `normal.ts` uses it.
 *
 * - A `@rewrite` axiom or theorem concludes `rel lhs rhs`, `rel` the
 *   `@relation` term of its sort, with no hypotheses. Rules are indexed by
 *   the head of `lhs` and kept in declaration order, the order the engine
 *   tries them in.
 * - A `@congr` rule lifts a step on a term's arguments to the term:
 *   `rel (f a1 a2 …) (f b1 b2 …)` over before/after pairs of its regular
 *   arguments, its bound ones once. The engine keeps the last for a term.
 *   Without one, the engine can state no step inside the term, so it
 *   cannot normalize there; `normal.ts` tracks that.
 * - An `@acui` combiner takes part once its sort has a `@relation` and its
 *   associativity law is declared. Commutativity and idempotence count
 *   where their laws are declared too. A unit is dropped only on a side
 *   where a declared rule states the unit law. No annotation names those
 *   rules: the engine finds them by their shape, `rel (f e a) a` or `rel
 *   (f a e) a` (either way round), with one regular binder of the sort and
 *   no hypotheses, and so does this module.
 *
 * Like the engine, nothing here checks that a law is true, or that it has
 * the shape `@acui` cites it at. The engine refuses a file whose laws are
 * misshapen; this module reads what such a file would mean.
 */

import type { SurfaceLanguage } from "./parse.js";
import type { AssertStatement, Binder } from "./reader/statements.js";
import { parseStatement } from "./statement.js";
import type { Term } from "./term.js";

/** How a variable takes part in the dependency check. */
export interface VariableInfo {
  readonly sort: string;
  /** A `{x: s}` binder: a variable a quantifier can bind. */
  readonly bound: boolean;
  /** The bound variables a regular one may depend on; empty for a bound one. */
  readonly dependencies: readonly string[];
}

/** One binder of a rule, as the dependency check reads it. */
export interface RuleBinder extends VariableInfo {
  readonly name: string;
}

/** An oriented `@rewrite`: `lhs` becomes `rhs`, over the rule's binders. */
export interface RewriteRule {
  readonly name: string;
  readonly binders: readonly RuleBinder[];
  readonly lhs: Term;
  readonly rhs: Term;
}

/** An `@acui` combiner the normalizer acts on, with the laws it can use. */
export interface Combiner {
  readonly term: string;
  /** The sort of its bags, its members and its unit. */
  readonly sort: string;
  readonly unit: string;
  readonly commutative: boolean;
  readonly idempotent: boolean;
  /** Whether `unit ; a` becomes `a`: a left unit law, or a right one and commutativity. */
  readonly leftUnit: boolean;
  /** Whether `a ; unit` becomes `a`. */
  readonly rightUnit: boolean;
}

export interface RewriteSystem {
  /** By the head of their left side, in declaration order. */
  readonly rewrites: ReadonlyMap<string, readonly RewriteRule[]>;
  /** Each term's `@congr` rule, by its binders. */
  readonly congruences: ReadonlyMap<string, readonly RuleBinder[]>;
  /** Each term's place in declaration order. */
  readonly termOrder: ReadonlyMap<string, number>;
  /** By the combiner term. */
  readonly combiners: ReadonlyMap<string, Combiner>;
  /** By the sort of its bags: the one combiner of that sort, or null for two. */
  readonly combinersBySort: ReadonlyMap<string, Combiner | null>;
}

const systems = new WeakMap<SurfaceLanguage, RewriteSystem>();

/** The rewrite system of a language's theory, read once. */
export function rewriteSystem(lang: SurfaceLanguage): RewriteSystem {
  let system = systems.get(lang);

  if (system === undefined) {
    system = readSystem(lang);
    systems.set(lang, system);
  }

  return system;
}

// Unlike `statementVariables`, a rule's `_` and dot-dummy binders are
// read as written: they are arguments the dependency check sees.
function ruleBinders(binders: readonly Binder[]): RuleBinder[] {
  const read: RuleBinder[] = [];

  for (const binder of binders) {
    if ("sort" in binder.type) {
      read.push({
        bound: binder.binds,
        dependencies: binder.binds ? [] : binder.type.dependencies,
        name: binder.name,
        sort: binder.type.sort,
      });
    }
  }

  return read;
}

/** A rule's conclusion, read in its scope; null where it does not read. */
function conclusionOf(
  lang: SurfaceLanguage,
  statement: AssertStatement,
): Term | null {
  const result = parseStatement(lang, statement).conclusion.result;

  return result.ok ? result.term : null;
}

/** Whether a rule has hypotheses: hypothesis binders, or formulas in its chain. */
function hasHypotheses(statement: AssertStatement): boolean {
  return (
    statement.binders.some((binder) => "text" in binder.type) ||
    statement.hypotheses.some((hypothesis) => "text" in hypothesis)
  );
}

function annotated(statement: AssertStatement, head: string): boolean {
  return statement.annotations.some(
    (annotation) => annotation.text.trim().split(/\s+/)[0] === head,
  );
}

function readSystem(lang: SurfaceLanguage): RewriteSystem {
  const spec = lang.spec;
  const relationTerms = new Set(
    [...spec.relations.values()].map((relation) => relation.term),
  );
  const rewrites = new Map<string, RewriteRule[]>();
  const congruences = new Map<string, readonly RuleBinder[]>();
  const leftUnits = new Set<string>();
  const rightUnits = new Set<string>();
  // The `@acui` terms whose sort has a relation, with its term.
  const candidates = [...spec.terms.values()].flatMap((info) => {
    const relation = spec.relations.get(info.returnSort);

    return info.acui === null || relation === undefined
      ? []
      : [{ acui: info.acui, info, relation: relation.term }];
  });

  for (const statement of spec.statements) {
    if (statement.kind !== "axiom" && statement.kind !== "theorem") {
      continue;
    }

    const congr = annotated(statement, "@congr");
    // Only a hypothesis-free rule can be a rewrite or a unit law.
    const plain = !hasHypotheses(statement);
    const rewrite = plain && annotated(statement, "@rewrite");

    if (!congr && !rewrite && (!plain || candidates.length === 0)) {
      continue;
    }

    const conclusion = conclusionOf(lang, statement);

    if (
      conclusion === null ||
      conclusion.kind !== "app" ||
      conclusion.args.length !== 2 ||
      !relationTerms.has(conclusion.term)
    ) {
      continue;
    }

    const [lhs, rhs] = conclusion.args as [Term, Term];
    const binders = ruleBinders(statement.binders);

    if (
      congr &&
      lhs.kind === "app" &&
      rhs.kind === "app" &&
      lhs.term === rhs.term
    ) {
      congruences.set(lhs.term, binders);
    }

    if (!plain) {
      continue;
    }

    if (rewrite && lhs.kind === "app") {
      const rule = { binders, lhs, name: statement.name, rhs };
      rewrites.set(lhs.term, [...(rewrites.get(lhs.term) ?? []), rule]);
    }

    for (const { acui, info, relation } of candidates) {
      if (conclusion.term !== relation) {
        continue;
      }

      const side = unitLawSide(info.name, acui.unit, binders, lhs, rhs);

      if (side === "left") {
        leftUnits.add(info.name);
      } else if (side === "right") {
        rightUnits.add(info.name);
      }
    }
  }

  const combiners = new Map<string, Combiner>();
  const combinersBySort = new Map<string, Combiner | null>();

  for (const { acui, info } of candidates) {
    if (!spec.rules.has(acui.assoc)) {
      continue;
    }

    const commutative = acui.comm !== null && spec.rules.has(acui.comm);
    const left = leftUnits.has(info.name);
    const right = rightUnits.has(info.name);

    const combiner: Combiner = {
      commutative,
      idempotent: acui.idem !== null && spec.rules.has(acui.idem),
      leftUnit: left || (commutative && right),
      rightUnit: right || (commutative && left),
      sort: info.returnSort,
      term: info.name,
      unit: acui.unit,
    };

    combiners.set(info.name, combiner);
    combinersBySort.set(
      combiner.sort,
      combinersBySort.has(combiner.sort) ? null : combiner,
    );
  }

  const termOrder = new Map<string, number>();

  [...spec.terms.keys()].forEach((name, at) => {
    termOrder.set(name, at);
  });

  return { combiners, combinersBySort, congruences, rewrites, termOrder };
}

/**
 * Which side's unit law a rule states, if it states one: one regular
 * binder `a` of the combiner's sort, and `f e a ~ a` or `f a e ~ a`, either
 * side first.
 */
function unitLawSide(
  combiner: string,
  unit: string,
  binders: readonly RuleBinder[],
  lhs: Term,
  rhs: Term,
): "left" | "right" | null {
  const [only, ...rest] = binders;

  if (only === undefined || rest.length > 0 || only.bound) {
    return null;
  }

  const isA = (term: Term): boolean =>
    term.kind === "variable" && term.name === only.name;
  const isUnit = (term: Term): boolean =>
    term.kind === "app" && term.term === unit && term.args.length === 0;
  const [combined, bare] = isA(rhs) ? [lhs, rhs] : [rhs, lhs];

  if (
    !isA(bare) ||
    combined.kind !== "app" ||
    combined.term !== combiner ||
    combined.args.length !== 2 ||
    combined.sort !== only.sort
  ) {
    return null;
  }

  const [first, second] = combined.args as [Term, Term];

  if (isUnit(first) && isA(second)) {
    return "left";
  }

  return isA(first) && isUnit(second) ? "right" : null;
}
