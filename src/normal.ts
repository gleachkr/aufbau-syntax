/**
 * Terms modulo the theory's rewrites, `@acui` laws and defs: the normal
 * form the engine reasons with, and whether the engine takes two terms
 * for the same.
 *
 * The normal form is the engine's own, with defs left folded
 * (`normalizer.ts` says how it is reached). Identity is the engine's
 * decision when it checks a line against what a rule derives
 * (`conversion.ts`): through defs, through normal forms where it can
 * state the proof, and through the common targets it searches for
 * between them. It is a relation between two terms, not a property of
 * each, so {@link termKey} gives a key that implies it rather than one
 * that decides it.
 *
 * The differential tests against the compiler
 * (`tests/normal-engine.test.ts`) say, theory by theory, where the two
 * still disagree.
 */

import { Conversion } from "./conversion.js";
import type { Node, Normalizer, Variables } from "./normalizer.js";
import { Unstatable } from "./normalizer.js";
import type { SurfaceLanguage } from "./parse.js";
import type { AssertStatement, DefStatement } from "./reader/statements.js";
import type { Term } from "./term.js";

export type { VariableInfo, Variables } from "./normalizer.js";
export { RewriteLimitError, Unstatable } from "./normalizer.js";

export interface NormalOptions {
  /**
   * The variables of the statement the term belongs to. A variable not
   * named here is taken as bound, depending on nothing but itself, as
   * {@link boundVariableBinders} would declare it.
   */
  readonly variables?: Variables;
}

/**
 * A statement's binders as variables: `{x: s}` bound, `(a: s x)` regular
 * with its dependencies. A def's dot-dummies are bound.
 */
export function statementVariables(
  statement: AssertStatement | DefStatement,
): Variables {
  const variables = new Map<
    string,
    { bound: boolean; dependencies: readonly string[]; sort: string }
  >();

  for (const binder of statement.binders) {
    if ("sort" in binder.type && binder.name !== "_") {
      const bound = binder.binds || binder.dummy;

      variables.set(binder.name, {
        bound,
        dependencies: bound ? [] : binder.type.dependencies,
        sort: binder.type.sort,
      });
    }
  }

  return variables;
}

// Each call builds its own conversion and normalizer: their memo tables
// hold every term they meet, so they live no longer than the request.

/**
 * `term`'s normal form under the theory's rewrites and `@acui` laws, with
 * its defs left folded. Throws {@link RewriteLimitError} where the rules
 * do not terminate, and {@link Unstatable} where folding a member into a
 * def would leave one of the def's dot-dummies without a witness, as the
 * engine's normalizer gives up there too.
 *
 * It goes as far as the rules go, which can be further than the engine
 * can prove its way (a rewrite under a term with no `@congr`), and there
 * the engine compares the term as written. {@link engineForm} is the
 * form the engine compares.
 */
export function normalTerm(
  lang: SurfaceLanguage,
  term: Term,
  options: NormalOptions = {},
): Term {
  const { n } = new Conversion(lang, options.variables);

  return n.toTerm(n.normalize(n.intern(term)));
}

/**
 * `term` as the engine compares it: its normal form where the engine can
 * prove its way there, and the term as written otherwise (a sort with no
 * `@relation`, a rewrite under a term with no `@congr`, a def's dot-dummy
 * left without a witness). {@link termKey} is its key. Throws
 * {@link RewriteLimitError} where the rules do not terminate.
 */
export function engineForm(
  lang: SurfaceLanguage,
  term: Term,
  options: NormalOptions = {},
): Term {
  const { n } = new Conversion(lang, options.variables);
  const node = n.intern(term);
  const normal = comparedNode(n, node);

  return normal === null ? term : n.toTerm(normal);
}

/**
 * A key for `term`: two terms with one key are ones the engine takes for
 * the same, as long as their two normalizations together stay within the
 * engine's thousand steps (which it counts across both sides of a line).
 * It is the key of {@link engineForm}, marked where that is the term as
 * written. Terms with different keys may still be the same to the engine,
 * through their defs or a common target; {@link sameTerm} decides that.
 * Throws {@link RewriteLimitError} where the rules do not terminate.
 */
export function termKey(
  lang: SurfaceLanguage,
  term: Term,
  options: NormalOptions = {},
): string {
  const { n } = new Conversion(lang, options.variables);
  const node = n.intern(term);
  const normal = comparedNode(n, node);

  return normal === null ? `!${n.keyOf(node)}` : n.keyOf(normal);
}

/** `node`'s normal form where the engine can prove its way there; null where it compares `node` as written. */
function comparedNode(n: Normalizer, node: Node): Node | null {
  try {
    return n.hasRelation(node.sort) && n.stated(node)
      ? n.normalize(node)
      : null;
  } catch (error) {
    // No proof reaches a normal form there.
    if (error instanceof Unstatable) {
      return null;
    }

    throw error;
  }
}

/**
 * Whether the engine takes a statement it has derived, `derived`, for the
 * one a line states, `stated`: whether it accepts the line. The relation
 * is the engine's, so it need not be symmetric. Throws
 * {@link RewriteLimitError} where the engine would report that the rules
 * do not terminate.
 */
export function sameTerm(
  lang: SurfaceLanguage,
  derived: Term,
  stated: Term,
  options: NormalOptions = {},
): boolean {
  const conversion = new Conversion(lang, options.variables);

  return conversion.converts(
    conversion.n.intern(derived),
    conversion.n.intern(stated),
  );
}
