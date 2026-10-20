/**
 * Reading an assertion's own formulas, and what its binders do to the
 * language they are read in.
 *
 * An axiom's or theorem's math strings are engine text over its binders:
 * `axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $` means nothing outside
 * `(a b: wff)`, and inside it `a` is a variable of sort `wff` whatever the
 * lexicon says `a` is. This module reads them that way, and says which
 * binders displace a meaning the language had given their name.
 */

import type { ParseResult, SurfaceLanguage } from "./parse.js";
import type {
  AssertStatement,
  DefStatement,
  MathString,
} from "./reader/statements.js";
import type { Scope } from "./scan.js";
import { surfaceVocabulary } from "./vocabulary.js";

/**
 * A statement's binders, name to sort: the scope its math strings are read
 * in. A hypothesis binder (`(h: $ … $)`) carries a formula, not a sort,
 * and an anonymous one (`_`) has no name to bind, so neither is in it. A
 * def's dot-dummies are, since its definiens names them.
 */
export function statementScope(
  statement: AssertStatement | DefStatement,
): Scope {
  const scope = new Map<string, string>();

  for (const binder of statement.binders) {
    if ("sort" in binder.type && binder.name !== "_") {
      scope.set(binder.name, binder.type.sort);
    }
  }

  return scope;
}

/** One of a statement's math strings, and how it read. */
export interface StatementFormula {
  readonly formula: MathString;
  readonly result: ParseResult;
}

/** An assertion's formulas, each read in engine mode in its scope. */
export interface StatementReading {
  /**
   * In the order the engine numbers them for citation: the hypothesis
   * binders, then the formulas of the `>`-chain. A type in the chain is an
   * anonymous binder, not a hypothesis, and is not among them.
   */
  readonly hypotheses: readonly StatementFormula[];
  readonly conclusion: StatementFormula;
  readonly scope: Scope;
}

/**
 * Read every formula of an axiom or theorem as the engine reads it:
 * engine mode, in the statement's own binder scope, without lints.
 *
 * MM0 gives an assertion's formula no sort of its own beyond "a provable
 * one", so without `sort` each is read at the first provable sort that
 * takes it, in declaration order (every sort, in a file that marks none),
 * and a failure reports that first sort's complaint. A caller that knows
 * what it is reading — a proof system's judgement sort — names it, and a
 * formula of any other sort is refused.
 */
export function parseStatement(
  language: SurfaceLanguage,
  statement: AssertStatement,
  options: { readonly sort?: string } = {},
): StatementReading {
  const scope = statementScope(statement);
  const sorts =
    options.sort === undefined ? assertableSorts(language) : [options.sort];
  const read = (formula: MathString): StatementFormula => ({
    formula,
    result: readAtSorts(language, formula.text, scope, sorts),
  });
  const hypotheses: StatementFormula[] = [];

  for (const binder of statement.binders) {
    if ("text" in binder.type) {
      hypotheses.push(read(binder.type));
    }
  }

  for (const hypothesis of statement.hypotheses) {
    if ("text" in hypothesis) {
      hypotheses.push(read(hypothesis));
    }
  }

  return { conclusion: read(statement.conclusion), hypotheses, scope };
}

/** mm0.md: "All formulas appearing in axioms and theorems … must have a
 *  provable sort." */
function assertableSorts(language: SurfaceLanguage): readonly string[] {
  const sorts = [...language.spec.sorts.values()];
  const provable = sorts.filter((sort) =>
    sort.modifiers.includes("provable"),
  );

  return (provable.length > 0 ? provable : sorts).map((sort) => sort.name);
}

function readAtSorts(
  language: SurfaceLanguage,
  text: string,
  scope: Scope,
  sorts: readonly string[],
): ParseResult {
  let first: ParseResult | null = null;

  for (const sort of sorts) {
    const result = language.parse(text, { mode: "engine", scope, sort });

    if (result.ok) {
      return result;
    }

    first ??= result;
  }

  return first ?? { diagnostics: [], ok: false };
}

/** What a binder pushed aside, which decides how a warning is worded. */
export type BinderShadowKind = "notation" | "term" | "variable";

/** One binder whose name the language already gave another meaning. */
export interface BinderShadow {
  /** For `variable`, the sort of the `@vars` pool the name is in. */
  readonly displacedSort?: string;
  readonly kind: BinderShadowKind;
  readonly name: string;
  /** The binder's own sort. */
  readonly sort: string;
}

/**
 * The binders in `scope` that displace a meaning the language gave their
 * name — a lint for whoever wrote the statement, since inside its scope the
 * name reads as the binder (see `SurfaceLanguage.parse`) and the other
 * meaning is gone.
 *
 * - `notation`: the name is a notation token, a grouping bracket, or an
 *   elab pattern literal, so that spelling stops working for the length of
 *   the statement. This outranks the other two: it is the one that makes
 *   text stop parsing.
 * - `term`: the name is a declared term's.
 * - `variable`: the name is a `@vars` token of a *different* sort. One of
 *   the binder's own sort is not reported: `{x: var}` over a pool holding
 *   `x` binds `x` to what it already meant, and a statement must bind the
 *   variables its formulas quantify over.
 *
 * A name the language does not spell is not reported. At most one entry
 * per binder, in the scope's order.
 */
export function binderShadows(
  language: SurfaceLanguage,
  scope: Scope,
): readonly BinderShadow[] {
  const { spec } = language;
  const vocabulary = surfaceVocabulary(spec);
  const spellings = new Set(vocabulary.tokens);

  for (const rule of spec.elabRules) {
    for (const element of rule.pattern) {
      if (element.kind === "literal") {
        spellings.add(element.token);
      }
    }
  }

  const shadows: BinderShadow[] = [];

  for (const [name, sort] of scope) {
    if (spellings.has(name)) {
      shadows.push({ kind: "notation", name, sort });
      continue;
    }

    const existing = vocabulary.names.get(name);

    if (existing === undefined) {
      continue;
    }

    if (existing.kind === "term") {
      shadows.push({ kind: "term", name, sort });
    } else if (existing.sort !== sort) {
      shadows.push({
        displacedSort: existing.sort,
        kind: "variable",
        name,
        sort,
      });
    }
  }

  return shadows;
}
