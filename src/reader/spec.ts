/**
 * From parsed statements to a `Spec` — the library's central object: the
 * signature, notations, coercions, and `@syntax` surface metadata of one
 * logical system, validated.
 *
 * Validation here is about the spec being *coherent* (token conflicts,
 * dangling names, non-invertible rewrites); whether the theory proves
 * anything is the engine's business, and axiom bodies pass through opaque.
 */

import { type Diagnostic, diagnostic, type Span } from "../diagnostics";
import {
  type LintName,
  parseSyntaxAnnotation,
  type RewriteRule,
  type SyntaxAnnotation,
} from "./annotations";
import {
  type Annotation,
  type Binder,
  type NotationLiteral,
  type Precedence,
  parseStatements,
  type Statement,
} from "./statements";

export interface SortInfo {
  readonly foreignAnnotations: readonly Annotation[];
  readonly modifiers: readonly string[];
  readonly name: string;
  readonly span: Span;
  /**
   * The sort's variable tokens, read from the engine's own `@vars`
   * annotation (which stays in `foreignAnnotations` untouched — it is the
   * engine's, we only listen in). These are the surface lexicon's
   * identifiers of this sort; whether a quantifier can bind them falls
   * out of the quantifiers' binder sorts, not from here.
   */
  readonly vars: readonly string[];
}

export interface TermInfo {
  readonly binders: readonly Binder[];
  /** `@syntax elided`: supplied when an argument of its sort is missing. */
  readonly elided: boolean;
  readonly foreignAnnotations: readonly Annotation[];
  /** True when this came from a `def` rather than a `term`. */
  readonly isDef: boolean;
  /** `@syntax juxtaposed`: adjacency of its sort's leaves denotes it. */
  readonly juxtaposed: boolean;
  readonly name: string;
  readonly returnSort: string;
  readonly roles: readonly string[];
  readonly span: Span;
}

export interface CoercionInfo {
  readonly from: string;
  readonly name: string;
  readonly span: Span;
  readonly to: string;
}

export type NotationInfo =
  | {
      readonly form: "general";
      /** The notation statement's own binders, which its variables name. */
      readonly binders: readonly Binder[];
      readonly literals: readonly NotationLiteral[];
      readonly span: Span;
      readonly term: string;
    }
  | {
      readonly form: "simple";
      readonly fixity: "infixl" | "infixr" | "prefix";
      readonly prec: Precedence;
      readonly span: Span;
      readonly term: string;
      readonly token: string;
    };

export interface Spec {
  readonly assocNone: ReadonlySet<number>;
  readonly coercions: readonly CoercionInfo[];
  readonly delimiters: {
    readonly left: ReadonlySet<string>;
    readonly right: ReadonlySet<string>;
  };
  readonly display: {
    readonly dropOuterParens: boolean;
    readonly rotateBrackets: readonly (readonly [string, string])[] | null;
  };
  /** Always starts with the built-in `("(", ")")` pair. */
  readonly groupingPairs: readonly (readonly [string, string])[];
  readonly lints: readonly LintName[];
  /** In declaration order; the last notation for a term is canonical. */
  readonly notations: readonly NotationInfo[];
  readonly rewrites: readonly RewriteRule[];
  readonly sorts: ReadonlyMap<string, SortInfo>;
  /** Every statement, in order, annotations intact — full fidelity. */
  readonly statements: readonly Statement[];
  readonly terms: ReadonlyMap<string, TermInfo>;
}

export interface SpecParse {
  readonly diagnostics: readonly Diagnostic[];
  readonly spec: Spec;
}

const TEMPLATES: Record<string, string> = {
  duplicate_declaration: "{name} is already declared",
  unknown_sort: "sort {name} is not declared",
  unknown_term: "term {name} is not declared",
  infix_arity: "an infix operator needs exactly two regular arguments",
  unknown_notation_variable:
    "notation variable {name} is not one of the declaration's binders",
  token_conflict:
    "token {token} already has a meaning; a token may carry one parse rule",
  precedence_mixed_associativity:
    "precedence {prec} mixes infixl and infixr operators",
  grouping_token_conflict:
    "{token} is a grouping bracket and cannot also be a notation token",
  rewrite_duplicate_capture: "capture {name} appears twice in the pattern",
  rewrite_unknown_reference:
    "the template references {name}, which the pattern does not capture",
  rewrite_not_invertible:
    "capture {name} is not used exactly once in the template; mark the rule input-only if that is intended",
  juxtaposed_target:
    "@syntax juxtaposed must sit on a binary term whose arguments and result share one sort",
  juxtaposed_needs_notation:
    "a juxtaposed term needs a declared notation, so the engine can read it",
  juxtaposed_duplicate: "sort {sort} already has a juxtaposed combiner",
  elided_target: "@syntax elided must sit on a term with no arguments",
  elided_duplicate: "sort {sort} already has an elided term",
  vars_term_conflict:
    "@vars token {token} is also a declared term; a name can be only one",
  role_target: "@syntax role must sit on a term",
};

function report(
  diagnostics: Diagnostic[],
  id: string,
  params: Record<string, string>,
  span: Span,
): void {
  diagnostics.push(diagnostic(id, TEMPLATES[id] ?? id, params, span));
}

/** The binder count an application must fill (bound and regular alike). */
function regularBinders(binders: readonly Binder[]): readonly Binder[] {
  return binders.filter((binder) => !binder.binds);
}

function binderSortOf(binder: Binder): string {
  return "sort" in binder.type ? binder.type.sort : "";
}

interface TokenMeaning {
  readonly key: string;
  readonly term: string;
}

/**
 * One line per parse rule a token can carry. Two identical lines are a
 * pointless duplicate but not an ambiguity; anything else sharing a token
 * is a conflict.
 */
function meaningOf(notation: NotationInfo): TokenMeaning | null {
  if (notation.form === "simple") {
    return {
      key: `${notation.fixity}:${String(notation.prec)}`,
      term: notation.term,
    };
  }

  const first = notation.literals[0];

  if (first === undefined || first.kind !== "constant") {
    return null;
  }

  return { key: "general", term: notation.term };
}

export function parseSpec(source: string): SpecParse {
  const { statements, diagnostics: parseDiagnostics } =
    parseStatements(source);
  const diagnostics: Diagnostic[] = [...parseDiagnostics];

  const sorts = new Map<string, SortInfo>();
  const terms = new Map<string, TermInfo>();
  const coercions: CoercionInfo[] = [];
  const notations: NotationInfo[] = [];
  const rewrites: RewriteRule[] = [];
  const lints: LintName[] = [];
  const assocNone = new Set<number>();
  const delimitersLeft = new Set<string>();
  const delimitersRight = new Set<string>();
  const groupingPairs: (readonly [string, string])[] = [["(", ")"]];
  let dropOuterParens = false;
  let rotateBrackets: readonly (readonly [string, string])[] | null = null;

  // ── First pass: split each statement's annotations, collect declarations.

  interface Attached {
    readonly annotation: SyntaxAnnotation;
    readonly span: Span;
    readonly statement: Statement;
  }

  const attached: Attached[] = [];

  for (const statement of statements) {
    const foreign: Annotation[] = [];

    for (const annotation of statement.annotations) {
      const parsed = parseSyntaxAnnotation(annotation.text, annotation.span);

      if (parsed === null) {
        foreign.push(annotation);
        continue;
      }

      if (parsed.diagnostic !== null) {
        diagnostics.push(parsed.diagnostic);
        continue;
      }

      attached.push({
        annotation: parsed.annotation,
        span: annotation.span,
        statement,
      });
    }

    switch (statement.kind) {
      case "sort": {
        if (sorts.has(statement.name) || terms.has(statement.name)) {
          report(
            diagnostics,
            "duplicate_declaration",
            { name: statement.name },
            statement.span,
          );
          break;
        }

        // The engine's `@vars` pools are this library's variable lexicon
        // too; the lines stay foreign (they are the engine's to keep).
        const vars: string[] = [];

        for (const annotation of foreign) {
          const match = /^@vars\s+(.+)$/.exec(annotation.text.trim());

          if (match !== null) {
            vars.push(
              ...(match[1] ?? "").split(/\s+/).filter((w) => w.length > 0),
            );
          }
        }

        sorts.set(statement.name, {
          foreignAnnotations: foreign,
          modifiers: statement.modifiers,
          name: statement.name,
          span: statement.span,
          vars,
        });
        break;
      }

      case "term":
      case "def": {
        if (sorts.has(statement.name) || terms.has(statement.name)) {
          report(
            diagnostics,
            "duplicate_declaration",
            { name: statement.name },
            statement.span,
          );
          break;
        }

        const returnSort =
          statement.kind === "term"
            ? (statement.returnChain[statement.returnChain.length - 1]
                ?.sort ?? "")
            : statement.returnType.sort;

        // Arrow sugar on a term (`a > b > c`) desugars to extra anonymous
        // regular binders so arity means one thing everywhere downstream.
        const extra: Binder[] =
          statement.kind === "term"
            ? statement.returnChain.slice(0, -1).map((type) => ({
                binds: false,
                dummy: false,
                name: "_",
                span: type.span,
                type,
              }))
            : [];

        terms.set(statement.name, {
          binders: [...statement.binders, ...extra],
          elided: false,
          foreignAnnotations: foreign,
          isDef: statement.kind === "def",
          juxtaposed: false,
          name: statement.name,
          returnSort,
          roles: [],
          span: statement.span,
        });
        break;
      }

      case "coercion": {
        coercions.push({
          from: statement.from,
          name: statement.name,
          span: statement.span,
          to: statement.to,
        });
        break;
      }

      case "delimiter": {
        for (const ch of statement.left) {
          delimitersLeft.add(ch);
        }
        for (const ch of statement.right) {
          delimitersRight.add(ch);
        }
        break;
      }

      case "simple-notation": {
        notations.push({
          form: "simple",
          fixity: statement.fixity,
          prec: statement.prec,
          span: statement.span,
          term: statement.term,
          token: statement.token,
        });
        break;
      }

      case "notation": {
        notations.push({
          form: "general",
          binders: statement.binders,
          literals: statement.literals,
          span: statement.span,
          term: statement.term,
        });

        for (const literal of statement.literals) {
          if (
            literal.kind === "variable" &&
            !statement.binders.some((b) => b.name === literal.name)
          ) {
            report(
              diagnostics,
              "unknown_notation_variable",
              { name: literal.name },
              literal.span,
            );
          }
        }
        break;
      }

      case "axiom":
      case "theorem":
        break;
    }
  }

  // ── Second pass: interpret @syntax annotations now that names resolve.

  const juxtaposedBySort = new Map<string, string>();
  const elidedBySort = new Map<string, string>();

  for (const { annotation, span, statement } of attached) {
    switch (annotation.kind) {
      case "juxtaposed": {
        const info =
          statement.kind === "term" || statement.kind === "def"
            ? terms.get(statement.name)
            : undefined;
        const regular =
          info === undefined ? [] : regularBinders(info.binders);
        const sort = info?.returnSort ?? "";

        if (
          info === undefined ||
          info.binders.length !== 2 ||
          regular.length !== 2 ||
          regular.some((binder) => binderSortOf(binder) !== sort)
        ) {
          report(diagnostics, "juxtaposed_target", {}, span);
          break;
        }

        if (!notations.some((notation) => notation.term === info.name)) {
          report(diagnostics, "juxtaposed_needs_notation", {}, span);
          break;
        }

        if (juxtaposedBySort.has(sort)) {
          report(diagnostics, "juxtaposed_duplicate", { sort }, span);
          break;
        }

        juxtaposedBySort.set(sort, info.name);
        terms.set(info.name, { ...info, juxtaposed: true });
        break;
      }

      case "elided": {
        const info =
          statement.kind === "term" || statement.kind === "def"
            ? terms.get(statement.name)
            : undefined;

        if (info === undefined || regularBinders(info.binders).length !== 0) {
          report(diagnostics, "elided_target", {}, span);
          break;
        }

        if (elidedBySort.has(info.returnSort)) {
          report(
            diagnostics,
            "elided_duplicate",
            { sort: info.returnSort },
            span,
          );
          break;
        }

        elidedBySort.set(info.returnSort, info.name);
        terms.set(info.name, { ...info, elided: true });
        break;
      }

      case "role": {
        if (statement.kind !== "term" && statement.kind !== "def") {
          report(diagnostics, "role_target", {}, span);
          break;
        }

        const info = terms.get(statement.name);

        if (info !== undefined) {
          terms.set(statement.name, {
            ...info,
            roles: [...info.roles, annotation.role],
          });
        }
        break;
      }

      case "brackets": {
        for (const pair of annotation.pairs) {
          const exists = groupingPairs.some(
            ([open, close]) => open === pair[0] && close === pair[1],
          );

          if (!exists) {
            groupingPairs.push(pair);
          }
        }
        break;
      }

      case "assoc-none": {
        assocNone.add(annotation.prec);
        break;
      }

      case "lint": {
        if (!lints.includes(annotation.name)) {
          lints.push(annotation.name);
        }
        break;
      }

      case "display-drop-outer-parens": {
        dropOuterParens = true;
        break;
      }

      case "display-rotate-brackets": {
        rotateBrackets = annotation.pairs;
        break;
      }

      case "rewrite": {
        rewrites.push(annotation.rule);
        break;
      }
    }
  }

  // ── Validation over the collected spec.

  for (const info of terms.values()) {
    for (const binder of info.binders) {
      if ("sort" in binder.type && !sorts.has(binder.type.sort)) {
        report(
          diagnostics,
          "unknown_sort",
          { name: binder.type.sort },
          binder.type.span,
        );
      }
    }

    if (info.returnSort !== "" && !sorts.has(info.returnSort)) {
      report(
        diagnostics,
        "unknown_sort",
        { name: info.returnSort },
        info.span,
      );
    }
  }

  for (const sort of sorts.values()) {
    for (const token of sort.vars) {
      if (terms.has(token)) {
        report(diagnostics, "vars_term_conflict", { token }, sort.span);
      }
    }
  }

  for (const coercion of coercions) {
    if (!terms.has(coercion.name)) {
      report(
        diagnostics,
        "unknown_term",
        { name: coercion.name },
        coercion.span,
      );
    }
    for (const sort of [coercion.from, coercion.to]) {
      if (!sorts.has(sort)) {
        report(diagnostics, "unknown_sort", { name: sort }, coercion.span);
      }
    }
  }

  const tokenMeanings = new Map<string, { key: string; term: string }>();

  for (const notation of notations) {
    const info = terms.get(notation.term);

    if (info === undefined) {
      report(
        diagnostics,
        "unknown_term",
        { name: notation.term },
        notation.span,
      );
      continue;
    }

    if (
      notation.form === "simple" &&
      notation.fixity !== "prefix" &&
      (regularBinders(info.binders).length !== 2 ||
        info.binders.some((b) => b.binds))
    ) {
      report(diagnostics, "infix_arity", {}, notation.span);
    }

    const token =
      notation.form === "simple"
        ? notation.token
        : notation.literals[0]?.kind === "constant"
          ? notation.literals[0].token
          : null;
    const meaning = meaningOf(notation);

    if (token === null || meaning === null) {
      continue;
    }

    const existing = tokenMeanings.get(token);

    if (existing !== undefined) {
      if (existing.key !== meaning.key || existing.term !== meaning.term) {
        report(diagnostics, "token_conflict", { token }, notation.span);
      }
      continue;
    }

    tokenMeanings.set(token, meaning);
  }

  const precFixities = new Map<number, Set<"infixl" | "infixr">>();

  for (const notation of notations) {
    if (
      notation.form === "simple" &&
      notation.fixity !== "prefix" &&
      typeof notation.prec === "number"
    ) {
      const set = precFixities.get(notation.prec) ?? new Set();
      set.add(notation.fixity);
      precFixities.set(notation.prec, set);

      if (set.size > 1) {
        report(
          diagnostics,
          "precedence_mixed_associativity",
          { prec: String(notation.prec) },
          notation.span,
        );
      }
    }
  }

  for (const [open, close] of groupingPairs) {
    for (const token of [open, close]) {
      if (tokenMeanings.has(token)) {
        report(
          diagnostics,
          "grouping_token_conflict",
          { token },
          {
            start: 0,
            end: 0,
          },
        );
      }
    }
  }

  for (const rule of rewrites) {
    const captures = new Map<string, number>();

    for (const element of rule.pattern) {
      if (element.kind === "capture") {
        if (captures.has(element.name)) {
          report(
            diagnostics,
            "rewrite_duplicate_capture",
            { name: element.name },
            rule.span,
          );
        }
        captures.set(element.name, 0);
      }
    }

    for (const element of rule.template) {
      if (element.kind === "reference") {
        const count = captures.get(element.name);

        if (count === undefined) {
          report(
            diagnostics,
            "rewrite_unknown_reference",
            { name: element.name },
            rule.span,
          );
          continue;
        }

        captures.set(element.name, count + 1);
      }
    }

    if (!rule.inputOnly) {
      for (const [name, count] of captures) {
        if (count !== 1) {
          report(diagnostics, "rewrite_not_invertible", { name }, rule.span);
        }
      }
    }
  }

  return {
    diagnostics,
    spec: {
      assocNone,
      coercions,
      delimiters: { left: delimitersLeft, right: delimitersRight },
      display: { dropOuterParens, rotateBrackets },
      groupingPairs,
      lints,
      notations,
      rewrites,
      sorts,
      statements,
      terms,
    },
  };
}
