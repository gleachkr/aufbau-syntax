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
  type SubscriptForm,
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
}

export interface TermInfo {
  readonly binders: readonly Binder[];
  readonly foreignAnnotations: readonly Annotation[];
  /** True when this came from a `def` rather than a `term`. */
  readonly isDef: boolean;
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

export interface LetterFamily {
  readonly class: string;
  readonly letters: ReadonlySet<string>;
  readonly subscripts: SubscriptForm;
  readonly target:
    | { readonly kind: "sort"; readonly sort: string }
    | { readonly kind: "template"; readonly term: string };
}

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
  readonly families: readonly LetterFamily[];
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
  duplicate_family_class: "letter family {name} is already declared",
  family_target: "@syntax family must sit on a sort or on a placeholder term",
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
  const families: LetterFamily[] = [];
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

        sorts.set(statement.name, {
          foreignAnnotations: foreign,
          modifiers: statement.modifiers,
          name: statement.name,
          span: statement.span,
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
          foreignAnnotations: foreign,
          isDef: statement.kind === "def",
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

  for (const { annotation, span, statement } of attached) {
    switch (annotation.kind) {
      case "family": {
        if (families.some((family) => family.class === annotation.class)) {
          report(
            diagnostics,
            "duplicate_family_class",
            { name: annotation.class },
            span,
          );
          break;
        }

        if (statement.kind === "sort") {
          families.push({
            class: annotation.class,
            letters: annotation.letters,
            subscripts: annotation.subscripts,
            target: { kind: "sort", sort: statement.name },
          });
        } else if (statement.kind === "term") {
          families.push({
            class: annotation.class,
            letters: annotation.letters,
            subscripts: annotation.subscripts,
            target: { kind: "template", term: statement.name },
          });
        } else {
          report(diagnostics, "family_target", {}, span);
        }
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
      families,
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
