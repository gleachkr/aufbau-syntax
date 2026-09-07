/**
 * From parsed statements to a `Spec` — the library's central object: the
 * signature, notations, coercions, and `@syntax` surface metadata of one
 * logical system, validated.
 *
 * Validation here is about the spec being *coherent* (token conflicts,
 * dangling names, non-invertible elab rules); whether the theory proves
 * anything is the engine's business, and axiom bodies pass through opaque.
 */

import {
  type DelimiterSet,
  delimiterRules,
  isReachableChunk,
  segment,
} from "../delimiters.js";
import {
  type Diagnostic,
  diagnostic,
  type Severity,
  type Span,
} from "../diagnostics.js";
import { nameOnlyTerms, surfaceVocabulary } from "../vocabulary.js";
import {
  type ElabRule,
  type LintName,
  type OperandRelation,
  parseSyntaxAnnotation,
  type SyntaxAnnotation,
} from "./annotations.js";
import {
  type Annotation,
  type Binder,
  type NotationLiteral,
  type Precedence,
  parseStatements,
  type Statement,
} from "./statements.js";

export interface SortInfo {
  readonly foreignAnnotations: readonly Annotation[];
  readonly modifiers: readonly string[];
  readonly name: string;
  readonly roles: readonly string[];
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
  /**
   * `@syntax juxtaposed compound`: a parenthesized group may stand as a
   * glue operand in argument position, not just a single token. False
   * whenever `juxtaposed` is.
   */
  readonly juxtaposedCompound: boolean;
  readonly name: string;
  /**
   * `@syntax forbid`: the unbracketed connective operands this term
   * refuses. Empty — the default — permits all three.
   * See {@link OperandRelation} for what each one names.
   */
  readonly refuses: ReadonlySet<OperandRelation>;
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

/**
 * An axiom or theorem, as far as the surface layer is concerned: a name a
 * proof cites, the `@syntax alias` names it may cite it by instead, and the
 * `@syntax role`s that say what it is for. The statement itself passes
 * through opaque, on `Spec.statements`.
 */
export interface RuleInfo {
  /** In declaration order; never contains the rule's own name. */
  readonly aliases: readonly string[];
  readonly foreignAnnotations: readonly Annotation[];
  readonly kind: "axiom" | "theorem";
  readonly name: string;
  /**
   * `@syntax role`: what this rule *is* to a consumer — a proof editor
   * looks for `assumption` to tell the lines that open a hypothesis from
   * the ones that cite a rule. Uninterpreted here, like a term's roles.
   */
  readonly roles: readonly string[];
  readonly span: Span;
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
  readonly coercions: readonly CoercionInfo[];
  /**
   * The theory's own `delimiter` statement — how the *engine* cuts up math
   * strings. Single bytes, because that is all the engine's table holds.
   */
  readonly delimiters: DelimiterSet;
  readonly display: {
    readonly dropOuterParens: boolean;
    readonly rotateBrackets: readonly (readonly [string, string])[] | null;
  };
  /** Always starts with the built-in `("(", ")")` pair. */
  readonly groupingPairs: readonly (readonly [string, string])[];
  readonly lints: readonly LintName[];
  /** In declaration order; the last notation for a term is canonical. */
  readonly notations: readonly NotationInfo[];
  readonly elabRules: readonly ElabRule[];
  /**
   * Alias to the rule it names, over every `@syntax alias` in the spec —
   * the one lookup a proof reader needs: `ruleAliases.get(cited) ?? cited`
   * is what to hand the engine. Canonical names are not keys; a name that
   * is not an alias is already the engine's.
   */
  readonly ruleAliases: ReadonlyMap<string, string>;
  /** Every axiom and theorem, keyed by name. */
  readonly rules: ReadonlyMap<string, RuleInfo>;
  readonly sorts: ReadonlyMap<string, SortInfo>;
  /** Every statement, in order, annotations intact — full fidelity. */
  readonly statements: readonly Statement[];
  /**
   * How *student* input is cut up: `delimiters` unioned with every
   * `@syntax delimiter` the spec declares. A spec that declares none gets
   * the theory's set unchanged — so writing textbook notation tight
   * (`~~P`, `Fxy`) is an explicit opt-in, never something a spec acquires
   * by accident.
   */
  readonly surfaceDelimiters: DelimiterSet;
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
  elab_duplicate_capture: "capture {name} appears twice in the pattern",
  elab_unknown_reference:
    "the template references {name}, which the pattern does not capture",
  elab_not_invertible:
    "capture {name} is not used exactly once in the template; mark the rule input-only if that is intended",
  elab_literal_split:
    "the literal {literal} is not one chunk — the delimiters read it as {chunks}; write those as separate elements",
  elab_literal_looks_like_capture:
    "the literal {literal} contains ?; a capture is its own element, so write it with spaces around it",
  juxtaposed_target:
    "@syntax juxtaposed must sit on a binary term whose arguments and result share one sort",
  juxtaposed_needs_notation:
    "a juxtaposed term needs an infix notation — adjacency inherits its precedence, and the engine cannot read invisibility",
  juxtaposed_duplicate: "sort {sort} already has a juxtaposed combiner",
  elided_target: "@syntax elided must sit on a term with no arguments",
  refusal_target:
    "@syntax forbid must sit on a two-place term with an infix notation",
  elided_duplicate: "sort {sort} already has an elided term",
  vars_term_conflict:
    "@vars token {token} is also a declared term; a name can be only one",
  role_target: "@syntax role must sit on a sort, a term, or a rule",
  alias_target: "@syntax alias must sit on an axiom or a theorem",
  alias_is_rule_name:
    "{alias} is already the name of a rule, so it cannot be an alias",
  alias_duplicate: "{alias} already names {rule}",
  delimiter_unknown:
    "delimiter {token} is neither a notation token, a bracket, nor a lexicon name, so no input can ever be read as it",
  delimiter_token_not_delimited:
    "{token} is not a surface delimiter; it is only read when whitespace or a delimiter bounds it, so it will run into an adjacent token",
  delimiter_unreachable_name:
    "the delimiters split {name} into {chunks}, so it can never be read as one name",
  delimiter_splits_token:
    "the delimiters split the notation token {token} into {chunks}, so it can never be read; mm0.md requires a token not to contain a delimiter",
};

function report(
  diagnostics: Diagnostic[],
  id: string,
  params: Record<string, string>,
  span: Span,
  severity: Severity = "error",
): void {
  diagnostics.push(
    diagnostic(id, TEMPLATES[id] ?? id, params, span, severity),
  );
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

/** Where each notation constant was declared, for pointing a diagnostic. */
function tokenSpans(spec: Spec): Map<string, Span> {
  const spans = new Map<string, Span>();

  for (const notation of spec.notations) {
    const constants =
      notation.form === "simple"
        ? [notation.token]
        : notation.literals
            .filter((literal) => literal.kind === "constant")
            .map((literal) => literal.token);

    for (const token of constants) {
      if (!spans.has(token)) {
        spans.set(token, notation.span);
      }
    }
  }

  return spans;
}

/**
 * A notation token a delimiter cuts through is dead: mm0.md forbids it
 * outright ("a declared token must not contain a delimiter token as a
 * substring"), the engine cannot read it either, and the printer never
 * picks it as a spelling. A warning rather than an error, since the
 * engine tolerates the declaration — `/\\` beside `∧` in a file whose
 * `[x/t]` makes `/` a delimiter — and so does everything here.
 */
function reportDeadTokens(spec: Spec, diagnostics: Diagnostic[]): void {
  // The theory's own delimiters, not the surface set: a token the surface
  // letters split (`tsub` under forallx) is an engine-only notation, and
  // `delimiter_token_not_delimited` already says so.
  const rules = delimiterRules(spec.delimiters);
  const spans = tokenSpans(spec);

  for (const token of surfaceVocabulary(spec).tokens) {
    const span = spans.get(token);

    if (span === undefined || isReachableChunk(token, rules)) {
      continue;
    }

    report(
      diagnostics,
      "delimiter_splits_token",
      { chunks: segment(token, rules).join(" "), token },
      span,
      "warning",
    );
  }
}

/**
 * The surface delimiter set, checked against the vocabulary it has to cut
 * up. Only runs when the spec declares `@syntax delimiter`: a spec that
 * declares none is read under the theory's own delimiters, where tokens
 * are whitespace-separated and none of this can bite.
 */
function checkSurfaceDelimiters(
  spec: Spec,
  declarations: readonly { entries: readonly string[]; span: Span }[],
  diagnostics: Diagnostic[],
): void {
  const fallback = declarations[0]?.span;

  if (fallback === undefined) {
    return;
  }

  const vocabulary = surfaceVocabulary(spec);
  const rules = delimiterRules(spec.surfaceDelimiters);
  const declared = new Set([
    ...spec.surfaceDelimiters.left,
    ...spec.surfaceDelimiters.right,
  ]);

  // A delimiter nothing can be classified as cuts input into pieces the
  // parser must then reject — a boundary with no meaning behind it.
  for (const { entries, span } of declarations) {
    for (const entry of entries) {
      if (!vocabulary.tokens.has(entry) && !vocabulary.names.has(entry)) {
        report(diagnostics, "delimiter_unknown", { token: entry }, span);
      }
    }
  }

  // A token that is not itself a delimiter still reads when whitespace or a
  // delimiter bounds it — `P->Q` is fine with the letters declared — so this
  // is advice, not breakage. What it warns about is two such tokens
  // meeting: `->~` is one chunk unless one of them delimits.
  const spans = tokenSpans(spec);

  for (const token of vocabulary.tokens) {
    if (!declared.has(token)) {
      report(
        diagnostics,
        "delimiter_token_not_delimited",
        { token },
        spans.get(token) ?? fallback,
        "warning",
      );
    }
  }

  // A name the delimiters split apart is unreachable: segmentation happens
  // before anything knows the name exists, so no bracketing recovers it.
  // Only a term with no other spelling is at stake; a notated term's name
  // is MM0's application syntax, still reachable under the engine's own
  // delimiters. Elided terms are exempt — they are supplied by the parser
  // and dropped by the printer, never typed.
  const nameOnly = nameOnlyTerms(spec);

  for (const [name, ref] of vocabulary.names) {
    if (
      ref.kind === "term" &&
      (spec.terms.get(ref.term)?.elided === true || !nameOnly.has(ref.term))
    ) {
      continue;
    }

    if (isReachableChunk(name, rules)) {
      continue;
    }

    const span =
      ref.kind === "term"
        ? spec.terms.get(ref.term)?.span
        : spec.sorts.get(ref.sort)?.span;

    report(
      diagnostics,
      "delimiter_unreachable_name",
      { chunks: segment(name, rules).join(" "), name },
      span ?? fallback,
    );
  }
}

/**
 * Elab literals against the delimiters that will cut up the text they have
 * to match. A literal need not be declared vocabulary — that is the point
 * of the layer — but it is matched one chunk at a time, so a literal the
 * delimiters split can never match anything, and a rule that quietly does
 * nothing is the failure this reader exists to prevent.
 *
 * Template literals are checked too, for every rule that is not
 * `input-only`: delaboration runs the rule inverted, where the template's
 * literals *are* the pattern.
 */
function checkElabLiterals(spec: Spec, diagnostics: Diagnostic[]): void {
  const rules = delimiterRules(spec.surfaceDelimiters);

  const check = (token: string, span: Span): void => {
    // `parsePattern` splits on whitespace, so `(?x:var)` arrives as one
    // literal rather than three elements. It would trip the split check
    // below as well, but this names the actual mistake.
    if (token.includes("?")) {
      report(
        diagnostics,
        "elab_literal_looks_like_capture",
        { literal: token },
        span,
      );
      return;
    }

    if (!isReachableChunk(token, rules)) {
      report(
        diagnostics,
        "elab_literal_split",
        { chunks: segment(token, rules).join(" "), literal: token },
        span,
      );
    }
  };

  for (const rule of spec.elabRules) {
    for (const element of rule.pattern) {
      if (element.kind === "literal") {
        check(element.token, rule.span);
      }
    }

    if (rule.inputOnly) {
      continue;
    }

    for (const element of rule.template) {
      if (element.kind === "literal") {
        check(element.token, rule.span);
      }
    }
  }
}

export function parseSpec(source: string): SpecParse {
  const { statements, diagnostics: parseDiagnostics } =
    parseStatements(source);
  const diagnostics: Diagnostic[] = [...parseDiagnostics];

  const sorts = new Map<string, SortInfo>();
  const terms = new Map<string, TermInfo>();
  const coercions: CoercionInfo[] = [];
  const rules = new Map<string, RuleInfo>();
  const ruleAliases = new Map<string, string>();
  const notations: NotationInfo[] = [];
  const elabRules: ElabRule[] = [];
  const lints: LintName[] = [];
  const delimitersLeft = new Set<string>();
  const delimitersRight = new Set<string>();
  const surfaceLeft = new Set<string>();
  const surfaceRight = new Set<string>();
  const surfaceDeclarations: {
    readonly entries: readonly string[];
    readonly span: Span;
  }[] = [];
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
        // Sorts and terms are separate namespaces (peano.mm0 declares a
        // sort `nat` and a def `nat`); each name may be declared once
        // within its own.
        if (sorts.has(statement.name)) {
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
          roles: [],
          span: statement.span,
          vars,
        });
        break;
      }

      case "term":
      case "def": {
        if (terms.has(statement.name)) {
          report(
            diagnostics,
            "duplicate_declaration",
            { name: statement.name },
            statement.span,
          );
          break;
        }

        const returnSort =
          statement.returnChain[statement.returnChain.length - 1]?.sort ?? "";

        // Arrow sugar (`a > b > c`) desugars to extra anonymous regular
        // binders so arity means one thing everywhere downstream. A
        // def's dot-dummies go the other way: they are variables of the
        // definiens, never arguments, so they are no part of the
        // syntax.
        const extra: Binder[] = statement.returnChain
          .slice(0, -1)
          .map((type) => ({
            binds: false,
            dummy: false,
            name: "_",
            span: type.span,
            type,
          }));
        const arguments_ = statement.binders.filter(
          (binder) => !binder.dummy,
        );

        terms.set(statement.name, {
          binders: [...arguments_, ...extra],
          elided: false,
          foreignAnnotations: foreign,
          isDef: statement.kind === "def",
          juxtaposed: false,
          juxtaposedCompound: false,
          name: statement.name,
          refuses: new Set(),
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
      case "theorem": {
        // The engine refuses a second declaration of a name; recording it
        // once here keeps the alias table from ever being ambiguous.
        if (rules.has(statement.name)) {
          report(
            diagnostics,
            "duplicate_declaration",
            { name: statement.name },
            statement.span,
          );
          break;
        }

        rules.set(statement.name, {
          aliases: [],
          roles: [],
          foreignAnnotations: foreign,
          kind: statement.kind,
          name: statement.name,
          span: statement.span,
        });
        break;
      }
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

        // An *infix* notation specifically: adjacency stands in for the
        // written operator, so it needs a precedence and an associativity
        // to inherit — and the engine cannot read invisibility either way.
        if (
          !notations.some(
            (notation) =>
              notation.term === info.name &&
              notation.form === "simple" &&
              notation.fixity !== "prefix",
          )
        ) {
          report(diagnostics, "juxtaposed_needs_notation", {}, span);
          break;
        }

        if (juxtaposedBySort.has(sort)) {
          report(diagnostics, "juxtaposed_duplicate", { sort }, span);
          break;
        }

        juxtaposedBySort.set(sort, info.name);
        terms.set(info.name, {
          ...info,
          juxtaposed: true,
          juxtaposedCompound: annotation.compound,
        });
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
        if (statement.kind === "sort") {
          const info = sorts.get(statement.name);

          if (info !== undefined) {
            sorts.set(statement.name, {
              ...info,
              roles: [...info.roles, annotation.role],
            });
          }
          break;
        }

        if (statement.kind === "axiom" || statement.kind === "theorem") {
          const info = rules.get(statement.name);

          if (info !== undefined) {
            rules.set(statement.name, {
              ...info,
              roles: [...info.roles, annotation.role],
            });
          }
          break;
        }

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

      case "alias": {
        const info =
          statement.kind === "axiom" || statement.kind === "theorem"
            ? rules.get(statement.name)
            : undefined;

        if (info === undefined) {
          report(diagnostics, "alias_target", {}, span);
          break;
        }

        for (const alias of annotation.names) {
          // A proof citing this name must mean one rule. The rule's own
          // name is the engine's, and another rule's alias is taken.
          if (rules.has(alias)) {
            report(diagnostics, "alias_is_rule_name", { alias }, span);
            continue;
          }

          const owner = ruleAliases.get(alias);

          if (owner !== undefined) {
            if (owner !== info.name) {
              report(
                diagnostics,
                "alias_duplicate",
                { alias, rule: owner },
                span,
              );
            }
            continue;
          }

          ruleAliases.set(alias, info.name);
          const current = rules.get(info.name) ?? info;
          rules.set(info.name, {
            ...current,
            aliases: [...current.aliases, alias],
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

      case "delimiter": {
        for (const entry of annotation.left) {
          surfaceLeft.add(entry);
        }

        for (const entry of annotation.right) {
          surfaceRight.add(entry);
        }

        surfaceDeclarations.push({
          entries: [...new Set([...annotation.left, ...annotation.right])],
          span,
        });
        break;
      }

      case "forbid": {
        const info =
          statement.kind === "term" || statement.kind === "def"
            ? terms.get(statement.name)
            : undefined;

        // Only an infix two-place term can *have* an unbracketed connective
        // operand, so anywhere else the annotation would sit and do nothing.
        if (
          info === undefined ||
          regularBinders(info.binders).length !== 2 ||
          !notations.some(
            (notation) =>
              notation.term === info.name &&
              notation.form === "simple" &&
              notation.fixity !== "prefix",
          )
        ) {
          report(diagnostics, "refusal_target", {}, span);
          break;
        }

        terms.set(info.name, {
          ...info,
          refuses: new Set([...info.refuses, ...annotation.relations]),
        });
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

      case "elab": {
        elabRules.push(annotation.rule);
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

  for (const rule of elabRules) {
    const captures = new Map<string, number>();

    for (const element of rule.pattern) {
      if (element.kind === "capture") {
        if (captures.has(element.name)) {
          report(
            diagnostics,
            "elab_duplicate_capture",
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
            "elab_unknown_reference",
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
          report(diagnostics, "elab_not_invertible", { name }, rule.span);
        }
      }
    }
  }

  const spec: Spec = {
    coercions,
    delimiters: { left: delimitersLeft, right: delimitersRight },
    display: { dropOuterParens, rotateBrackets },
    groupingPairs,
    lints,
    notations,
    elabRules,
    ruleAliases,
    rules,
    sorts,
    statements,
    // The union: what the engine splits on, plus what the textbook does.
    surfaceDelimiters: {
      left: new Set([...delimitersLeft, ...surfaceLeft]),
      right: new Set([...delimitersRight, ...surfaceRight]),
    },
    terms,
  };

  reportDeadTokens(spec, diagnostics);
  checkSurfaceDelimiters(spec, surfaceDeclarations, diagnostics);
  checkElabLiterals(spec, diagnostics);

  return { diagnostics, spec };
}
