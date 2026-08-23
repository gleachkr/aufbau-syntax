/**
 * The surface parser: a faithful port of MM0's operator-precedence math
 * parser (mm0.md, "the dynamic parser"), running over the character-level
 * scanner instead of MM0's whitespace lexer, with exactly three declared
 * extensions beyond the upstream grammar:
 *
 *   1. **Grouping pairs** — `expression(max) → open expression(0) close`
 *      for every declared bracket pair, close matching open;
 *   2. **assoc-none levels** — a precedence in `@syntax assoc-none` refuses
 *      to chain regardless of its declared associativity (`P → Q → R` is an
 *      error, per forallx);
 *   3. **Lints** — the closed set of post-parse checks
 *      (`parenthesize-binary-only`, `closed-sentences`).
 *
 * Two survivable deviations, both surface-side supersets: an elaborated
 * letter (nullary or applied to grouped arguments) counts as
 * `expression(max)`, where MM0 puts constructor application at 1024; and a
 * token that is both a notation and a family letter (Calgary's `A`) is
 * disambiguated by backtracking, notation reading first.
 *
 * mm0.md's slot-precedence rules are used exactly: a prefix notation's
 * intermediate arguments parse at max and its last at the notation's
 * precedence; a general notation's slot parses at max before a variable, at
 * `p+1` before a constant of precedence `p`, and at the head precedence
 * when last. Coercions are inserted along the (unique) path in the coercion
 * graph, per the spec.
 */

import { type Diagnostic, diagnostic, type Span } from "./diagnostics";
import type { LetterFamily, Spec, TermInfo } from "./reader/spec";
import type { Binder, TypeRef } from "./reader/statements";
import { type Reading, Scanner } from "./scan";
import type { AppTerm, Term, VariableTerm } from "./term";
import { walkTerm } from "./term";

const TEMPLATES: Record<string, string> = {
  unrecognized_character: "Unexpected character “{character}”.",
  expected_formula: "Expected a formula.",
  expected_formula_found: "Expected a formula but found “{token}”.",
  unexpected_token: "Unexpected “{token}”.",
  expected_variable: "Expected a variable after the quantifier.",
  expected_bracket: "Expected “{bracket}”.",
  chain_refused:
    "“{operator}” cannot be chained; add parentheses to group it.",
  group_binary_only:
    "Parentheses may only enclose a sentence joined by a two-place connective.",
  free_variable:
    "“{name}” is a free variable; every formula must be a sentence.",
  sort_mismatch: "This has sort {actual} where {expected} is needed.",
  term_not_sentence: "This is a {actual}, not a complete sentence.",
  needs_parentheses: "“{token}” binds too loosely here; parenthesize it.",
  spec_notation_incomplete:
    "The notation for {term} does not cover all of its arguments.",
};

function precNum(prec: number | "max"): number {
  return prec === "max" ? Number.POSITIVE_INFINITY : prec;
}

interface PrefixEntry {
  readonly kind: "prefix";
  readonly info: TermInfo;
  readonly prec: number | "max";
}

interface InfixEntry {
  readonly kind: "infix";
  readonly info: TermInfo;
  readonly prec: number;
  readonly fixity: "infixl" | "infixr";
}

interface GeneralSlot {
  readonly binder: Binder;
  /** Index into the term's binder list this slot fills. */
  readonly index: number;
  readonly prec: number;
}

interface GeneralEntry {
  readonly kind: "general";
  readonly info: TermInfo;
  /** Interleaved constants (to expect) and slots (to parse), head dropped. */
  readonly parts: readonly (
    | { readonly kind: "constant"; readonly token: string }
    | { readonly kind: "slot"; readonly slot: GeneralSlot }
  )[];
}

type HeadEntry = GeneralEntry | PrefixEntry;

interface FamilyInfo {
  readonly family: LetterFamily;
  /** Regular binders of the template; empty for a nullary or a variable. */
  readonly argBinders: readonly Binder[];
  readonly sort: string;
  readonly isVariable: boolean;
}

export interface ParseSuccess {
  readonly ok: true;
  readonly term: Term;
  readonly diagnostics: readonly Diagnostic[];
}

export interface ParseFailure {
  readonly ok: false;
  readonly diagnostics: readonly Diagnostic[];
}

export type ParseResult = ParseFailure | ParseSuccess;

function binderSort(binder: Binder | undefined): string {
  if (binder === undefined || !("sort" in binder.type)) {
    return "";
  }

  return (binder.type as TypeRef).sort;
}

/** Everything derived from a Spec that parsing needs, built once. */
export class SurfaceLanguage {
  readonly spec: Spec;
  readonly scanner: Scanner;
  readonly heads = new Map<string, HeadEntry>();
  readonly infixes = new Map<string, InfixEntry>();
  readonly closeOf = new Map<string, string>();
  readonly closers = new Set<string>();
  readonly familyInfo = new Map<string, FamilyInfo>();
  readonly provableSort: string | null;
  private readonly coercionPaths = new Map<
    string,
    readonly string[] | null
  >();

  constructor(spec: Spec) {
    this.spec = spec;
    this.scanner = new Scanner(spec);

    for (const notation of spec.notations) {
      const info = spec.terms.get(notation.term);

      if (info === undefined) {
        continue;
      }

      if (notation.form === "simple") {
        if (notation.fixity === "prefix") {
          this.heads.set(notation.token, {
            kind: "prefix",
            info,
            prec: notation.prec,
          });
        } else if (typeof notation.prec === "number") {
          this.infixes.set(notation.token, {
            kind: "infix",
            info,
            prec: notation.prec,
            fixity: notation.fixity,
          });
        }
        continue;
      }

      const head = notation.literals[0];

      if (head === undefined || head.kind !== "constant") {
        continue;
      }

      // mm0.md's P(lits, q): a slot parses at max before a variable, at
      // p+1 before a constant of precedence p, and at q (the head
      // precedence) when it is the trailing slot.
      const parts: (
        | { kind: "constant"; token: string }
        | { kind: "slot"; slot: GeneralSlot }
      )[] = [];
      const rest = notation.literals.slice(1);

      for (let i = 0; i < rest.length; i += 1) {
        const literal = rest[i];

        if (literal === undefined) {
          continue;
        }

        if (literal.kind === "constant") {
          parts.push({ kind: "constant", token: literal.token });
          continue;
        }

        const index = notation.binders.findIndex(
          (binder) => binder.name === literal.name,
        );
        const binder = notation.binders[index];

        if (binder === undefined) {
          continue;
        }

        const following = rest[i + 1];
        const prec =
          following === undefined
            ? precNum(head.prec)
            : following.kind === "constant"
              ? precNum(following.prec) + 1
              : Number.POSITIVE_INFINITY;

        parts.push({ kind: "slot", slot: { binder, index, prec } });
      }

      this.heads.set(head.token, { kind: "general", info, parts });
    }

    for (const [open, close] of spec.groupingPairs) {
      this.closeOf.set(open, close);
      this.closers.add(close);
    }

    for (const family of spec.families) {
      if (family.target.kind === "sort") {
        this.familyInfo.set(family.class, {
          family,
          argBinders: [],
          sort: family.target.sort,
          isVariable: true,
        });
        continue;
      }

      const template = spec.terms.get(family.target.term);

      if (template === undefined) {
        continue;
      }

      this.familyInfo.set(family.class, {
        family,
        argBinders: template.binders.filter((binder) => !binder.binds),
        sort: template.returnSort,
        isVariable: false,
      });
    }

    this.provableSort =
      [...spec.sorts.values()].find((sort) =>
        sort.modifiers.includes("provable"),
      )?.name ?? null;
  }

  /** The coercion path from one sort to another; unique per mm0.md. */
  coerce(from: string, to: string): readonly string[] | null {
    if (from === to) {
      return [];
    }

    const key = `${from}>${to}`;
    const cached = this.coercionPaths.get(key);

    if (cached !== undefined) {
      return cached;
    }

    const previous = new Map<string, { sort: string; name: string }>();
    const queue = [from];

    while (queue.length > 0) {
      const sort = queue.shift();

      if (sort === undefined || sort === to) {
        break;
      }

      for (const coercion of this.spec.coercions) {
        if (coercion.from === sort && !previous.has(coercion.to)) {
          previous.set(coercion.to, { sort, name: coercion.name });
          queue.push(coercion.to);
        }
      }
    }

    let path: string[] | null = null;

    if (previous.has(to)) {
      path = [];
      let at = to;

      while (at !== from) {
        const step = previous.get(at);

        if (step === undefined) {
          path = null;
          break;
        }

        path.unshift(step.name);
        at = step.sort;
      }
    }

    this.coercionPaths.set(key, path);
    return path;
  }

  parse(text: string): ParseResult {
    return new Parse(this, text).run();
  }
}

class Parse {
  private position = 0;
  private diagnostics: Diagnostic[] = [];
  /**
   * The deepest-reaching diagnostic a failed trial produced. When a
   * fallback reading succeeds but leaves trailing input short of where a
   * higher-priority reading got to, that earlier, more specific error is
   * the one the writer should see — `F(a` is an unclosed argument list,
   * not a stray `(` after the sentence letter F.
   */
  private bestTrialFailure: { end: number; diag: Diagnostic } | null = null;

  constructor(
    private readonly lang: SurfaceLanguage,
    private readonly text: string,
  ) {}

  run(): ParseResult {
    const parsed = this.parseExpr(0);

    if (parsed !== null) {
      const point = this.lang.scanner.at(this.text, this.position);

      if (!point.atEnd) {
        const trial = this.bestTrialFailure;

        if (trial !== null && trial.end > point.start) {
          this.diagnostics.push(trial.diag);
        } else if (point.readings.length === 0) {
          this.report(
            "unrecognized_character",
            { character: this.text[point.start] ?? "" },
            { start: point.start, end: point.start + 1 },
          );
        } else {
          const reading = point.readings[0];
          const token =
            reading === undefined
              ? (this.text[point.start] ?? "")
              : reading.kind === "token"
                ? reading.token
                : reading.name;

          this.report(
            "unexpected_token",
            { token },
            {
              start: point.start,
              end: point.start + (reading?.length ?? 1),
            },
          );
        }

        return { ok: false, diagnostics: this.diagnostics };
      }
    }

    if (parsed === null) {
      if (this.diagnostics.length === 0) {
        this.report("expected_formula", {}, { start: 0, end: 0 });
      }

      return { ok: false, diagnostics: this.diagnostics };
    }

    let term = parsed;
    const provable = this.lang.provableSort;

    if (provable !== null && term.sort !== provable) {
      const wrapped = this.coerceTerm(term, provable);

      if (wrapped === null) {
        this.report("term_not_sentence", { actual: term.sort }, term.span);
        return { ok: false, diagnostics: this.diagnostics };
      }

      term = wrapped;
    }

    this.lint(term);

    if (this.diagnostics.length > 0) {
      return { ok: false, diagnostics: this.diagnostics };
    }

    return { ok: true, term, diagnostics: this.diagnostics };
  }

  // ── plumbing ──────────────────────────────────────────────────────────

  private report(
    id: string,
    params: Record<string, string>,
    span: Span,
  ): null {
    this.diagnostics.push(diagnostic(id, TEMPLATES[id] ?? id, params, span));
    return null;
  }

  /** Run a trial parse; on failure, rewind input and drop its diagnostics. */
  private attempt<T>(body: () => T | null): T | null {
    const position = this.position;
    const kept = this.diagnostics.length;
    const result = body();

    if (result === null) {
      for (const diag of this.diagnostics.slice(kept)) {
        if (diag.span.end > (this.bestTrialFailure?.end ?? -1)) {
          this.bestTrialFailure = { end: diag.span.end, diag };
        }
      }

      this.position = position;
      this.diagnostics.length = kept;
    }

    return result;
  }

  private coerceTerm(term: Term, target: string): Term | null {
    const path = this.lang.coerce(term.sort, target);

    if (path === null) {
      return null;
    }

    let wrapped = term;

    for (const name of path) {
      const info = this.lang.spec.terms.get(name);

      wrapped = {
        kind: "app",
        term: name,
        family: null,
        args: [wrapped],
        sort: info?.returnSort ?? target,
        span: wrapped.span,
        grouped: false,
        fixity: null,
        prec: null,
        token: null,
      };
    }

    return wrapped;
  }

  private coerceOrReport(term: Term, target: string): Term | null {
    const wrapped = this.coerceTerm(term, target);

    if (wrapped === null) {
      return this.report(
        "sort_mismatch",
        { actual: term.sort, expected: target },
        term.span,
      );
    }

    return wrapped;
  }

  // ── the precedence parser ─────────────────────────────────────────────

  private parseExpr(min: number): Term | null {
    let left = this.parsePrimary(min);

    if (left === null) {
      return null;
    }

    for (;;) {
      const point = this.lang.scanner.at(this.text, this.position);

      if (point.atEnd) {
        return left;
      }

      const reading = point.readings.find((r) => r.kind === "token");

      if (reading === undefined || reading.kind !== "token") {
        return left;
      }

      const entry = this.lang.infixes.get(reading.token);

      if (entry === undefined || entry.prec < min) {
        return left;
      }

      this.position = point.start + reading.length;

      const right = this.parseExpr(
        entry.fixity === "infixl" ? entry.prec + 1 : entry.prec,
      );

      if (right === null) {
        return null;
      }

      const binders = entry.info.binders;
      const leftSort = binderSort(binders[0]);
      const rightSort = binderSort(binders[1]);
      const coercedLeft = this.coerceOrReport(left, leftSort);
      const coercedRight = this.coerceOrReport(right, rightSort);

      if (coercedLeft === null || coercedRight === null) {
        return null;
      }

      left = {
        kind: "app",
        term: entry.info.name,
        family: null,
        args: [coercedLeft, coercedRight],
        sort: entry.info.returnSort,
        span: { start: left.span.start, end: right.span.end },
        grouped: false,
        fixity: entry.fixity,
        prec: entry.prec,
        token: reading.token,
      } satisfies AppTerm;
    }
  }

  private parsePrimary(min: number): Term | null {
    const point = this.lang.scanner.at(this.text, this.position);

    if (point.atEnd) {
      return this.report(
        "expected_formula",
        {},
        {
          start: point.start,
          end: point.start,
        },
      );
    }

    if (point.readings.length === 0) {
      return this.report(
        "unrecognized_character",
        { character: this.text[point.start] ?? "" },
        { start: point.start, end: point.start + 1 },
      );
    }

    // Try each reading with backtracking; if none succeeds, re-run the
    // first viable one so its diagnostics — the most specific available —
    // are the ones the writer sees.
    const viable = point.readings.filter((reading) =>
      this.isViablePrimary(reading),
    );

    for (const reading of viable) {
      const result = this.attempt(() =>
        this.parsePrimaryReading(point.start, reading, min),
      );

      if (result !== null) {
        return result;
      }
    }

    const first = viable[0];

    if (first !== undefined) {
      return this.parsePrimaryReading(point.start, first, min);
    }

    const reading = point.readings[0];
    const token =
      reading?.kind === "token" ? reading.token : (reading?.name ?? "");

    return this.report(
      "expected_formula_found",
      { token },
      {
        start: point.start,
        end: point.start + (reading?.length ?? 1),
      },
    );
  }

  private isViablePrimary(reading: Reading): boolean {
    if (reading.kind === "letter") {
      return true;
    }

    return (
      this.lang.closeOf.has(reading.token) ||
      this.lang.heads.has(reading.token)
    );
  }

  private parsePrimaryReading(
    start: number,
    reading: Reading,
    min: number,
  ): Term | null {
    if (reading.kind === "letter") {
      return this.parseLetter(start, reading);
    }

    const close = this.lang.closeOf.get(reading.token);

    if (close !== undefined) {
      return this.parseGroup(start, close, reading.length);
    }

    const head = this.lang.heads.get(reading.token);

    if (head === undefined) {
      return this.report(
        "expected_formula_found",
        { token: reading.token },
        {
          start,
          end: start + reading.length,
        },
      );
    }

    this.position = start + reading.length;

    return head.kind === "prefix"
      ? this.parsePrefix(start, reading.token, head, min)
      : this.parseGeneral(start, reading.token, head, min);
  }

  private parseGroup(
    start: number,
    close: string,
    openLength: number,
  ): Term | null {
    this.position = start + openLength;

    const inner = this.parseExpr(0);

    if (inner === null) {
      return null;
    }

    const point = this.lang.scanner.at(this.text, this.position);
    const reading = point.readings.find(
      (r) => r.kind === "token" && r.token === close,
    );

    if (reading === undefined) {
      return this.report(
        "expected_bracket",
        { bracket: close },
        {
          start: point.start,
          end: point.start + 1,
        },
      );
    }

    this.position = point.start + reading.length;

    return {
      ...inner,
      grouped: true,
      span: { start, end: this.position },
    };
  }

  private parsePrefix(
    start: number,
    token: string,
    entry: PrefixEntry,
    min: number,
  ): Term | null {
    if (precNum(entry.prec) < min) {
      return this.report(
        "needs_parentheses",
        { token },
        {
          start,
          end: this.position,
        },
      );
    }

    const binders = entry.info.binders;
    const args: Term[] = [];

    for (let i = 0; i < binders.length; i += 1) {
      const binder = binders[i];

      if (binder === undefined) {
        continue;
      }

      if (binder.binds) {
        const variable = this.expectBoundVariable(binderSort(binder));

        if (variable === null) {
          return null;
        }

        args.push(variable);
        continue;
      }

      // mm0.md: a prefix notation's intermediate arguments parse at max,
      // its last at the notation's own precedence.
      const slotPrec =
        i === binders.length - 1
          ? precNum(entry.prec)
          : Number.POSITIVE_INFINITY;
      const arg = this.parseExpr(slotPrec);

      if (arg === null) {
        return null;
      }

      const coerced = this.coerceOrReport(arg, binderSort(binder));

      if (coerced === null) {
        return null;
      }

      args.push(coerced);
    }

    return {
      kind: "app",
      term: entry.info.name,
      family: null,
      args,
      sort: entry.info.returnSort,
      span: {
        start,
        end: args[args.length - 1]?.span.end ?? this.position,
      },
      grouped: false,
      fixity: "prefix",
      prec: precNum(entry.prec),
      token,
    };
  }

  private parseGeneral(
    start: number,
    token: string,
    entry: GeneralEntry,
    min: number,
  ): Term | null {
    const headPrec = this.headPrecOf(token);

    if (headPrec !== null && headPrec < min) {
      return this.report(
        "needs_parentheses",
        { token },
        {
          start,
          end: this.position,
        },
      );
    }

    const byIndex = new Map<number, Term>();

    for (const part of entry.parts) {
      if (part.kind === "constant") {
        const point = this.lang.scanner.at(this.text, this.position);
        const reading = point.readings.find(
          (r) => r.kind === "token" && r.token === part.token,
        );

        if (reading === undefined) {
          return this.report(
            "expected_bracket",
            { bracket: part.token },
            {
              start: point.start,
              end: point.start + 1,
            },
          );
        }

        this.position = point.start + reading.length;
        continue;
      }

      const { binder, index, prec } = part.slot;

      if (binder.binds) {
        const variable = this.expectBoundVariable(binderSort(binder));

        if (variable === null) {
          return null;
        }

        byIndex.set(index, variable);
        continue;
      }

      const arg = this.parseExpr(prec);

      if (arg === null) {
        return null;
      }

      const coerced = this.coerceOrReport(arg, binderSort(binder));

      if (coerced === null) {
        return null;
      }

      byIndex.set(index, coerced);
    }

    const args: Term[] = [];

    for (let i = 0; i < entry.info.binders.length; i += 1) {
      const arg = byIndex.get(i);

      if (arg === undefined) {
        return this.report(
          "spec_notation_incomplete",
          { term: entry.info.name },
          { start, end: this.position },
        );
      }

      args.push(arg);
    }

    return {
      kind: "app",
      term: entry.info.name,
      family: null,
      args,
      sort: entry.info.returnSort,
      span: { start, end: args[args.length - 1]?.span.end ?? this.position },
      grouped: false,
      fixity: "general",
      prec: headPrec,
      token,
    };
  }

  private headPrecOf(token: string): number | null {
    for (const notation of this.lang.spec.notations) {
      if (notation.form === "general") {
        const head = notation.literals[0];

        if (head?.kind === "constant" && head.token === token) {
          return precNum(head.prec);
        }
      }
    }

    return null;
  }

  private expectBoundVariable(sort: string): VariableTerm | null {
    const point = this.lang.scanner.at(this.text, this.position);
    const reading = point.readings.find(
      (r): r is Reading & { kind: "letter" } =>
        r.kind === "letter" &&
        (this.lang.familyInfo.get(r.family.class)?.isVariable ?? false) &&
        this.lang.familyInfo.get(r.family.class)?.sort === sort,
    );

    if (reading === undefined || reading.kind !== "letter") {
      return this.report(
        "expected_variable",
        {},
        {
          start: point.start,
          end: point.start + 1,
        },
      );
    }

    this.position = point.start + reading.length;

    return {
      kind: "variable",
      name: reading.name,
      sort,
      span: { start: point.start, end: this.position },
      grouped: false,
      binder: true,
    };
  }

  private parseLetter(
    start: number,
    reading: Reading & { kind: "letter" },
  ): Term | null {
    const info = this.lang.familyInfo.get(reading.family.class);

    if (info === undefined) {
      return this.report(
        "expected_formula_found",
        { token: reading.name },
        { start, end: start + reading.length },
      );
    }

    this.position = start + reading.length;

    if (info.isVariable) {
      return {
        kind: "variable",
        name: reading.name,
        sort: info.sort,
        span: { start, end: this.position },
        grouped: false,
        binder: false,
      };
    }

    // A template with arguments demands them, parenthesized — Calgary's
    // `predicatesTakeParens`. Argument parentheses are application syntax,
    // not grouping, so the argument is not marked `grouped` and the
    // binary-only lint does not apply inside; the canonical pair is always
    // the first declared one.
    const args: Term[] = [];

    for (const binder of info.argBinders) {
      const point = this.lang.scanner.at(this.text, this.position);
      const open = this.lang.spec.groupingPairs[0]?.[0] ?? "(";
      const close = this.lang.spec.groupingPairs[0]?.[1] ?? ")";
      const openReading = point.readings.find(
        (r) => r.kind === "token" && r.token === open,
      );

      if (openReading === undefined) {
        return this.report(
          "expected_formula_found",
          { token: reading.name },
          {
            start,
            end: start + reading.length,
          },
        );
      }

      this.position = point.start + openReading.length;

      const arg = this.parseExpr(0);

      if (arg === null) {
        return null;
      }

      const closePoint = this.lang.scanner.at(this.text, this.position);
      const closeReading = closePoint.readings.find(
        (r) => r.kind === "token" && r.token === close,
      );

      if (closeReading === undefined) {
        return this.report(
          "expected_bracket",
          { bracket: close },
          {
            start: closePoint.start,
            end: closePoint.start + 1,
          },
        );
      }

      this.position = closePoint.start + closeReading.length;

      const coerced = this.coerceOrReport(arg, binderSort(binder));

      if (coerced === null) {
        return null;
      }

      args.push(coerced);
    }

    return {
      kind: "app",
      term: reading.name,
      family: reading.family.class,
      args,
      sort: info.sort,
      span: { start, end: this.position },
      grouped: false,
      fixity: null,
      prec: null,
      token: null,
    };
  }

  // ── lints ─────────────────────────────────────────────────────────────

  private lint(term: Term): void {
    const lints = this.lang.spec.lints;
    const assocNone = this.lang.spec.assocNone;
    const provable = this.lang.provableSort;

    walkTerm(term, (node, bound) => {
      if (node.kind === "variable") {
        if (
          lints.includes("closed-sentences") &&
          !node.binder &&
          !bound.has(node.name)
        ) {
          this.report("free_variable", { name: node.name }, node.span);
        }

        return;
      }

      // The chain refusal: an operand produced by an operator at the same
      // assoc-none level, without its own brackets, has no reading.
      if (
        typeof node.prec === "number" &&
        assocNone.has(node.prec) &&
        (node.fixity === "infixl" || node.fixity === "infixr")
      ) {
        for (const arg of node.args) {
          if (
            arg.kind === "app" &&
            typeof arg.prec === "number" &&
            arg.prec === node.prec &&
            (arg.fixity === "infixl" || arg.fixity === "infixr") &&
            !arg.grouped
          ) {
            const operator =
              arg.token ?? this.canonicalToken(arg.term) ?? arg.term;

            this.report("chain_refused", { operator }, arg.span);
          }
        }
      }

      if (lints.includes("parenthesize-binary-only") && node.grouped) {
        const binderSorts = this.lang.spec.terms
          .get(node.term)
          ?.binders.map(binderSort);
        const connective =
          (node.fixity === "infixl" || node.fixity === "infixr") &&
          provable !== null &&
          binderSorts !== undefined &&
          binderSorts.length === 2 &&
          binderSorts.every((sort) => sort === provable);

        if (!connective) {
          this.report(
            "group_binary_only",
            {},
            {
              start: node.span.start,
              end: node.span.start + 1,
            },
          );
        }
      }
    });
  }

  /** The last-declared notation token for a term — its canonical spelling. */
  private canonicalToken(term: string): string | null {
    let token: string | null = null;

    for (const notation of this.lang.spec.notations) {
      if (notation.term === term && notation.form === "simple") {
        token = notation.token;
      }
    }

    return token;
  }
}
