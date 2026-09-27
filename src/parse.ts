/**
 * The surface parser: a faithful port of MM0's operator-precedence math
 * parser (mm0.md, "the dynamic parser"), running over the delimiter
 * scanner — MM0's own segmentation rule under a wider, declared delimiter
 * set — with exactly four declared extensions beyond the upstream
 * grammar:
 *
 *   1. **Grouping pairs** — `expression(max) → open expression(0) close`
 *      for every declared bracket pair, close matching open;
 *   2. **Refused operands** — a connective's `@syntax forbid` list rejects
 *      an unbracketed connective operand of the named shape, whatever
 *      associativity would otherwise allow (`P → Q → R` and `P ∧ Q → R`
 *      are both errors under forallx);
 *   3. **Adjacency** — a sort's `@syntax juxtaposed` combiner is an
 *      invisible infix operator: two adjacent expressions of its sort
 *      denote it (`ab` for `a*b`, `gf` for `g∘f`), at the precedence and
 *      associativity of the combiner's canonical infix notation;
 *   4. **Lints** — the closed set of post-parse checks
 *      (`parenthesize-binary-only`, `closed-sentences`).
 *
 * Constructor application is MM0's own production, `expression(1024) →
 * FUNC expression(max){n}` — `S x`, `pair a b`, `succ (succ x)` — with
 * two surface-side supersets in front of it: a lexicon name applied to
 * bracketed arguments (`S(x)`, `R(a,b)`), or elided-bare, or glued to
 * juxtaposed arguments, counts as `expression(max)`, so a textbook's
 * `F(a)` can sit anywhere an atom can. A token that is both a notation
 * and a lexicon name (Calgary's `A`) is disambiguated by backtracking,
 * notation reading first.
 *
 * mm0.md's slot-precedence rules are used exactly: a prefix notation's
 * intermediate arguments parse at max and its last at the notation's
 * precedence; a general notation's slot parses at max before a variable, at
 * `p+1` before a constant of precedence `p`, and at the head precedence
 * when last. Coercions are inserted along the (unique) path in the coercion
 * graph, per the spec.
 */

import { delimiterRules, isReachableChunk } from "./delimiters.js";
import { type Diagnostic, diagnostic, type Span } from "./diagnostics.js";
import { elaborate, remapSpan } from "./elab.js";
import type { NotationInfo, Spec, TermInfo } from "./reader/spec.js";
import type { Binder, TypeRef } from "./reader/statements.js";
import { type Reading, Scanner, type ScanPoint, type Scope } from "./scan.js";
import type { AppTerm, Term, VariableTerm } from "./term.js";
import { walkTerm } from "./term.js";

const TEMPLATES: Record<string, string> = {
  unrecognized_chunk: "“{chunk}” is not part of this language.",
  expected_formula: "Expected a formula.",
  expected_formula_found: "Expected a formula but found “{token}”.",
  unexpected_token: "Unexpected “{token}”.",
  expected_variable: "Expected a variable after the quantifier.",
  expected_bracket: "Expected “{bracket}”.",
  chain_refused:
    "“{operator}” cannot be repeated without parentheses; group it.",
  mix_refused:
    "“{inner}” and “{outer}” cannot be combined without parentheses.",
  nest_refused: "“{inner}” needs parentheses inside “{outer}”.",
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

export function precNum(prec: number | "max"): number {
  return prec === "max" ? Number.POSITIVE_INFINITY : prec;
}

/** mm0.md: bare constructor application is `expression(1024)`. */
const APPLICATION_PRECEDENCE = 1024;

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

export interface GeneralSlot {
  readonly binder: Binder;
  /** Index into the term's binder list this slot fills. */
  readonly index: number;
  readonly prec: number;
}

export type GeneralPart =
  | { readonly kind: "constant"; readonly token: string }
  | { readonly kind: "slot"; readonly slot: GeneralSlot };

/**
 * A general notation after its head, as the parser reads it: constants to
 * expect and slots to parse, each slot at mm0.md's P(lits, q) — max before
 * a variable, p+1 before a constant of precedence p, and q (the head
 * precedence) when it is the trailing slot. The printer reads the same
 * table, so what it decides needs no parentheses is what this parses.
 */
export function generalParts(
  notation: NotationInfo & { readonly form: "general" },
  headPrec: number | "max",
): readonly GeneralPart[] {
  const parts: GeneralPart[] = [];
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
        ? precNum(headPrec)
        : following.kind === "constant"
          ? precNum(following.prec) + 1
          : Number.POSITIVE_INFINITY;

    parts.push({ kind: "slot", slot: { binder, index, prec } });
  }

  return parts;
}

interface GeneralEntry {
  readonly kind: "general";
  readonly info: TermInfo;
  /** Interleaved constants (to expect) and slots (to parse), head dropped. */
  readonly parts: readonly GeneralPart[];
}

type HeadEntry = GeneralEntry | PrefixEntry;

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

/**
 * Which delimiter set cuts the input up. `surface` is student input, read
 * under the spec's `surfaceDelimiters`; `engine` is this library's own
 * engine-mode emission, read under the theory's own `delimiters` — the
 * counterpart of `printTerm`'s two modes.
 */
export type ParseMode = "engine" | "surface";

const EMPTY_SCOPE: Scope = new Map();

function binderSort(binder: Binder | undefined): string {
  if (binder === undefined || !("sort" in binder.type)) {
    return "";
  }

  return (binder.type as TypeRef).sort;
}

/** Everything derived from a Spec that parsing needs, built once. */
export class SurfaceLanguage {
  readonly spec: Spec;
  /** Student input: the wide surface delimiter set. */
  readonly scanner: Scanner;
  /** Engine text: the same vocabulary under the theory's own delimiters. */
  readonly engineScanner: Scanner;
  readonly heads = new Map<string, HeadEntry>();
  readonly infixes = new Map<string, InfixEntry>();
  readonly closeOf = new Map<string, string>();
  readonly closers = new Set<string>();
  /** Per sort, its `@syntax juxtaposed` combiner — adjacency's meaning. */
  readonly juxtaposedOf = new Map<string, TermInfo>();
  /**
   * Per sort, the operator the adjacency arc stands in for: the
   * combiner's canonical (last-declared) infix notation's entry. The arc
   * is that operator, written as nothing — same precedence, same
   * associativity — which is what keeps `ab⁻¹` and `a*b⁻¹` one tree.
   */
  readonly adjacencyOf = new Map<string, InfixEntry>();
  /** Per sort, its `@syntax elided` term — the unwritten argument. */
  readonly elidedOf = new Map<string, TermInfo>();
  /** Sorts some quantifier binds — whose variables *can* be captured. */
  readonly bindableSorts = new Set<string>();
  /**
   * The first sort the file marks `provable` — MM0's own way of saying
   * "assertable". It is `parse`'s default target sort and nothing else; a
   * caller that wants another sort names it, and a file with several
   * provable sorts is expected to.
   */
  readonly provableSort: string | null;
  /** Per term, its last-declared notation — the canonical spelling. */
  readonly canonical = new Map<string, NotationInfo>();
  readonly coercionNames = new Set<string>();
  private readonly coercionPaths = new Map<
    string,
    readonly string[] | null
  >();

  constructor(spec: Spec) {
    this.spec = spec;
    this.scanner = new Scanner(spec);
    this.engineScanner = new Scanner(spec, spec.delimiters);

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

      const parts = generalParts(notation, head.prec);

      this.heads.set(head.token, { kind: "general", info, parts });
    }

    for (const [open, close] of spec.groupingPairs) {
      this.closeOf.set(open, close);
      this.closers.add(close);
    }

    for (const term of spec.terms.values()) {
      if (term.juxtaposed) {
        this.juxtaposedOf.set(term.returnSort, term);
      }

      if (term.elided) {
        this.elidedOf.set(term.returnSort, term);
      }

      for (const binder of term.binders) {
        if (binder.binds) {
          this.bindableSorts.add(binderSort(binder));
        }
      }
    }

    // The canonical spelling is the last-declared notation the theory's
    // own delimiters can read back; a token a delimiter cuts through (`/\`
    // under `[x/t]`'s `/`) is dead — mm0.md forbids it — and only stands
    // when nothing else does.
    const rules = delimiterRules(spec.delimiters);
    const readable = (notation: NotationInfo): boolean =>
      (notation.form === "simple"
        ? [notation.token]
        : notation.literals.flatMap((literal) =>
            literal.kind === "constant" ? [literal.token] : [],
          )
      ).every((token) => isReachableChunk(token, rules));

    for (const notation of spec.notations) {
      const standing = this.canonical.get(notation.term);

      if (
        standing === undefined ||
        readable(notation) ||
        !readable(standing)
      ) {
        this.canonical.set(notation.term, notation);
      }
    }

    // Later notations overwrite earlier ones, so each sort's arc ends up
    // borrowing from the combiner's *last-declared* infix spelling — the
    // canonical one, Aufbau's rule everywhere else.
    for (const [sort, info] of this.juxtaposedOf) {
      for (const notation of spec.notations) {
        if (
          notation.term === info.name &&
          notation.form === "simple" &&
          notation.fixity !== "prefix"
        ) {
          const entry = this.infixes.get(notation.token);

          if (entry !== undefined) {
            this.adjacencyOf.set(sort, entry);
          }
        }
      }
    }

    for (const coercion of spec.coercions) {
      this.coercionNames.add(coercion.name);
    }

    this.provableSort =
      [...spec.sorts.values()].find((sort) =>
        sort.modifiers.includes("provable"),
      )?.name ?? null;
  }

  /**
   * A connective: an infix constructor closed over a `provable` sort —
   * two arguments of that sort, and a result of the same one. This is the
   * class forallx's bracket convention and the display printer's spacing
   * both key on: `∧` is one; `=` over terms is not (its arguments are of
   * another sort); a turnstile from two formulas to a judgement is not
   * (it does not return what it takes); and the argument comma is not
   * (`seq` is not provable), which is what keeps `R(a,b)` from printing
   * as `R((a , b))`.
   *
   * Nothing here privileges one sort. A theory that states judgements in
   * a provable sort of their own gets a judgement-level conjunction
   * spaced and bracketed on the same terms as a formula-level one, which
   * is right.
   */
  isConnective(term: string): boolean {
    const info = this.spec.terms.get(term);
    const notation = this.canonical.get(term);

    return (
      info !== undefined &&
      this.isProvableSort(info.returnSort) &&
      notation !== undefined &&
      notation.form === "simple" &&
      notation.fixity !== "prefix" &&
      info.binders.length === 2 &&
      info.binders.every(
        (binder) =>
          !binder.binds &&
          "sort" in binder.type &&
          binder.type.sort === info.returnSort,
      )
    );
  }

  /** Whether the sort carries MM0's `provable` modifier. */
  isProvableSort(sort: string): boolean {
    return this.spec.sorts.get(sort)?.modifiers.includes("provable") === true;
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

  /**
   * Parse surface text. `sort` is what the result is read at: the text
   * must parse to that sort, or coerce into it, or it is refused. It
   * defaults to `provableSort` — the first sort the file marks `provable`,
   * MM0's own way of saying "assertable" — which is the whole story for a
   * spec with one such sort. A file with several (a theory whose
   * judgements are `Γ ⊢ φ` in a sort of their own) has a genuine choice to
   * make per call, and the caller is who knows: a translation exercise
   * reads at the formula sort, a proof widget at the judgement sort.
   *
   * `lints: false` skips the spec's refusal conventions (bracket
   * discipline, chain refusal, closed sentences) — for reading text that
   * is grammatical but not surface-idiomatic.
   *
   * `mode: "engine"` reads this library's own engine-mode output instead:
   * the theory's delimiters rather than the surface set, no elaboration,
   * and lints off unless asked for. Engine text is whitespace-separated
   * and fully parenthesized, so it needs no wide delimiter set — and a
   * surface elab rule would misread it, Quine's `( ?x:var )` happily
   * eating the `(x)` inside `(F (x))`.
   *
   * `scope` is the enclosing theorem's binders, name to sort. A name in
   * scope reads as a variable of that sort and *stops* reading as whatever
   * the lexicon declares it to be — which is what the engine's own math
   * parser does, and the only way text belonging to a schematic theorem
   * can be read at all. Without it, `theorem mp (a b: wff)` has its
   * metavariables silently reinterpreted (or, more happily, refused) by a
   * lexicon that has never heard of them. See {@link Scope}.
   */
  parse(
    text: string,
    options: {
      readonly lints?: boolean;
      readonly mode?: ParseMode;
      readonly scope?: Scope;
      readonly sort?: string;
    } = {},
  ): ParseResult {
    const mode = options.mode ?? "surface";
    const lints = options.lints ?? mode === "surface";
    const sort = options.sort ?? this.provableSort;
    const scope = options.scope ?? EMPTY_SCOPE;

    if (mode === "engine") {
      return new Parse(
        this,
        this.engineScanner,
        text,
        lints,
        sort,
        scope,
        mode,
      ).run();
    }

    if (this.spec.elabRules.length === 0) {
      return new Parse(
        this,
        this.scanner,
        text,
        lints,
        sort,
        scope,
        mode,
      ).run();
    }

    // Elaborate first, then map every span in the outcome back through
    // the origin map, so nothing downstream sees elaborated offsets.
    const elaborated = elaborate(this, text, scope);
    const result = new Parse(
      this,
      this.scanner,
      elaborated.text,
      lints,
      sort,
      scope,
      mode,
    ).run();
    const diagnostics = result.diagnostics.map((diag) => ({
      ...diag,
      span: remapSpan(elaborated.origin, diag.span),
    }));

    if (!result.ok) {
      return { ok: false, diagnostics };
    }

    const remapTerm = (term: Term): Term =>
      term.kind === "variable"
        ? { ...term, span: remapSpan(elaborated.origin, term.span) }
        : {
            ...term,
            span: remapSpan(elaborated.origin, term.span),
            args: term.args.map(remapTerm),
          };

    return { ok: true, term: remapTerm(result.term), diagnostics };
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
    private readonly scanner: Scanner,
    private readonly text: string,
    private readonly lintsEnabled: boolean,
    /** The sort the result is read at; null leaves the target open. */
    private readonly sort: string | null,
    /** The enclosing theorem's binders, shadowing the lexicon. */
    private readonly scope: Scope,
    /** Engine text writes every operator, so the adjacency arc is off. */
    private readonly mode: ParseMode,
  ) {}

  /** The scan point at `position`, classified in this parse's scope. */
  private at(position: number): ScanPoint {
    return this.scanner.at(this.text, position, this.scope);
  }

  run(): ParseResult {
    const parsed = this.parseExpr(0);

    if (parsed !== null) {
      const point = this.at(this.position);

      if (!point.atEnd) {
        const trial = this.bestTrialFailure;

        if (trial !== null && trial.end > point.start) {
          this.diagnostics.push(trial.diag);
        } else if (point.readings.length === 0) {
          this.report(
            "unrecognized_chunk",
            { chunk: point.chunk },
            { start: point.start, end: point.start + point.chunk.length },
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
    const target = this.sort;

    if (target !== null && term.sort !== target) {
      const wrapped = this.coerceTerm(term, target);

      if (wrapped === null) {
        this.report(
          "term_not_sentence",
          { actual: term.sort, expected: target },
          term.span,
        );
        return { ok: false, diagnostics: this.diagnostics };
      }

      term = wrapped;
    }

    if (this.lintsEnabled) {
      this.lint(term);
    }

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

  /**
   * An `attempt` whose failure leaves no trace in `bestTrialFailure`.
   * For trials that fail routinely on perfectly good input — every
   * expression ends somewhere, so most adjacency offers are declined — a
   * diagnostic from one must never displace the error the writer
   * actually made.
   */
  private attemptQuiet<T>(body: () => T | null): T | null {
    const saved = this.bestTrialFailure;
    const result = this.attempt(body);

    if (result === null) {
      this.bestTrialFailure = saved;
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
      const point = this.at(this.position);

      if (point.atEnd) {
        return left;
      }

      const reading = point.readings.find((r) => r.kind === "token");
      const entry =
        reading !== undefined && reading.kind === "token"
          ? this.lang.infixes.get(reading.token)
          : undefined;

      if (reading === undefined || entry === undefined || entry.prec < min) {
        // No operator readable here. Adjacency may still continue the
        // expression — but never *across* a written infix: an operator
        // the writer spelled out, even one too loose for this slot, is
        // theirs, and gluing past it would silently reparse the input.
        const glued: Term | null =
          entry === undefined ? this.glueAdjacent(left, min) : null;

        if (glued === null) {
          return left;
        }

        left = glued;
        continue;
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

  /**
   * The adjacency arc: continue `left` through its sort's `@syntax
   * juxtaposed` combiner without an operator having been written — `ab`
   * for `a*b`, `gf` for `g∘f`. The arc is the combiner's canonical infix
   * notation spelled as nothing, so it binds exactly as the written
   * operator would ({@link SurfaceLanguage.adjacencyOf}); the sort guard
   * is what keeps two adjacent *formulas* apart in a spec whose combiner
   * lives at the term level.
   *
   * Offered, never insisted on: the right-hand side runs under a quiet
   * attempt, and any failure — nothing parseable there, a sort that will
   * not coerce — just ends the expression with the diagnostics as they
   * were. Surface mode only; engine text writes every operator and an
   * arc there could only misread.
   */
  private glueAdjacent(left: Term, min: number): Term | null {
    if (this.mode === "engine" || this.lang.adjacencyOf.size === 0) {
      return null;
    }

    const point = this.at(this.position);

    if (
      point.atEnd ||
      !point.readings.some((reading) => this.isViablePrimary(reading))
    ) {
      return null;
    }

    // Candidate combiners nearest coercion first, so a leaf eligible for
    // two sorts glues at the closest one — deterministic, like every
    // other ordered alternative in this parser.
    const candidates = [...this.lang.adjacencyOf.entries()]
      .map(([sort, entry]) => ({
        entry,
        path: this.lang.coerce(left.sort, sort),
      }))
      .filter(
        (
          candidate,
        ): candidate is { entry: InfixEntry; path: readonly string[] } =>
          candidate.path !== null,
      )
      .sort((a, b) => a.path.length - b.path.length);

    for (const { entry } of candidates) {
      if (entry.prec < min) {
        continue;
      }

      const glued = this.attemptQuiet(() => this.glueRight(left, entry));

      if (glued !== null) {
        return glued;
      }
    }

    return null;
  }

  /** One adjacency trial: the invisible operator's right-hand side. */
  private glueRight(left: Term, entry: InfixEntry): Term | null {
    const right = this.parseExpr(
      entry.fixity === "infixl" ? entry.prec + 1 : entry.prec,
    );

    if (right === null) {
      return null;
    }

    const binders = entry.info.binders;
    const coercedLeft = this.coerceTerm(left, binderSort(binders[0]));
    const coercedRight = this.coerceTerm(right, binderSort(binders[1]));

    if (coercedLeft === null || coercedRight === null) {
      return null;
    }

    return {
      kind: "app",
      term: entry.info.name,
      args: [coercedLeft, coercedRight],
      sort: entry.info.returnSort,
      span: { start: left.span.start, end: right.span.end },
      grouped: false,
      fixity: entry.fixity,
      prec: entry.prec,
      // Nothing was written: the printer must not claim a token was.
      token: null,
    };
  }

  private parsePrimary(min: number): Term | null {
    const point = this.at(this.position);

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

    // The chunk's boundaries were fixed by the delimiters, so the whole of
    // what the writer wrote between them is what nothing recognizes — not
    // just its first character.
    if (point.readings.length === 0) {
      return this.report(
        "unrecognized_chunk",
        { chunk: point.chunk },
        { start: point.start, end: point.start + point.chunk.length },
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
    if (reading.kind === "name") {
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
    if (reading.kind === "name") {
      return this.parseName(start, reading, min);
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

    const point = this.at(this.position);
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
        const point = this.at(this.position);
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
    const point = this.at(this.position);
    const reading = point.readings.find(
      (r): r is Reading & { kind: "name" } =>
        r.kind === "name" && r.ref.kind === "var" && r.ref.sort === sort,
    );

    if (reading === undefined || reading.kind !== "name") {
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

  /**
   * A lexicon name: a `@vars` token (a variable of its sort), or any
   * declared term — a sentence letter, predicate, function symbol, or
   * constant, or a notated term written by name. Each of a term's arguments
   * comes one of four ways, tried in this order: parenthesized
   * (application syntax, so the argument is not marked `grouped` and the
   * binary-only lint does not apply inside; the canonical pair is always
   * the first declared one); juxtaposed, when the argument sort has an
   * `@syntax juxtaposed` combiner; not at all, when it has an `@syntax
   * elided` term; or bare — MM0's own `FUNC expression(max){n}`, so
   * `S x` and `pair a b` read exactly as the engine reads them. The
   * declared shapes go first because they are declared: a spec that
   * elides a sort's unit has said what a bare letter means there.
   * Context settles the `A`-as-∀ ambiguity exactly as in Carnap: the
   * quantifier reading was tried first, and fell through to here only if
   * it failed.
   */
  private parseName(
    start: number,
    reading: Reading & { kind: "name" },
    min: number,
  ): Term | null {
    this.position = start + reading.length;

    if (reading.ref.kind === "var") {
      return {
        kind: "variable",
        name: reading.name,
        sort: reading.ref.sort,
        span: { start, end: this.position },
        grouped: false,
        binder: false,
      };
    }

    const info = this.lang.spec.terms.get(reading.ref.term);

    if (info === undefined) {
      return this.report(
        "expected_formula_found",
        { token: reading.name },
        { start, end: start + reading.length },
      );
    }

    const argBinders = info.binders.filter((binder) => !binder.binds);
    const args: Term[] = [];

    for (const binder of info.binders) {
      const target = binderSort(binder);

      // A bound binder is filled positionally, by a variable of its sort —
      // `sb x t p`, `all x p` — as in every MM0 application.
      if (binder.binds) {
        if (min > APPLICATION_PRECEDENCE) {
          return this.report(
            "needs_parentheses",
            { token: reading.name },
            { start, end: start + reading.length },
          );
        }

        const variable = this.expectBoundVariable(target);

        if (variable === null) {
          return null;
        }

        args.push(variable);
        continue;
      }

      const combiner =
        argBinders.length === 1
          ? this.lang.juxtaposedOf.get(target)
          : undefined;
      const point = this.at(this.position);
      const open = this.lang.spec.groupingPairs[0]?.[0] ?? "(";
      const close = this.lang.spec.groupingPairs[0]?.[1] ?? ")";
      const openReading = point.readings.find(
        (r) => r.kind === "token" && r.token === open,
      );

      // Under a *compound* combiner a leading `(` is not application
      // syntax but the first glue operand, so the glue loop below owns
      // it — that is what lets `F(x)(y)` fold instead of stranding the
      // second group.
      if (
        openReading !== undefined &&
        combiner?.juxtaposedCompound !== true
      ) {
        this.position = point.start + openReading.length;

        const arg = this.parseExpr(0);

        if (arg === null) {
          return null;
        }

        const closePoint = this.at(this.position);
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

        const coerced = this.coerceOrReport(arg, target);

        if (coerced === null) {
          return null;
        }

        args.push(coerced);
        continue;
      }

      // Juxtaposed gluing — `Fxy`, the pre-2019 forallx shape. Operands
      // (self-delimiting single-token expressions, plus parenthesized
      // groups under a compound combiner) are consumed greedily while
      // they coerce into the argument sort; several fold through the
      // sort's declared combiner.
      if (combiner !== undefined) {
        const leaves: Term[] = [];

        for (;;) {
          const leaf = this.glueOperand(target, combiner.juxtaposedCompound);

          if (leaf === null) {
            break;
          }

          leaves.push(leaf);
        }

        const first = leaves[0];

        if (first !== undefined) {
          let folded = first;

          for (const leaf of leaves.slice(1)) {
            folded = {
              kind: "app",
              term: combiner.name,
              args: [folded, leaf],
              sort: combiner.returnSort,
              span: { start: folded.span.start, end: leaf.span.end },
              grouped: false,
              fixity: null,
              prec: null,
              token: null,
            };
          }

          args.push(folded);
          continue;
        }
        // No operand at all: fall through to elision, so a bare letter
        // can still be a sentence letter in a juxtaposed dialect.
      }

      const elided = this.lang.elidedOf.get(target);

      if (elided !== undefined) {
        args.push({
          kind: "app",
          term: elided.name,
          args: [],
          sort: elided.returnSort,
          span: { start, end: start + reading.length },
          grouped: false,
          fixity: null,
          prec: null,
          token: null,
        });
        continue;
      }

      // Bare application. It is `expression(1024)`, so it cannot fill a
      // max slot — another application's argument, a prefix notation's
      // intermediate argument: `succ succ x` is refused here just as the
      // engine refuses it, and `succ (succ x)` is the spelling.
      if (min > APPLICATION_PRECEDENCE) {
        return this.report(
          "needs_parentheses",
          { token: reading.name },
          { start, end: start + reading.length },
        );
      }

      const arg = this.parseExpr(Number.POSITIVE_INFINITY);

      if (arg === null) {
        return null;
      }

      const coerced = this.coerceOrReport(arg, target);

      if (coerced === null) {
        return null;
      }

      args.push(coerced);
    }

    return {
      kind: "app",
      term: reading.name,
      args,
      sort: info.returnSort,
      span: { start, end: this.position },
      grouped: false,
      fixity: null,
      prec: null,
      token: null,
    };
  }

  /**
   * One juxtaposed operand: a self-delimiting single-token expression — a
   * variable, a nullary lexicon name, or a nullary notation (an
   * empty-set-style constant) — whose sort coerces into the target.
   *
   * Under `@syntax juxtaposed compound`, a parenthesized group is an
   * operand too — `F(x)(y)`, `(lambda x)a`. That stays opt-in rather
   * than general because under a variadic sequence with an elided unit
   * (Magnus's `seq`) a group is already spoken for: `P(Q)` is
   * parenthesized application, and a second reading of the same text is
   * exactly the ambiguity this parser exists to refuse.
   */
  private glueOperand(target: string, compound: boolean): Term | null {
    const point = this.at(this.position);

    for (const reading of point.readings) {
      if (compound && reading.kind === "token") {
        const close = this.lang.closeOf.get(reading.token);

        if (close !== undefined) {
          const group = this.attemptQuiet(() => {
            const inner = this.parseGroup(point.start, close, reading.length);

            return inner === null ? null : this.coerceTerm(inner, target);
          });

          if (group !== null) {
            return group;
          }

          continue;
        }
      }

      if (reading.kind === "name") {
        if (reading.ref.kind === "var") {
          if (this.lang.coerce(reading.ref.sort, target) === null) {
            continue;
          }

          this.position = point.start + reading.length;

          return this.coerceOrReport(
            {
              kind: "variable",
              name: reading.name,
              sort: reading.ref.sort,
              span: { start: point.start, end: this.position },
              grouped: false,
              binder: false,
            },
            target,
          );
        }

        const info = this.lang.spec.terms.get(reading.ref.term);

        if (
          info === undefined ||
          info.binders.some((binder) => !binder.binds) ||
          this.lang.coerce(info.returnSort, target) === null
        ) {
          continue;
        }

        this.position = point.start + reading.length;

        return this.coerceOrReport(
          {
            kind: "app",
            term: info.name,
            args: [],
            sort: info.returnSort,
            span: { start: point.start, end: this.position },
            grouped: false,
            fixity: null,
            prec: null,
            token: null,
          },
          target,
        );
      }

      const head = this.lang.heads.get(reading.token);

      if (
        head?.kind === "general" &&
        head.parts.length === 0 &&
        head.info.binders.length === 0 &&
        this.lang.coerce(head.info.returnSort, target) !== null
      ) {
        this.position = point.start + reading.length;

        return this.coerceOrReport(
          {
            kind: "app",
            term: head.info.name,
            args: [],
            sort: head.info.returnSort,
            span: { start: point.start, end: this.position },
            grouped: false,
            fixity: "general",
            prec: null,
            token: reading.token,
          },
          target,
        );
      }
    }

    return null;
  }

  // ── lints ─────────────────────────────────────────────────────────────

  private lint(term: Term): void {
    const lints = this.lang.spec.lints;
    // A scoped name is bound where it stands: the enclosing theorem binds
    // it. `theorem unimp {x: var} …` may perfectly well state a line with
    // `x` free *in the line*, and calling that an open sentence would
    // refuse the very proofs the scope exists to allow.
    const scoped = new Set(this.scope.keys());

    walkTerm(term, (node, bound) => {
      if (node.kind === "variable") {
        // A leaf of a sort no quantifier binds — a constant from a
        // `@vars` pool, like Calgary's names — cannot be *free*: freedom
        // is only meaningful where binding is possible.
        if (
          lints.includes("closed-sentences") &&
          !node.binder &&
          this.lang.bindableSorts.has(node.sort) &&
          !bound.has(node.name) &&
          !scoped.has(node.name)
        ) {
          this.report("free_variable", { name: node.name }, node.span);
        }

        return;
      }

      this.refuseOperands(node);

      if (lints.includes("parenthesize-binary-only") && node.grouped) {
        // The same class the printer brackets — see `isConnective`, which
        // this reads through the parse's own fixity rather than the
        // canonical notation's.
        const connective =
          (node.fixity === "infixl" || node.fixity === "infixr") &&
          this.lang.isConnective(node.term);

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

  /**
   * Refuse the unbracketed operands this connective says it will not take.
   *
   * An operand that is itself an infix connective, and carries no brackets
   * of its own, stands in exactly one of three relations to the operator
   * above it — the same term repeated (`chain`), a different term on the
   * same rung (`mix`), or a term on a tighter rung (`nest`) — and the spec
   * names which of them the operator refuses. Nothing here consults
   * associativity: the parse has already happened, and what is at stake is
   * whether the reading it found is one the textbook lets a student write
   * without brackets.
   *
   * There is no *looser*-rung case to consider. Precedence climbing parses
   * an operand of an operator at `p` with `min ≥ p` and admits only
   * operators at `prec ≥ min`, so an unbracketed operand's own operator is
   * always at `p` or tighter.
   */
  private refuseOperands(node: AppTerm): void {
    const refuses = this.lang.spec.terms.get(node.term)?.refuses;

    if (
      refuses === undefined ||
      refuses.size === 0 ||
      typeof node.prec !== "number" ||
      (node.fixity !== "infixl" && node.fixity !== "infixr")
    ) {
      return;
    }

    for (const arg of node.args) {
      if (
        arg.kind !== "app" ||
        arg.grouped ||
        typeof arg.prec !== "number" ||
        (arg.fixity !== "infixl" && arg.fixity !== "infixr") ||
        !this.lang.isConnective(arg.term)
      ) {
        continue;
      }

      const relation =
        arg.term === node.term
          ? "chain"
          : arg.prec === node.prec
            ? "mix"
            : "nest";

      if (!refuses.has(relation)) {
        continue;
      }

      const inner = arg.token ?? this.canonicalToken(arg.term) ?? arg.term;
      const outer = node.token ?? this.canonicalToken(node.term) ?? node.term;

      // The span is the operand's, not the operator's: the brackets the
      // reader has to add go around exactly that much of the input.
      this.report(
        relation === "chain" ? "chain_refused" : `${relation}_refused`,
        relation === "chain" ? { operator: inner } : { inner, outer },
        arg.span,
      );
    }
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
