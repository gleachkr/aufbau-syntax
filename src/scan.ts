/**
 * The surface scanner: segment, then classify.
 *
 * Segmentation comes from the declared delimiter set alone — MM0's own
 * tokenizer rule, in `delimiters.ts` — and never consults the term or
 * notation tables. Only once a chunk's boundaries are fixed is the chunk
 * looked up: as a notation token, as a lexicon name, or as both. Calgary's
 * `A` is at once a spelling of ∀ and the predicate letter A, so the scanner
 * reports both readings and the parser picks by backtracking.
 *
 * The order is the whole point. Under the character-level maximal munch
 * this replaces, declaring a term could silently re-read an existing
 * string: adding `term ab: tm;` to Magnus turned `Fab` from `F` of `a` and
 * `b` into `F` of `ab`. Boundaries fixed before any lookup cannot do that,
 * which is exactly what MM0 buys by keeping `delimiter` separate from
 * `notation`.
 *
 * The delimiter set is a parameter: student input is read under the spec's
 * `surfaceDelimiters`, and this library's own engine-mode output under the
 * theory's own `delimiters`.
 *
 * Classification is where a parse's {@link Scope} applies. Segmentation is
 * not: a binder shadows what a chunk *means*, never where the chunk ends,
 * so a theorem cannot change how its own statement is cut up.
 */

import {
  chunkAt,
  type DelimiterRules,
  type DelimiterSet,
  delimiterRules,
  segment,
} from "./delimiters.js";
import type { Span } from "./diagnostics.js";
import type { Spec } from "./reader/spec.js";
import { type NameRef, surfaceVocabulary } from "./vocabulary.js";

export type { NameRef } from "./vocabulary.js";

/**
 * Names a parse holds in scope, each with the sort it stands at — the
 * binders of the theorem the text belongs to.
 *
 * A theorem's binders shadow the file's declarations for the length of that
 * theorem, and a surface parse that does not know them reads them as the
 * declarations they collide with: `theorem mp (a b: wff)` turns the
 * metavariable `a` into whatever `a` means in the lexicon. A scope closes
 * that, and it is not the parser's to infer — the caller holds the theorem.
 */
export type Scope = ReadonlyMap<string, string>;

const NO_SCOPE: Scope = new Map();

export type Reading =
  | {
      readonly kind: "name";
      readonly name: string;
      readonly ref: NameRef;
      readonly length: number;
    }
  | {
      readonly kind: "token";
      readonly token: string;
      readonly length: number;
    };

export interface ScanPoint {
  /** Position after leading whitespace; the chunk starts here. */
  readonly start: number;
  /** The chunk at `start`, before classification. Empty at end of input. */
  readonly chunk: string;
  /** The notation reading, then the name reading — whichever the chunk
   * answers to. Empty at end of input, or when it answers to neither. */
  readonly readings: readonly Reading[];
  readonly atEnd: boolean;
}

export class Scanner {
  private readonly rules: DelimiterRules;
  /** Notation and grouping tokens. */
  private readonly tokens: ReadonlySet<string>;
  /** Lexicon names, each with what it refers to. */
  private readonly names: ReadonlyMap<string, NameRef>;

  constructor(spec: Spec, delimiters: DelimiterSet = spec.surfaceDelimiters) {
    const { names, tokens } = surfaceVocabulary(spec);

    this.rules = delimiterRules(delimiters);
    this.names = names;
    this.tokens = tokens;
  }

  /**
   * The chunk at `position` in `text`, after skipping whitespace, and what
   * it can be read as: the notation token first, then the name.
   *
   * `scope` acts on the *name* reading, and only on it. A scoped chunk
   * reads as a variable of its sort and stops reading as whatever the
   * lexicon declares it to be — replacing that reading rather than
   * outranking it, since a fallback would let `P snil` back in silently
   * whenever the metavariable reading happened to fail.
   *
   * Its notation reading is untouched, and keeps its priority. Calgary
   * spells ∀ `A`, so a theorem binding `(A: wff)` still has to be able to
   * quantify; which reading a given occurrence wants is settled by the
   * parser's backtracking, exactly as the `A`-the-quantifier /
   * `A`-the-predicate-letter ambiguity already is. Notation is not part of
   * what a binder shadows — MM0's own math parser reads a constant as a
   * constant however the enclosing theorem binds its variables.
   */
  at(text: string, position: number, scope: Scope = NO_SCOPE): ScanPoint {
    let start = position;

    while (start < text.length && /\s/.test(text[start] ?? "")) {
      start += 1;
    }

    if (start >= text.length) {
      return { start, chunk: "", readings: [], atEnd: true };
    }

    const chunk = chunkAt(text, start, this.rules);
    const readings: Reading[] = [];

    if (this.tokens.has(chunk)) {
      readings.push({ kind: "token", token: chunk, length: chunk.length });
    }

    const scoped = scope.get(chunk);
    const ref: NameRef | undefined =
      scoped === undefined
        ? this.names.get(chunk)
        : { kind: "var", sort: scoped };

    if (ref !== undefined) {
      readings.push({ kind: "name", name: chunk, ref, length: chunk.length });
    }

    return { start, chunk, readings, atEnd: false };
  }

  /**
   * The chunk sequence of `text`, before any classification — the view
   * that shows what the delimiters did, independently of what the spec's
   * vocabulary happens to contain.
   */
  chunks(text: string): string[] {
    return segment(text, this.rules);
  }

  /** The span a reading occupies from a scan point. */
  span(point: ScanPoint, reading: Reading): Span {
    return { start: point.start, end: point.start + reading.length };
  }
}
