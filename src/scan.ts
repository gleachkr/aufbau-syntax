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
   * it can be read as: the notation token first, then the lexicon name.
   */
  at(text: string, position: number): ScanPoint {
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

    const ref = this.names.get(chunk);

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
