/**
 * The surface scanner: character-level maximal munch over a spec's token
 * vocabulary and lexicon names.
 *
 * Where MM0's own lexer splits math strings on whitespace and single-byte
 * delimiters, students write textbook notation with no spaces at all —
 * `∀xF(x)`, `~~P`, `AxEy~R(x,y)`. So this scanner asks, at each position:
 * which declared notation token starts here (longest match wins), and which
 * lexicon name? A position can answer *both* — Calgary's `A` is at once a
 * spelling of ∀ and the predicate letter A — so the scanner reports
 * alternative readings, each with its own length, and the parser picks by
 * context.
 *
 * The vocabulary it classifies against is `surfaceVocabulary`, derived from
 * the spec rather than annotated.
 */

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
  /** Position after leading whitespace; readings start here. */
  readonly start: number;
  /** Longest-first notation reading, then the longest name reading. Empty
   * at end of input or on an unrecognized character. */
  readonly readings: readonly Reading[];
  readonly atEnd: boolean;
}

export class Scanner {
  /** Notation and grouping tokens, longest first. */
  private readonly tokens: readonly string[];
  /** Lexicon names, longest first, each with what it refers to. */
  private readonly names: readonly (readonly [string, NameRef])[];

  constructor(spec: Spec) {
    const { names, tokens } = surfaceVocabulary(spec);

    this.tokens = [...tokens].sort((a, b) => b.length - a.length);
    this.names = [...names.entries()].sort(
      (a, b) => b[0].length - a[0].length,
    );
  }

  /**
   * The alternative readings at `position` in `text`, after skipping
   * whitespace. The list is ordered: the longest matching notation token
   * first, then the longest matching name.
   */
  at(text: string, position: number): ScanPoint {
    let start = position;

    while (start < text.length && /\s/.test(text[start] ?? "")) {
      start += 1;
    }

    if (start >= text.length) {
      return { start, readings: [], atEnd: true };
    }

    const readings: Reading[] = [];

    for (const token of this.tokens) {
      if (text.startsWith(token, start)) {
        readings.push({ kind: "token", token, length: token.length });
        break;
      }
    }

    for (const [name, ref] of this.names) {
      if (text.startsWith(name, start)) {
        readings.push({ kind: "name", name, ref, length: name.length });
        break;
      }
    }

    return { start, readings, atEnd: false };
  }

  /** The span a reading occupies from a scan point. */
  span(point: ScanPoint, reading: Reading): Span {
    return { start: point.start, end: point.start + reading.length };
  }
}
