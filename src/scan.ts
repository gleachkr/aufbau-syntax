/**
 * The surface scanner: character-level maximal munch over a spec's token
 * vocabulary and letter families.
 *
 * Where MM0's own lexer splits math strings on whitespace and single-byte
 * delimiters, students write textbook notation with no spaces at all —
 * `∀xF(x)`, `~~P`, `AxEy~R(x,y)`. So this scanner asks, at each position:
 * which declared notation token starts here (longest match wins), and which
 * letter families claim this character (with its subscript, when the family
 * writes them)? A position can answer *both* — Calgary's `A` is at once a
 * spelling of ∀ and a predicate letter — so the scanner reports alternative
 * readings, each with its own length, and the parser picks by context.
 */

import type { Span } from "./diagnostics";
import type { LetterFamily, Spec } from "./reader/spec";

export type Reading =
  | {
      readonly kind: "letter";
      readonly family: LetterFamily;
      /** The full name, subscript included: `F_12`, `P0`. */
      readonly name: string;
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
  /** Longest-first notation reading, then letter readings. Empty at end of
   * input or on an unrecognized character. */
  readonly readings: readonly Reading[];
  readonly atEnd: boolean;
}

function isDigit(ch: string): boolean {
  return ch >= "0" && ch <= "9";
}

export class Scanner {
  /** Notation and grouping tokens, longest first. */
  private readonly tokens: readonly string[];
  private readonly families: readonly LetterFamily[];

  constructor(spec: Spec) {
    const vocabulary = new Set<string>();

    for (const notation of spec.notations) {
      if (notation.form === "simple") {
        vocabulary.add(notation.token);
      } else {
        for (const literal of notation.literals) {
          if (literal.kind === "constant") {
            vocabulary.add(literal.token);
          }
        }
      }
    }

    for (const [open, close] of spec.groupingPairs) {
      vocabulary.add(open);
      vocabulary.add(close);
    }

    this.tokens = [...vocabulary].sort((a, b) => b.length - a.length);
    this.families = spec.families;
  }

  /**
   * The alternative readings at `position` in `text`, after skipping
   * whitespace. The list is ordered: the longest matching notation token
   * first, then one letter reading per claiming family.
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

    const ch = text[start] ?? "";

    for (const family of this.families) {
      if (!family.letters.has(ch)) {
        continue;
      }

      let length = 1;

      if (family.subscripts === "underscore") {
        // `x_1` — the underscore joins only when digits follow, so `F_` is
        // the letter F and then a stray underscore, as in Carnap.
        if (text[start + 1] === "_" && isDigit(text[start + 2] ?? "")) {
          let end = start + 2;

          while (isDigit(text[end] ?? "")) {
            end += 1;
          }

          length = end - start;
        }
      } else if (family.subscripts === "bare") {
        let end = start + 1;

        while (isDigit(text[end] ?? "")) {
          end += 1;
        }

        length = end - start;
      }

      readings.push({
        kind: "letter",
        family,
        name: text.slice(start, start + length),
        length,
      });
    }

    return { start, readings, atEnd: false };
  }

  /** The span a reading occupies from a scan point. */
  span(point: ScanPoint, reading: Reading): Span {
    return { start: point.start, end: point.start + reading.length };
  }
}
