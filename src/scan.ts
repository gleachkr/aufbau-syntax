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
 * The name vocabulary is derived, not annotated: every token in a sort's
 * `@vars` pool, and every declared term that has no notation of its own,
 * binds nothing, and is not a coercion. A term *with* a notation is
 * spelled by that notation; a term without one is spelled by its name —
 * MM0's own application rule, read character-level.
 */

import type { Span } from "./diagnostics.js";
import type { Spec } from "./reader/spec.js";

export type NameRef =
  | { readonly kind: "term"; readonly term: string }
  | { readonly kind: "var"; readonly sort: string };

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
    const vocabulary = new Set<string>();
    const notated = new Set<string>();

    for (const notation of spec.notations) {
      notated.add(notation.term);

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

    const coercions = new Set(spec.coercions.map((c) => c.name));
    const names = new Map<string, NameRef>();

    for (const sort of spec.sorts.values()) {
      for (const token of sort.vars) {
        names.set(token, { kind: "var", sort: sort.name });
      }
    }

    for (const term of spec.terms.values()) {
      if (
        !notated.has(term.name) &&
        !coercions.has(term.name) &&
        !term.binders.some((binder) => binder.binds) &&
        !names.has(term.name)
      ) {
        names.set(term.name, { kind: "term", term: term.name });
      }
    }

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
