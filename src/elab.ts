/**
 * The bidirectional token-elaboration layer — `@syntax elab` rules.
 *
 * Forward (elaboration, before the parser): each rule makes one
 * left-to-right pass over the text, matching at chunk boundaries only.
 * Where a rule matches, its template is spliced in — literals in their own
 * spelling, captures copied from the source — separated by spaces so the
 * result re-scans cleanly. No fixpoints: matching resumes *after* each
 * replacement, and rules run in declaration order, so the layer terminates
 * by construction. An origin map carries every emitted offset back to
 * the source, so diagnostics and term spans point at what the writer
 * actually typed.
 *
 * Backward (delaboration, after the display printer): the same rules run
 * inverted — template as pattern, pattern as replacement — in reverse
 * declaration order, joined tight, skipping `input-only` rules. A linear
 * rule is a lens: the Quine rule `( ?x:var ) => ∀ ?x` read backward *is*
 * the display convention that writes `∀x` as `(x)`.
 *
 * Captures match single lexicon names — a `@vars` token or a nullary
 * declared term — whose sort coerces into the capture's named sort. A
 * literal matches a whole chunk, which need not be declared vocabulary at
 * all: the layer exists to accept surface forms the MM0 grammar rejects.
 * It is deliberately regular — nesting facts belong to the parser.
 *
 * **The three commitments.** What an author has to reason about is that
 * this layer decides, and the parser then inherits the decision as fact —
 * the parser backtracks over ambiguity, but only over what reaches it.
 *
 *   - *Leftmost*: the first match at the earliest scan point wins, and the
 *     span it consumed is replaced and never re-examined.
 *   - *Greedy*: a `+` capture takes the maximum it can and never gives one
 *     back to let the rest of the pattern match.
 *   - *One sweep per rule*, in declaration order, so a later rule sees
 *     what earlier rules emitted, and never the other way round.
 *
 * The hazard those three add up to: a rule may eat a span that had another
 * reading. Prefer patterns anchored by a leading literal — a spelling the
 * author chose — over capture-initial ones, which fire wherever the sorts
 * line up. The dialect where even that is not enough is one with both
 * letter-spelled quantifiers and juxtaposed predication, where `Ax` is
 * genuinely both `∀x` and A-applied-to-x; there, juxtaposition has to be a
 * parser behavior (`@syntax juxtaposed`), as it is for Magnus.
 */

import type { SurfaceLanguage } from "./parse.js";
import type {
  ElabRule,
  RuleCapture,
  RuleLiteral,
  RuleTemplateElement,
} from "./reader/annotations.js";
import type { Reading, Scope } from "./scan.js";

const NO_SCOPE: Scope = new Map();

/**
 * The matcher's pattern element: the reader's, plus an optional separator
 * on a capture — inverted `?ts,*` references match separator-interleaved
 * repeats (`x , y`), which the forward syntax has no way to write.
 */
type MatchElement =
  | RuleLiteral
  | (RuleCapture & { readonly separator?: string | null });

export interface Elaborated {
  /** For each offset of `text`, the source offset it came from. */
  readonly origin: readonly number[];
  readonly text: string;
}

interface Captured {
  readonly start: number;
  readonly text: string;
}

interface RuleMatch {
  readonly captures: ReadonlyMap<string, readonly Captured[]>;
  readonly end: number;
}

function nameMatchesSort(
  lang: SurfaceLanguage,
  reading: Reading & { kind: "name" },
  sort: string,
): boolean {
  if (reading.ref.kind === "var") {
    const from = reading.ref.sort;

    return from === sort || lang.coerce(from, sort) !== null;
  }

  // A *leaf* term: nullary, its sort coercing into the named one. A term
  // that takes arguments is not a leaf.
  const info = lang.spec.terms.get(reading.ref.term);

  if (info === undefined || info.binders.some((binder) => !binder.binds)) {
    return false;
  }

  return (
    info.returnSort === sort || lang.coerce(info.returnSort, sort) !== null
  );
}

function matchCapture(
  lang: SurfaceLanguage,
  text: string,
  position: number,
  klass: string,
  scope: Scope,
): { captured: Captured; end: number } | null {
  const point = lang.scanner.at(text, position, scope);
  const reading = point.readings.find(
    (r): r is Reading & { kind: "name" } =>
      r.kind === "name" && nameMatchesSort(lang, r, klass),
  );

  if (reading === undefined || reading.kind !== "name") {
    return null;
  }

  return {
    captured: { start: point.start, text: reading.name },
    end: point.start + reading.length,
  };
}

function matchRule(
  lang: SurfaceLanguage,
  pattern: readonly MatchElement[],
  text: string,
  position: number,
  scope: Scope,
): RuleMatch | null {
  const captures = new Map<string, Captured[]>();
  let at = position;

  for (const element of pattern) {
    if (element.kind === "literal") {
      const point = lang.scanner.at(text, at, scope);

      // A literal matches the *chunk*, declared vocabulary or not. Elab
      // exists to accept surface forms the MM0 grammar rejects — the Quine
      // rule makes `(x)` mean something no declaration mentions — so
      // constraining its pieces to declared tokens would be a half-measure
      // with nothing behind it. Anchoring is unaffected: the chunk's
      // boundaries were fixed by the delimiters before any lookup.
      if (point.chunk !== element.token) {
        return null;
      }

      at = point.start + point.chunk.length;
      continue;
    }

    const taken: Captured[] = [];
    const first = matchCapture(lang, text, at, element.class, scope);

    if (first !== null) {
      taken.push(first.captured);
      at = first.end;

      if (element.quantifier === "+") {
        const separator =
          "separator" in element ? (element.separator ?? null) : null;

        for (;;) {
          let next = at;

          if (separator !== null) {
            const point = lang.scanner.at(text, next, scope);
            const sepReading = point.readings.find(
              (r) => r.kind === "token" && r.token === separator,
            );

            if (sepReading === undefined) {
              break;
            }

            next = point.start + sepReading.length;
          }

          const more = matchCapture(lang, text, next, element.class, scope);

          if (more === null) {
            break;
          }

          taken.push(more.captured);
          at = more.end;
        }
      }
    }

    if (taken.length === 0 && element.quantifier !== "?") {
      return null;
    }

    captures.set(element.name, taken);
  }

  return { captures, end: at };
}

interface Emission {
  readonly origin: number[];
  readonly text: string;
}

function emitTemplate(
  template: readonly RuleTemplateElement[],
  captures: ReadonlyMap<string, readonly Captured[]>,
  matchStart: number,
  originOf: (index: number) => number,
  separator: " " | "",
): Emission {
  const pieces: { text: string; start: number }[] = [];

  for (const element of template) {
    if (element.kind === "literal") {
      pieces.push({ text: element.token, start: matchStart });
      continue;
    }

    const taken = captures.get(element.name) ?? [];

    taken.forEach((captured, index) => {
      if (index > 0 && element.separator !== null) {
        pieces.push({ text: element.separator, start: matchStart });
      }

      pieces.push({ text: captured.text, start: captured.start });
    });
  }

  let text = "";
  const origin: number[] = [];

  pieces.forEach((piece, index) => {
    if (index > 0 && separator === " ") {
      text += " ";
      origin.push(originOf(piece.start));
    }

    for (let i = 0; i < piece.text.length; i += 1) {
      origin.push(originOf(piece.start + i));
    }

    text += piece.text;
  });

  return { text, origin };
}

/** One pass of one rule, in the given direction. */
function applyRule(
  lang: SurfaceLanguage,
  text: string,
  origin: readonly number[],
  pattern: readonly MatchElement[],
  template: readonly RuleTemplateElement[],
  separator: " " | "",
  scope: Scope,
): Elaborated {
  const originOf = (index: number): number =>
    origin[index] ?? origin[origin.length - 1] ?? 0;
  let out = "";
  const outOrigin: number[] = [];
  let position = 0;

  const copy = (from: number, to: number): void => {
    for (let i = from; i < to && i < text.length; i += 1) {
      out += text[i];
      outOrigin.push(originOf(i));
    }
  };

  while (position < text.length) {
    const point = lang.scanner.at(text, position, scope);

    copy(position, point.start);

    if (point.atEnd) {
      position = text.length;
      break;
    }

    const match = matchRule(lang, pattern, text, point.start, scope);

    if (match !== null && match.end > point.start) {
      const emitted = emitTemplate(
        template,
        match.captures,
        point.start,
        originOf,
        separator,
      );

      out += emitted.text;
      outOrigin.push(...emitted.origin);
      position = match.end;
      continue;
    }

    // Advance one whole chunk, so the pass only ever resumes on a
    // segmentation boundary; a chunk the vocabulary does not recognize
    // passes through untouched.
    const step = Math.max(1, point.chunk.length);

    copy(point.start, point.start + step);
    position = point.start + step;
  }

  return { text: out, origin: outOrigin };
}

/** The template read as a pattern: references become captures. */
function invertTemplate(rule: ElabRule): readonly MatchElement[] | null {
  const classes = new Map<string, { class: string; plural: boolean }>();

  for (const element of rule.pattern) {
    if (element.kind === "capture") {
      classes.set(element.name, {
        class: element.class,
        plural: element.quantifier === "+",
      });
    }
  }

  const inverted: MatchElement[] = [];

  for (const element of rule.template) {
    if (element.kind === "literal") {
      inverted.push(element);
      continue;
    }

    const known = classes.get(element.name);

    if (known === undefined) {
      return null;
    }

    inverted.push({
      kind: "capture",
      name: element.name,
      class: known.class,
      quantifier: known.plural ? "+" : "",
      separator: element.separator,
    });
  }

  return inverted;
}

/** The pattern read as a template: captures become plain references. */
function invertPattern(rule: ElabRule): readonly RuleTemplateElement[] {
  return rule.pattern.map((element) =>
    element.kind === "literal"
      ? element
      : { kind: "reference", name: element.name, separator: null },
  );
}

/**
 * Apply every elaboration rule forward, in declaration order, returning
 * the elaborated text and the offset map back to the source.
 */
export function elaborate(
  lang: SurfaceLanguage,
  text: string,
  scope: Scope = NO_SCOPE,
): Elaborated {
  let current: Elaborated = {
    text,
    origin: [...text].map((_, index) => index),
  };

  for (const rule of lang.spec.elabRules) {
    current = applyRule(
      lang,
      current.text,
      current.origin,
      rule.pattern,
      rule.template,
      " ",
      scope,
    );
  }

  return current;
}

/**
 * Apply every invertible rule backward over display text, last declared
 * first, joining replacements tight (display is character-level anyway).
 *
 * No scope, deliberately. Engine mode does not delaborate — it is the whole
 * output path a schematic theorem's text takes — so threading one here
 * would buy nothing today and cost `printTerm` a parameter. A display
 * printer that has to re-sugar a metavariable correctly is the point at
 * which to add it.
 */
export function delaborate(lang: SurfaceLanguage, text: string): string {
  let current = text;

  for (const rule of [...lang.spec.elabRules].reverse()) {
    if (rule.inputOnly) {
      continue;
    }

    const pattern = invertTemplate(rule);

    if (pattern === null) {
      continue;
    }

    current = applyRule(
      lang,
      current,
      [...current].map((_, index) => index),
      pattern,
      invertPattern(rule),
      "",
      NO_SCOPE,
    ).text;
  }

  return current;
}

/** An elaborated-text span mapped back to source offsets. */
export function remapSpan(
  origin: readonly number[],
  span: { readonly start: number; readonly end: number },
): { start: number; end: number } {
  const last = origin[origin.length - 1] ?? 0;
  const start = origin[span.start] ?? last + 1;
  const end =
    span.end > span.start ? (origin[span.end - 1] ?? last) + 1 : start;

  return { start, end };
}
