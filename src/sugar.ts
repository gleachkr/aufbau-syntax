/**
 * The bidirectional token-rewrite layer — `@syntax rewrite` rules.
 *
 * Forward (desugaring, before the parser): each rule makes one
 * left-to-right pass over the text, matching at token boundaries only.
 * Where a rule matches, its template is spliced in — literals in their own
 * spelling, captures copied from the source — separated by spaces so the
 * result re-scans cleanly. No fixpoints: matching resumes *after* each
 * replacement, and rules run in declaration order, so the layer terminates
 * by construction. An origin map carries every rewritten offset back to
 * the source, so diagnostics and term spans point at what the writer
 * actually typed.
 *
 * Backward (resugaring, after the display printer): the same rules run
 * inverted — template as pattern, pattern as replacement — in reverse
 * declaration order, joined tight, skipping `input-only` rules. A linear
 * rule is a lens: the Quine rule `( ?x:var ) => ∀ ?x` read backward *is*
 * the display convention that writes `∀x` as `(x)`.
 *
 * Captures match single letter tokens: by family class name, or by any
 * leaf family whose sort coerces into the named sort. The layer is
 * deliberately regular — nesting facts belong to the parser.
 */

import type { SurfaceLanguage } from "./parse";
import type {
  RewriteRule,
  RuleCapture,
  RuleLiteral,
  RuleTemplateElement,
} from "./reader/annotations";
import type { Reading } from "./scan";

/**
 * The matcher's pattern element: the reader's, plus an optional separator
 * on a capture — inverted `?ts,*` references match separator-interleaved
 * repeats (`x , y`), which the forward syntax has no way to write.
 */
type MatchElement =
  | RuleLiteral
  | (RuleCapture & { readonly separator?: string | null });

export interface Desugared {
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

function letterMatchesClass(
  lang: SurfaceLanguage,
  reading: Reading & { kind: "letter" },
  klass: string,
): boolean {
  if (reading.family.class === klass) {
    return true;
  }

  const info = lang.familyInfo.get(reading.family.class);

  if (info === undefined) {
    return false;
  }

  // The sort reading: any *leaf* letter whose sort coerces into the named
  // sort. An argument-taking letter is not a leaf.
  if (!info.isVariable && info.argBinders.length > 0) {
    return false;
  }

  return info.sort === klass || lang.coerce(info.sort, klass) !== null;
}

function matchCapture(
  lang: SurfaceLanguage,
  text: string,
  position: number,
  klass: string,
): { captured: Captured; end: number } | null {
  const point = lang.scanner.at(text, position);
  const reading = point.readings.find(
    (r): r is Reading & { kind: "letter" } =>
      r.kind === "letter" && letterMatchesClass(lang, r, klass),
  );

  if (reading === undefined || reading.kind !== "letter") {
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
): RuleMatch | null {
  const captures = new Map<string, Captured[]>();
  let at = position;

  for (const element of pattern) {
    if (element.kind === "literal") {
      const point = lang.scanner.at(text, at);
      const reading = point.readings.find(
        (r) => r.kind === "token" && r.token === element.token,
      );

      if (reading === undefined) {
        return null;
      }

      at = point.start + reading.length;
      continue;
    }

    const taken: Captured[] = [];
    const first = matchCapture(lang, text, at, element.class);

    if (first !== null) {
      taken.push(first.captured);
      at = first.end;

      if (element.quantifier === "+") {
        const separator =
          "separator" in element ? (element.separator ?? null) : null;

        for (;;) {
          let next = at;

          if (separator !== null) {
            const point = lang.scanner.at(text, next);
            const sepReading = point.readings.find(
              (r) => r.kind === "token" && r.token === separator,
            );

            if (sepReading === undefined) {
              break;
            }

            next = point.start + sepReading.length;
          }

          const more = matchCapture(lang, text, next, element.class);

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
): Desugared {
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
    const point = lang.scanner.at(text, position);

    copy(position, point.start);

    if (point.atEnd) {
      position = text.length;
      break;
    }

    const match = matchRule(lang, pattern, text, point.start);

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

    // Advance one whole token (the longest reading), staying on
    // boundaries; an unrecognized character passes through untouched.
    const step = Math.max(1, ...point.readings.map((r) => r.length));

    copy(point.start, point.start + step);
    position = point.start + step;
  }

  return { text: out, origin: outOrigin };
}

/** The template read as a pattern: references become captures. */
function invertTemplate(rule: RewriteRule): readonly MatchElement[] | null {
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
function invertPattern(rule: RewriteRule): readonly RuleTemplateElement[] {
  return rule.pattern.map((element) =>
    element.kind === "literal"
      ? element
      : { kind: "reference", name: element.name, separator: null },
  );
}

/**
 * Apply every rewrite rule forward, in declaration order, returning the
 * desugared text and the offset map back to the source.
 */
export function desugar(lang: SurfaceLanguage, text: string): Desugared {
  let current: Desugared = {
    text,
    origin: [...text].map((_, index) => index),
  };

  for (const rule of lang.spec.rewrites) {
    current = applyRule(
      lang,
      current.text,
      current.origin,
      rule.pattern,
      rule.template,
      " ",
    );
  }

  return current;
}

/**
 * Apply every invertible rule backward over display text, last declared
 * first, joining replacements tight (display is character-level anyway).
 */
export function resugar(lang: SurfaceLanguage, text: string): string {
  let current = text;

  for (const rule of [...lang.spec.rewrites].reverse()) {
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
    ).text;
  }

  return current;
}

/** A rewritten-text span mapped back to source offsets. */
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
