/**
 * The `@syntax` annotation vocabulary — the "little extra metadata" that
 * turns an MM0 theory into a full surface-language spec.
 *
 * Annotations ride MM0's `--|` doc-comment channel, the same one Aufbau uses
 * for `@acui`, `@congr`, and the rest. Anything that is not `@syntax` is
 * *foreign*: preserved untouched for whoever owns it, never interpreted
 * here. The library also owns stripping `@syntax` lines before a theory is
 * handed to the engine, which currently rejects annotations it does not
 * know.
 *
 * Attachment rules (checked by the spec builder, not here):
 *   - `family` attaches to a `sort` (binding variables of that sort) or to
 *     a placeholder `term` (each letter elaborates to a copy of it);
 *   - `role` attaches to a `term`;
 *   - everything else is spec-wide and may sit on any statement.
 */

import { type Diagnostic, diagnostic, type Span } from "../diagnostics";

export const LINT_NAMES = [
  "parenthesize-binary-only",
  "closed-sentences",
] as const;

export type LintName = (typeof LINT_NAMES)[number];

/**
 * How a letter family writes subscripts: `x_1` (Carnap's first-order
 * convention), `P1` (its propositional one), or not at all.
 */
export type SubscriptForm = "bare" | "none" | "underscore";

/** A capture in a rewrite pattern: `?ts:tm+` — name, class, quantifier. */
export interface RuleCapture {
  readonly kind: "capture";
  readonly name: string;
  /** A letter-family class or a sort name; resolved by the sugar layer. */
  readonly class: string;
  readonly quantifier: "" | "+" | "?";
}

export interface RuleLiteral {
  readonly kind: "literal";
  readonly token: string;
}

export type RulePatternElement = RuleCapture | RuleLiteral;

/** A capture reference in a rewrite template: `?ts` or joined `?ts,*`. */
export interface RuleReference {
  readonly kind: "reference";
  readonly name: string;
  /** For a `+` capture, the token to join repeats with; null joins bare. */
  readonly separator: string | null;
}

export type RuleTemplateElement = RuleLiteral | RuleReference;

export interface RewriteRule {
  readonly inputOnly: boolean;
  readonly pattern: readonly RulePatternElement[];
  readonly span: Span;
  readonly template: readonly RuleTemplateElement[];
}

export type SyntaxAnnotation =
  | {
      readonly kind: "assoc-none";
      readonly prec: number;
    }
  | {
      readonly kind: "brackets";
      readonly pairs: readonly (readonly [string, string])[];
    }
  | {
      readonly kind: "display-drop-outer-parens";
    }
  | {
      readonly kind: "display-rotate-brackets";
      readonly pairs: readonly (readonly [string, string])[];
    }
  | {
      readonly kind: "family";
      readonly class: string;
      /** Arguments are glued straight on (`Fxy`), Carnap's no-paren style. */
      readonly juxtaposed: boolean;
      readonly letters: ReadonlySet<string>;
      readonly subscripts: SubscriptForm;
    }
  | {
      readonly kind: "lint";
      readonly name: LintName;
    }
  | {
      readonly kind: "rewrite";
      readonly rule: RewriteRule;
    }
  | {
      readonly kind: "role";
      readonly role: string;
    };

const TEMPLATES: Record<string, string> = {
  syntax_unknown_subcommand: "unknown @syntax subcommand {subcommand}",
  syntax_bad_family:
    "@syntax family wants: family <class> <letters…> [subscripts]",
  syntax_bad_letters: "cannot read letter specification {letters}",
  syntax_bad_brackets:
    "bracket pairs come as: <open> <close> [<open> <close>…]",
  syntax_bad_assoc_none: "@syntax assoc-none wants one precedence number",
  syntax_unknown_lint: "unknown lint {name}; known lints: {known}",
  syntax_bad_display:
    "@syntax display wants drop-outer-parens or rotate-brackets <pairs…>",
  syntax_bad_rewrite:
    "@syntax rewrite wants: rewrite $ <pattern> $ => $ <template> $ [input-only]",
  syntax_bad_pattern_element: "cannot read pattern element {element}",
  syntax_bad_template_element: "cannot read template element {element}",
  syntax_bad_role: "@syntax role wants one role name",
};

function fail(
  id: string,
  params: Record<string, string>,
  span: Span,
): { annotation: null; diagnostic: Diagnostic } {
  const template = TEMPLATES[id] ?? id;
  return {
    annotation: null,
    diagnostic: diagnostic(id, template, params, span),
  };
}

function ok(annotation: SyntaxAnnotation): {
  annotation: SyntaxAnnotation;
  diagnostic: null;
} {
  return { annotation, diagnostic: null };
}

export type SyntaxAnnotationResult =
  | { readonly annotation: SyntaxAnnotation; readonly diagnostic: null }
  | { readonly annotation: null; readonly diagnostic: Diagnostic };

/**
 * Read a letter specification: each word is either a range `a-z` (by code
 * point) or a literal run of letters (`stuvwxyz`).
 */
function parseLetters(words: readonly string[]): Set<string> | null {
  const letters = new Set<string>();

  for (const word of words) {
    const points = [...word];

    if (points.length === 3 && points[1] === "-") {
      const from = points[0]?.codePointAt(0);
      const to = points[2]?.codePointAt(0);

      if (from === undefined || to === undefined || from > to) {
        return null;
      }

      for (let cp = from; cp <= to; cp += 1) {
        letters.add(String.fromCodePoint(cp));
      }
      continue;
    }

    for (const point of points) {
      if (point === "-") {
        return null;
      }
      letters.add(point);
    }
  }

  return letters.size > 0 ? letters : null;
}

function parsePairs(
  words: readonly string[],
): (readonly [string, string])[] | null {
  if (words.length === 0 || words.length % 2 !== 0) {
    return null;
  }

  const pairs: (readonly [string, string])[] = [];

  for (let i = 0; i < words.length; i += 2) {
    const open = words[i];
    const close = words[i + 1];

    if (open === undefined || close === undefined || open === close) {
      return null;
    }

    pairs.push([open, close]);
  }

  return pairs;
}

const CAPTURE =
  /^\?([A-Za-z_][A-Za-z0-9_]*):([A-Za-z_][A-Za-z0-9_]*)([+?]?)$/;
const REFERENCE = /^\?([A-Za-z_][A-Za-z0-9_]*)(?:(.)\*)?$/;

function parsePattern(text: string): readonly RulePatternElement[] | string {
  const elements: RulePatternElement[] = [];

  for (const word of text.split(/\s+/).filter((w) => w.length > 0)) {
    if (word.startsWith("?")) {
      const match = CAPTURE.exec(word);

      if (match === null) {
        return word;
      }

      elements.push({
        kind: "capture",
        name: match[1] ?? "",
        class: match[2] ?? "",
        quantifier: (match[3] ?? "") as "" | "+" | "?",
      });
      continue;
    }

    elements.push({ kind: "literal", token: word });
  }

  return elements;
}

function parseTemplate(
  text: string,
): readonly RuleTemplateElement[] | string {
  const elements: RuleTemplateElement[] = [];

  for (const word of text.split(/\s+/).filter((w) => w.length > 0)) {
    if (word.startsWith("?")) {
      const match = REFERENCE.exec(word);

      if (match === null) {
        return word;
      }

      elements.push({
        kind: "reference",
        name: match[1] ?? "",
        separator: match[2] ?? null,
      });
      continue;
    }

    elements.push({ kind: "literal", token: word });
  }

  return elements;
}

const REWRITE = /^\$(.*?)\$\s*=>\s*\$(.*?)\$\s*(input-only)?\s*$/s;

/**
 * Parse one annotation payload (the text after `--|`). Returns null for a
 * foreign annotation — anything that does not begin `@syntax`.
 */
export function parseSyntaxAnnotation(
  text: string,
  span: Span,
): SyntaxAnnotationResult | null {
  const trimmed = text.trim();

  if (!trimmed.startsWith("@syntax")) {
    return null;
  }

  const rest = trimmed.slice("@syntax".length).trim();
  const words = rest.split(/\s+/).filter((w) => w.length > 0);
  const subcommand = words[0];

  switch (subcommand) {
    case "family": {
      const klass = words[1];
      let subscripts: SubscriptForm = "none";
      let juxtaposed = false;
      let end = words.length;

      // Trailing flags, in any order: `subscripts`, `bare-subscripts`,
      // `juxtaposed`.
      for (;;) {
        const last = words[end - 1];

        if (last === "subscripts") {
          subscripts = "underscore";
        } else if (last === "bare-subscripts") {
          subscripts = "bare";
        } else if (last === "juxtaposed") {
          juxtaposed = true;
        } else {
          break;
        }

        end -= 1;
      }

      const letterWords = words.slice(2, end);

      if (klass === undefined || letterWords.length === 0) {
        return fail("syntax_bad_family", {}, span);
      }

      const letters = parseLetters(letterWords);

      if (letters === null) {
        return fail(
          "syntax_bad_letters",
          { letters: letterWords.join(" ") },
          span,
        );
      }

      return ok({
        kind: "family",
        class: klass,
        juxtaposed,
        letters,
        subscripts,
      });
    }

    case "brackets": {
      const pairs = parsePairs(words.slice(1));

      if (pairs === null) {
        return fail("syntax_bad_brackets", {}, span);
      }

      return ok({ kind: "brackets", pairs });
    }

    case "assoc-none": {
      const number = words[1];

      if (
        words.length !== 2 ||
        number === undefined ||
        !/^\d+$/.test(number)
      ) {
        return fail("syntax_bad_assoc_none", {}, span);
      }

      return ok({ kind: "assoc-none", prec: Number.parseInt(number, 10) });
    }

    case "lint": {
      const name = words[1];

      if (
        words.length !== 2 ||
        name === undefined ||
        !(LINT_NAMES as readonly string[]).includes(name)
      ) {
        return fail(
          "syntax_unknown_lint",
          { name: name ?? "", known: LINT_NAMES.join(", ") },
          span,
        );
      }

      return ok({ kind: "lint", name: name as LintName });
    }

    case "display": {
      if (words[1] === "drop-outer-parens" && words.length === 2) {
        return ok({ kind: "display-drop-outer-parens" });
      }

      if (words[1] === "rotate-brackets") {
        const pairs = parsePairs(words.slice(2));

        if (pairs !== null) {
          return ok({ kind: "display-rotate-brackets", pairs });
        }
      }

      return fail("syntax_bad_display", {}, span);
    }

    case "rewrite": {
      const match = REWRITE.exec(rest.slice("rewrite".length).trim());

      if (match === null) {
        return fail("syntax_bad_rewrite", {}, span);
      }

      const pattern = parsePattern(match[1] ?? "");

      if (typeof pattern === "string") {
        return fail("syntax_bad_pattern_element", { element: pattern }, span);
      }

      const template = parseTemplate(match[2] ?? "");

      if (typeof template === "string") {
        return fail(
          "syntax_bad_template_element",
          { element: template },
          span,
        );
      }

      return ok({
        kind: "rewrite",
        rule: {
          inputOnly: match[3] === "input-only",
          pattern,
          span,
          template,
        },
      });
    }

    case "role": {
      const role = words[1];

      if (words.length !== 2 || role === undefined) {
        return fail("syntax_bad_role", {}, span);
      }

      return ok({ kind: "role", role });
    }

    default:
      return fail(
        "syntax_unknown_subcommand",
        { subcommand: subcommand ?? "(none)" },
        span,
      );
  }
}
