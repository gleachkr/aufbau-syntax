/**
 * The `@syntax` annotation vocabulary — the "little extra metadata" that
 * turns an MM0 theory into a full surface-language spec.
 *
 * Annotations ride MM0's `--|` doc-comment channel, the same one Aufbau uses
 * for `@acui`, `@congr`, `@rewrite`, and the rest. Anything that is not
 * `@syntax` is *foreign*: preserved untouched for whoever owns it, never
 * interpreted here. The library also owns stripping `@syntax` lines before a theory is
 * handed to the engine, which currently rejects annotations it does not
 * know.
 *
 * Attachment rules (checked by the spec builder, not here):
 *   - `juxtaposed` attaches to a binary term whose arguments and result
 *     share one sort (adjacency of that sort's expressions denotes it);
 *   - `elided` attaches to a nullary term (supplied when an argument of
 *     its sort is missing, dropped again when printing);
 *   - `role` attaches to a `sort`, a `term`, or a `def`;
 *   - everything else is spec-wide and may sit on any statement.
 *
 * The lexicon itself needs no `@syntax` at all: letters are ordinary term
 * declarations, and variables ride the engine's own `@vars` annotation.
 */

import { type Diagnostic, diagnostic, type Span } from "../diagnostics.js";

export const LINT_NAMES = [
  "parenthesize-binary-only",
  "closed-sentences",
] as const;

export type LintName = (typeof LINT_NAMES)[number];

/** A capture in an elab pattern: `?ts:tm+` — name, class, quantifier. */
export interface RuleCapture {
  readonly kind: "capture";
  readonly name: string;
  /** A sort name; a leaf whose sort coerces into it matches. */
  readonly class: string;
  readonly quantifier: "" | "+" | "?";
}

export interface RuleLiteral {
  readonly kind: "literal";
  readonly token: string;
}

export type RulePatternElement = RuleCapture | RuleLiteral;

/** A capture reference in an elab template: `?ts` or joined `?ts,*`. */
export interface RuleReference {
  readonly kind: "reference";
  readonly name: string;
  /** For a `+` capture, the token to join repeats with; null joins bare. */
  readonly separator: string | null;
}

export type RuleTemplateElement = RuleLiteral | RuleReference;

export interface ElabRule {
  readonly inputOnly: boolean;
  readonly pattern: readonly RulePatternElement[];
  readonly span: Span;
  readonly template: readonly RuleTemplateElement[];
}

export type SyntaxAnnotation =
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
      /** A bidirectional token rule: elaborate in, delaborate out. */
      readonly kind: "elab";
      readonly rule: ElabRule;
    }
  | {
      /**
       * Surface delimiters: where a chunk of *student* input ends. Same
       * shape and same meaning as MM0's own `delimiter` statement, and
       * unioned with it — but an entry may be any string, not just a single
       * byte, so `∧` and `<->` can self-delimit where the engine's
       * byte table cannot hold them.
       */
      readonly kind: "delimiter";
      readonly left: readonly string[];
      readonly right: readonly string[];
    }
  | {
      /** Supplied when an argument of its sort is missing; drops on print. */
      readonly kind: "elided";
    }
  | {
      /** Adjacency of this combiner's sort denotes it — `Fxy`, `ab`. */
      readonly kind: "juxtaposed";
    }
  | {
      readonly kind: "lint";
      readonly name: LintName;
    }
  | {
      /**
       * `@syntax forbid chain mix nest` — which unbracketed operands this
       * connective refuses. Unlisted permits, so an unmarked term refuses
       * nothing, which is the ordinary reading.
       */
      readonly kind: "forbid";
      readonly relations: readonly OperandRelation[];
    }
  | {
      readonly kind: "role";
      readonly role: string;
    };

/**
 * How an unbracketed connective operand sits under the connective above it.
 *
 * The three cases are exhaustive. Precedence climbing parses an operand of
 * an operator at `p` with `min ≥ p` and admits only operators at
 * `prec ≥ min`, so an unbracketed operand's own operator is never *looser*
 * than its parent's; and a same-rung operand can only fall on the
 * associative side, the other side parsing at `p + 1`. There is no fourth
 * relation to name.
 */
export type OperandRelation =
  /** The same term repeated: `A ∧ B ∧ C`. */
  | "chain"
  /** A different term on the same rung: `A ∧ B ∨ C`. */
  | "mix"
  /** A term on a tighter rung: `A → B ∧ C`. */
  | "nest";

const OPERAND_RELATIONS: readonly OperandRelation[] = [
  "chain",
  "mix",
  "nest",
];

const TEMPLATES: Record<string, string> = {
  syntax_unknown_subcommand: "unknown @syntax subcommand {subcommand}",
  syntax_bad_flag: "@syntax {flag} takes no arguments",
  syntax_bad_forbid: "@syntax forbid wants one or more of: {known}",
  syntax_bad_brackets:
    "bracket pairs come as: <open> <close> [<open> <close>…]",
  syntax_unknown_lint: "unknown lint {name}; known lints: {known}",
  syntax_bad_display:
    "@syntax display wants drop-outer-parens or rotate-brackets <pairs…>",
  syntax_bad_delimiter:
    "@syntax delimiter wants: delimiter $ <entries…> $, or delimiter $ <left…> $ $ <right…> $",
  syntax_empty_delimiter: "a @syntax delimiter math string must list entries",
  syntax_bad_elab:
    "@syntax elab wants: elab $ <pattern> $ => $ <template> $ [input-only]",
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

const ELAB = /^\$(.*?)\$\s*=>\s*\$(.*?)\$\s*(input-only)?\s*$/s;

/** `$ … $`, or `$ left… $ $ right… $` — MM0's own two shapes. */
const DELIMITER = /^\$([^$]*)\$(?:\s*\$([^$]*)\$)?\s*$/;

/**
 * Every entry written out, one at a time. There is deliberately no range
 * shorthand: a spike of `A-Z`-style ranges read `<->` as the range `<`…`>`
 * and silently turned one delimiter into three. A declaration that decides
 * how input is cut up is worth its verbosity.
 */
function delimiterEntries(text: string): string[] {
  return text.split(/\s+/).filter((entry) => entry.length > 0);
}

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
    case "juxtaposed":
    case "elided": {
      if (words.length !== 1) {
        return fail("syntax_bad_flag", { flag: subcommand }, span);
      }

      return ok({ kind: subcommand });
    }

    case "forbid": {
      const relations = words.slice(1);

      if (
        relations.length === 0 ||
        !relations.every((relation): relation is OperandRelation =>
          (OPERAND_RELATIONS as readonly string[]).includes(relation),
        )
      ) {
        return fail(
          "syntax_bad_forbid",
          { known: OPERAND_RELATIONS.join(", ") },
          span,
        );
      }

      return ok({ kind: "forbid", relations });
    }

    case "brackets": {
      const pairs = parsePairs(words.slice(1));

      if (pairs === null) {
        return fail("syntax_bad_brackets", {}, span);
      }

      return ok({ kind: "brackets", pairs });
    }

    case "delimiter": {
      const match = DELIMITER.exec(rest.slice("delimiter".length).trim());

      if (match === null) {
        return fail("syntax_bad_delimiter", {}, span);
      }

      const first = delimiterEntries(match[1] ?? "");
      const second =
        match[2] === undefined ? null : delimiterEntries(match[2]);

      if (first.length === 0 || second?.length === 0) {
        return fail("syntax_empty_delimiter", {}, span);
      }

      // One list means both sides, as in MM0.
      return ok({ kind: "delimiter", left: first, right: second ?? first });
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

    case "elab": {
      const match = ELAB.exec(rest.slice("elab".length).trim());

      if (match === null) {
        return fail("syntax_bad_elab", {}, span);
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
        kind: "elab",
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
