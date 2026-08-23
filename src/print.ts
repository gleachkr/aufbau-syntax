/**
 * The printer: a term tree back to text, in one of two modes.
 *
 * **Display** is what a reader sees, in the textbook's own conventions:
 * the canonical spelling of each constructor (the last-declared notation,
 * Aufbau's rule), *full* parenthesization of sentential connectives with
 * the outermost pair optionally dropped (`@syntax display
 * drop-outer-parens`) — Carnap's convention, not minimal-parens — spaces
 * around connectives, everything else set tight (`¬P`, `∀x`, `a=b`,
 * `R(a,b)`).
 *
 * **Engine** is what the Aufbau compiler's own math parser reads: the same
 * canonical spellings, every token whitespace-separated, every compound
 * operand parenthesized, and coercion wrappers omitted (the engine
 * re-inserts them). Lexicon names print as constructor application —
 * `F ((x , y))`, `P (snil)` — which is valid at any slot once
 * parenthesized, and elided arguments are written out in full.
 *
 * Display mode presumes the spec's term-level infixes (identity, argument
 * commas) bind tighter than its prefixes, as every textbook's do; a spec
 * violating that should print through engine mode. The round-trip law —
 * parsing a printed term yields the same tree — is enforced by test for
 * both modes.
 */

import { delaborate } from "./elab.js";
import type { SurfaceLanguage } from "./parse.js";
import type { Term } from "./term.js";

export type PrintMode = "display" | "engine";

export function printTerm(
  lang: SurfaceLanguage,
  term: Term,
  mode: PrintMode = "display",
): string {
  let printed = render(lang, term, mode);

  if (
    mode === "display" &&
    lang.spec.display.dropOuterParens &&
    printed.startsWith("(") &&
    printed.endsWith(")")
  ) {
    printed = printed.slice(1, -1);
  }

  if (mode === "display" && lang.spec.elabRules.length > 0) {
    printed = delaborate(lang, printed);
  }

  return printed;
}

function render(lang: SurfaceLanguage, term: Term, mode: PrintMode): string {
  if (term.kind === "variable") {
    return term.name;
  }

  // Coercions are the parser's bookkeeping; both readers re-derive them.
  if (term.args.length === 1 && lang.coercionNames.has(term.term)) {
    const inner = term.args[0];

    if (inner !== undefined) {
      return render(lang, inner, mode);
    }
  }

  const notation = lang.canonical.get(term.term);

  if (notation === undefined) {
    return renderApplication(lang, term, mode);
  }

  if (notation.form === "simple" && notation.fixity !== "prefix") {
    const left = operand(lang, term.args[0], mode);
    const right = operand(lang, term.args[1], mode);

    if (mode === "engine") {
      return `(${left} ${notation.token} ${right})`;
    }

    // Connectives are spaced and self-parenthesized (the full-paren
    // convention); term-level infixes close up and stand bare.
    return lang.isConnective(term.term)
      ? `(${left} ${notation.token} ${right})`
      : `${left}${notation.token}${right}`;
  }

  if (notation.form === "simple") {
    const args = term.args.map((arg) => operand(lang, arg, mode));

    return mode === "engine"
      ? `(${[notation.token, ...args].join(" ")})`
      : `${notation.token}${args.join("")}`;
  }

  // General notation: constants and binder slots, in literal order.
  const pieces: string[] = [];

  for (const literal of notation.literals) {
    if (literal.kind === "constant") {
      pieces.push(literal.token);
      continue;
    }

    const index = notation.binders.findIndex(
      (binder) => binder.name === literal.name,
    );
    const arg = term.args[index];

    if (arg !== undefined) {
      pieces.push(operand(lang, arg, mode));
    }
  }

  if (mode === "engine") {
    return term.args.length === 0
      ? pieces.join(" ")
      : `(${pieces.join(" ")})`;
  }

  return pieces.join("");
}

/**
 * A term with no notation prints as application — the lexicon's shape.
 * Display elides an `@syntax elided` argument (bare `P`), flattens a
 * juxtaposed argument into glued leaves (`Rxy`), and otherwise sets each
 * argument in its own parentheses (`R(a,b)`, the comma coming from the
 * argument's own notation). Engine mode writes application in full —
 * `P (snil)`, `R ((x , y))` — which the compiler reads at expression(max).
 */
function renderApplication(
  lang: SurfaceLanguage,
  term: Term & { kind: "app" },
  mode: PrintMode,
): string {
  if (term.args.length === 0) {
    return term.term;
  }

  if (mode === "engine") {
    const args = term.args.map((arg) => {
      const rendered = render(lang, arg, mode);

      return rendered.startsWith("(") ? rendered : `(${rendered})`;
    });

    return [term.term, ...args].join(" ");
  }

  const sole = term.args.length === 1 ? term.args[0] : undefined;

  if (sole !== undefined) {
    const bare = uncoerced(lang, sole);
    const elided = lang.elidedOf.get(sole.sort);

    if (
      elided !== undefined &&
      bare.kind === "app" &&
      bare.term === elided.name
    ) {
      return term.term;
    }

    const combiner = lang.juxtaposedOf.get(sole.sort);

    if (combiner !== undefined) {
      const groupers = lang.spec.groupingPairs.flat();
      const leaves: string[] = [];
      const flatten = (node: Term): void => {
        const at = uncoerced(lang, node);

        if (at.kind === "app" && at.term === combiner.name) {
          for (const inner of at.args) {
            flatten(inner);
          }

          return;
        }

        leaves.push(render(lang, at, mode));
      };

      flatten(sole);

      // Glue only when every leaf is itself glueable — a single token the
      // parser would consume back. A compound element falls back to the
      // parenthesized form.
      const simple = leaves.every(
        (leaf) => !/\s/.test(leaf) && !groupers.some((g) => leaf.includes(g)),
      );

      if (simple) {
        return `${term.term}${leaves.join("")}`;
      }
    }
  }

  const args = term.args
    .map((arg) => `(${render(lang, arg, mode)})`)
    .join("");

  return `${term.term}${args}`;
}

/** The term with any coercion wrappers peeled off — what actually prints. */
function uncoerced(lang: SurfaceLanguage, term: Term): Term {
  let at = term;

  while (
    at.kind === "app" &&
    at.args.length === 1 &&
    lang.coercionNames.has(at.term)
  ) {
    const inner = at.args[0];

    if (inner === undefined) {
      break;
    }

    at = inner;
  }

  return at;
}

/** An argument position: parenthesize what would not survive re-parsing. */
function operand(
  lang: SurfaceLanguage,
  term: Term | undefined,
  mode: PrintMode,
): string {
  if (term === undefined) {
    return "";
  }

  const rendered = render(lang, term, mode);

  if (mode === "display") {
    // Connectives arrive self-parenthesized; everything else stands bare.
    return rendered;
  }

  // Engine mode: any unparenthesized compound gets parentheses, so every
  // operand is expression(max) and fits any slot.
  const bearer = uncoerced(lang, term);
  const bare =
    bearer.kind === "variable" ||
    (bearer.kind === "app" &&
      bearer.args.length === 0 &&
      lang.canonical.get(bearer.term) === undefined) ||
    rendered.startsWith("(");

  return bare ? rendered : `(${rendered})`;
}
