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
 * Parentheses beyond the connectives' own are exactly the ones the parser
 * needs, decided from its own precedence tables: a piece stands bare in a
 * slot when its head binds at least as tight as the slot reads, and when
 * nothing on its right edge would swallow the operator after it — the
 * `(λx.x)·y` that bare would read the `y` into the body. So `1 + 0 * 0`
 * prints as such, and `(1 + 0) * 0` keeps its pair.
 *
 * The round-trip law — parsing a printed term, in the same mode, yields
 * the same tree — holds for every term, and is enforced by test over
 * generated terms in both modes. Its segmentation half is structural:
 * every seam between two printed pieces goes through {@link adjoin},
 * which sets them tight only where the reader's delimiters would cut
 * there anyway, and spaces them where it would not. "Tight" is the
 * display convention, not a promise — under a spec with no letter
 * delimiters `∀x Cube(x)` keeps its space, because `∀xCube(x)` would read
 * `xCube` as one chunk.
 */

import { adjoin, type DelimiterRules } from "./delimiters.js";
import { delaborate } from "./elab.js";
import { generalParts, precNum, type SurfaceLanguage } from "./parse.js";
import type { Term } from "./term.js";

export type PrintMode = "display" | "engine";

/**
 * A term display text cannot spell. The one such term is an `@syntax
 * elided` term standing anywhere but where the reader supplies it —
 * `R(snil,a)` — which has no surface spelling at all: written by name it
 * either fails to read (`snil` is four letters to Calgary) or, worse,
 * reads as something else (Magnus glues the letters into arguments). The
 * printer refuses rather than write text that does not read back as the
 * term. Engine text can always spell it, by name.
 */
export class UnprintableTermError extends Error {
  readonly term: string;

  constructor(term: string) {
    super(
      `${term} is elided wherever it is read, so display text has no way to write it here`,
    );
    this.name = "UnprintableTermError";
    this.term = term;
  }
}

/**
 * `term` as text in `mode`, which parses back in the same mode to the same
 * term. Display mode throws {@link UnprintableTermError} for the one shape
 * it cannot spell; engine mode is total.
 */
export function printTerm(
  lang: SurfaceLanguage,
  term: Term,
  mode: PrintMode = "display",
): string {
  const printer: Printer = {
    lang,
    mode,
    // Each mode is read back by its own scanner, so each is set against
    // that scanner's delimiters: the surface set for display, the
    // theory's own for engine text (where `(a)` is one chunk to a theory
    // that never declares `(`).
    rules: mode === "display" ? lang.scanner.rules : lang.engineScanner.rules,
  };
  if (mode === "engine") {
    return engine(printer, term);
  }

  const printed = display(printer, term, lang.spec.display.dropOuterParens);

  return lang.spec.elabRules.length > 0
    ? delaborate(lang, printed.text)
    : printed.text;
}

interface Printer {
  readonly lang: SurfaceLanguage;
  readonly mode: PrintMode;
  readonly rules: DelimiterRules;
}

/** Pieces set as tight as the reader's delimiters allow. */
function tight(printer: Printer, ...pieces: readonly string[]): string {
  return pieces.reduce((left, right) => adjoin(left, right, printer.rules));
}

/** Pieces set one space apart — always safe, and the connective style. */
function spaced(...pieces: readonly string[]): string {
  return pieces.filter((piece) => piece.length > 0).join(" ");
}

/** A piece in the built-in grouping pair. */
function grouped(printer: Printer, inner: string): string {
  return tight(printer, "(", inner, ")");
}

// ── engine text ──────────────────────────────────────────────────────

function engine(printer: Printer, term: Term): string {
  const { lang } = printer;

  if (term.kind === "variable") {
    return term.name;
  }

  // Coercions are the parser's bookkeeping; the engine re-derives them.
  const inner = coerced(lang, term);

  if (inner !== null) {
    return engine(printer, inner);
  }

  const notation = lang.canonical.get(term.term);

  // A term with no notation is written as application in full —
  // `P (snil)`, `R ((x , y))` — which the compiler reads at
  // expression(max).
  if (notation === undefined) {
    if (term.args.length === 0) {
      return term.term;
    }

    const binders = lang.spec.terms.get(term.term)?.binders ?? [];
    const args = term.args.map((arg, at) => {
      const rendered = engine(printer, arg);

      // A bound binder's argument is a variable and must stand bare: the
      // engine wants a name in that slot, not a group around one.
      if (binders[at]?.binds === true) {
        return rendered;
      }

      return rendered.startsWith("(") ? rendered : grouped(printer, rendered);
    });

    return spaced(term.term, ...args);
  }

  if (notation.form === "simple") {
    const args = term.args.map((arg) => engineOperand(printer, arg));

    return notation.fixity === "prefix"
      ? grouped(printer, spaced(notation.token, ...args))
      : grouped(
          printer,
          spaced(args[0] ?? "", notation.token, args[1] ?? ""),
        );
  }

  // General notation: constants and binder slots, in literal order.
  const pieces = notation.literals.map((literal) => {
    if (literal.kind === "constant") {
      return literal.token;
    }

    const index = notation.binders.findIndex(
      (binder) => binder.name === literal.name,
    );

    return engineOperand(printer, term.args[index]);
  });

  return term.args.length === 0
    ? spaced(...pieces)
    : grouped(printer, spaced(...pieces));
}

/**
 * An engine operand: any unparenthesized compound gets parentheses, so
 * every operand is expression(max) and fits any slot.
 */
function engineOperand(printer: Printer, term: Term | undefined): string {
  if (term === undefined) {
    return "";
  }

  const { lang } = printer;
  const rendered = engine(printer, term);
  const bearer = uncoerced(lang, term);
  const bare =
    bearer.kind === "variable" ||
    (bearer.kind === "app" &&
      bearer.args.length === 0 &&
      lang.canonical.get(bearer.term) === undefined) ||
    rendered.startsWith("(");

  return bare ? rendered : grouped(printer, rendered);
}

// ── display ──────────────────────────────────────────────────────────

const TIGHTEST = Number.POSITIVE_INFINITY;

/** mm0.md: bare constructor application is `expression(1024)`. */
const APPLICATION_PRECEDENCE = 1024;

/**
 * A piece of display text, with the two facts about it its context needs,
 * both in the parser's own precedence numbers.
 */
interface Printed {
  readonly text: string;
  /** It stands bare in a slot read at `min` exactly when `head >= min`. */
  readonly head: number;
  /**
   * The loosest slot still open at its right edge: an operator of
   * precedence `o` written straight after it is read *into* it when
   * `o >= tail`. Infinite when the right edge is closed — a bracket, a
   * name, a constant.
   */
  readonly tail: number;
}

function atom(text: string): Printed {
  return { text, head: TIGHTEST, tail: TIGHTEST };
}

/**
 * A piece set in a slot the parser reads at `min`, with an operator of
 * precedence `next` (or nothing) written after it: bare when it re-reads
 * as itself there, parenthesized when it would not.
 */
function fit(
  printer: Printer,
  piece: Printed,
  min: number,
  next: number | null,
): Printed {
  return piece.head >= min && (next === null || next < piece.tail)
    ? piece
    : atom(grouped(printer, piece.text));
}

/**
 * `outer` is true for the whole printed term under `@syntax display
 * drop-outer-parens`: the one pair a connective would wrap itself in is
 * left off. Coercions pass it through, since they print as what they wrap.
 */
function display(printer: Printer, term: Term, outer = false): Printed {
  const { lang } = printer;

  if (term.kind === "variable") {
    return atom(term.name);
  }

  // Coercions are the parser's bookkeeping; the reader re-derives them.
  const inner = coerced(lang, term);

  if (inner !== null) {
    return display(printer, inner, outer);
  }

  const notation = lang.canonical.get(term.term);

  if (notation === undefined) {
    return displayApplication(printer, term);
  }

  const binders = lang.spec.terms.get(term.term)?.binders ?? [];

  if (notation.form === "simple" && notation.fixity !== "prefix") {
    const prec = precNum(notation.prec);
    const leftMin = notation.fixity === "infixl" ? prec : prec + 1;
    const rightMin = notation.fixity === "infixl" ? prec + 1 : prec;
    const left = fitArg(printer, term.args[0], leftMin, prec);
    const right = fitArg(printer, term.args[1], rightMin, null);
    const tail = Math.min(rightMin, right.tail);

    // Connectives are spaced and self-parenthesized (the full-paren
    // convention), bar the outermost under drop-outer-parens.
    if (lang.isConnective(term.term)) {
      const text = spaced(left.text, notation.token, right.text);

      return outer
        ? { text, head: prec, tail }
        : atom(grouped(printer, text));
    }

    // A juxtaposed combiner displays as nothing when both sides are
    // single glue operands: `abc` for `mul(mul(a,b),c)`. The adjacency
    // arc is its operator written invisibly, at the same precedence, so
    // the slots above hold for it too; a compound side (`a*(bc)`) brings
    // the visible token back.
    const glued =
      lang.spec.terms.get(term.term)?.juxtaposed === true &&
      glueablePiece(lang, left.text) &&
      glueablePiece(lang, right.text);
    const text = glued
      ? tight(printer, left.text, right.text)
      : tight(printer, left.text, notation.token, right.text);

    return { text, head: prec, tail };
  }

  if (notation.form === "simple") {
    // mm0.md: a prefix notation's intermediate arguments read at max,
    // its last at the notation's own precedence.
    const prec = precNum(notation.prec);
    const pieces: string[] = [notation.token];
    let tail = TIGHTEST;

    term.args.forEach((arg, at) => {
      if (binders[at]?.binds === true) {
        pieces.push(display(printer, arg).text);
        tail = TIGHTEST;
        return;
      }

      const min = at === term.args.length - 1 ? prec : TIGHTEST;
      const piece = fit(printer, display(printer, arg), min, null);

      pieces.push(piece.text);
      tail = Math.min(min, piece.tail);
    });

    return { text: tight(printer, ...pieces), head: prec, tail };
  }

  const first = notation.literals[0];

  if (first?.kind !== "constant") {
    return displayApplication(printer, term);
  }

  // General notation: the head, then the parser's own slots in order.
  const pieces: string[] = [first.token];
  let tail = TIGHTEST;

  for (const part of generalParts(notation, first.prec)) {
    if (part.kind === "constant") {
      pieces.push(part.token);
      tail = TIGHTEST;
      continue;
    }

    const arg = term.args[part.slot.index];

    if (arg === undefined) {
      continue;
    }

    if (part.slot.binder.binds) {
      pieces.push(display(printer, arg).text);
      tail = TIGHTEST;
      continue;
    }

    const piece = fit(printer, display(printer, arg), part.slot.prec, null);

    pieces.push(piece.text);
    tail = Math.min(part.slot.prec, piece.tail);
  }

  return {
    text: tight(printer, ...pieces),
    head: precNum(first.prec),
    tail,
  };
}

function fitArg(
  printer: Printer,
  arg: Term | undefined,
  min: number,
  next: number | null,
): Printed {
  return arg === undefined
    ? { text: "", head: TIGHTEST, tail: TIGHTEST }
    : fit(printer, display(printer, arg), min, next);
}

/**
 * A term with no notation prints as application — the lexicon's shape.
 * Display elides an `@syntax elided` argument (bare `P`), flattens a
 * juxtaposed argument into glued leaves (`Rxy`), and otherwise sets each
 * argument in its own parentheses (`R(a,b)`, the comma coming from the
 * argument's own notation) — except a bound binder's variable, which the
 * reader takes bare (`sb x(t)(p)`), as MM0 application does.
 */
function displayApplication(
  printer: Printer,
  term: Term & { kind: "app" },
): Printed {
  const { lang } = printer;

  if (term.args.length === 0) {
    // Its one place is the sole argument of a name, which is elided
    // below before it ever gets here.
    if (lang.spec.terms.get(term.term)?.elided === true) {
      throw new UnprintableTermError(term.term);
    }

    return atom(term.term);
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
      return atom(term.term);
    }

    const combiner = lang.juxtaposedOf.get(sole.sort);

    if (combiner !== undefined) {
      // The parser folds glued leaves to the left, so only a left-nested
      // tree flattens back into itself: `Rxyz` is `R((x,y),z)`, and a
      // right operand that is itself a combination keeps its brackets.
      const leaves: string[] = [];
      const flatten = (node: Term): boolean => {
        const at = uncoerced(lang, node);

        if (at.kind !== "app" || at.term !== combiner.name) {
          leaves.push(display(printer, at).text);
          return true;
        }

        const [left, right] = at.args;
        const last = right === undefined ? undefined : uncoerced(lang, right);

        if (
          left === undefined ||
          last === undefined ||
          (last.kind === "app" && last.term === combiner.name) ||
          !flatten(left)
        ) {
          return false;
        }

        leaves.push(display(printer, last).text);
        return true;
      };

      // Glue only when every leaf is itself glueable — a single token the
      // parser would consume back. A compound element falls back to the
      // parenthesized form.
      if (
        flatten(sole) &&
        leaves.every((leaf) => glueablePiece(lang, leaf))
      ) {
        return atom(tight(printer, term.term, ...leaves));
      }
    }
  }

  const binders = lang.spec.terms.get(term.term)?.binders ?? [];
  const binds = term.args.some((_, at) => binders[at]?.binds === true);
  const pieces = term.args.map((arg, at) =>
    binders[at]?.binds === true
      ? display(printer, arg).text
      : grouped(printer, display(printer, arg).text),
  );

  // A name with a bound binder is read as bare application, which a
  // slot tighter than expression(1024) refuses.
  return {
    text: tight(printer, term.term, ...pieces),
    head: binds ? APPLICATION_PRECEDENCE : TIGHTEST,
    tail: TIGHTEST,
  };
}

/** The argument of a coercion node, or null when it is not one. */
function coerced(
  lang: SurfaceLanguage,
  term: Term & { kind: "app" },
): Term | null {
  return term.args.length === 1 && lang.coercionNames.has(term.term)
    ? (term.args[0] ?? null)
    : null;
}

/**
 * Whether a printed piece can stand as one glued element — one leaf of
 * `Rxy`, one factor of `abc`: no whitespace and no brackets, so it is a
 * single chunk the adjacency arc takes back whole. Where the seam falls
 * is {@link adjoin}'s business; this is only whether the piece is atomic.
 */
function glueablePiece(lang: SurfaceLanguage, piece: string): boolean {
  return (
    !/\s/.test(piece) &&
    !lang.spec.groupingPairs.flat().some((g) => piece.includes(g))
  );
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
