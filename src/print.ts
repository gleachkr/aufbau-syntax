/**
 * The printer: a term tree back to text, in one of two modes.
 *
 * **Display** is what a reader sees, in the textbook's own conventions:
 * the canonical spelling of each constructor (the last-declared notation,
 * Aufbau's rule), *full* parenthesization of sentential connectives with
 * the outermost pair optionally dropped (`@syntax display
 * drop-outer-parens`) — Carnap's convention, not minimal-parens. A formula
 * is outermost wherever the sort changes above it, not only at the top:
 * `𝕋 A ∧ B`, `A ∧ B ⊢ C`. Connectives are spaced, and so is a notation
 * that takes its operands to another sort (`a = b`, `𝕋 A`); everything
 * else is set tight (`¬P`, `∀x`, `R(a,b)`). A notation token declared a
 * delimiter on one side only hugs that side and stands off the other, so
 * a right-only `,` writes `a, b`.
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
import { delaborate, delaborateTracked, type Elaborated } from "./elab.js";
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

  const printed = displayed(lang, term);

  return lang.spec.elabRules.length > 0
    ? delaborate(lang, printed.text)
    : printed.text;
}

interface Printer {
  readonly lang: SurfaceLanguage;
  readonly mode: PrintMode;
  readonly rules: DelimiterRules;
}

/** Engine pieces set as tight as the reader's delimiters allow. */
function tight(printer: Printer, ...pieces: readonly string[]): string {
  return pieces.reduce((left, right) => adjoin(left, right, printer.rules));
}

/** Pieces set one space apart — always safe, and the connective style. */
function spaced(...pieces: readonly string[]): string {
  return pieces.filter((piece) => piece.length > 0).join(" ");
}

/** One piece of a display notation: an operand's text, or its own token. */
interface Piece {
  readonly laid: Laid;
  readonly token: boolean;
}

function operand(laid: Laid): Piece {
  return { laid, token: false };
}

function token(text: string, path: readonly number[]): Piece {
  return { laid: laid(text, path, "token"), token: true };
}

/**
 * A display notation's pieces in order, its seams spaced when `apart` and
 * otherwise as tight as the delimiters allow. A token the surface
 * delimiters list on one side only decides its own seams instead: a
 * right-only token breaks before itself, so it hugs what precedes it and
 * stands off what follows (`a, b`); a left-only one is the mirror. That is
 * the declaration read as layout, and it holds in a spec whose letters are
 * delimiters too, where `a,b` would read back just as well. `path` is the
 * notation's node, whose the spaces are.
 */
function setPieces(
  printer: Printer,
  pieces: readonly Piece[],
  apart: boolean,
  path: readonly number[],
): Laid {
  let text = NOTHING;
  let previous: Piece | null = null;

  for (const piece of pieces) {
    if (piece.laid.text.length === 0) {
      continue;
    }

    if (previous === null) {
      text = piece.laid;
      previous = piece;
      continue;
    }

    const after = previous.token
      ? oneSide(printer, previous.laid.text)
      : null;
    const before = piece.token ? oneSide(printer, piece.laid.text) : null;
    const space =
      after === "right" || before === "left"
        ? true
        : after === "left" || before === "right"
          ? false
          : apart;

    // A space never joins two chunks, so only the tight seam needs adjoin.
    text = space
      ? joined(text, laid(" ", path, "space"), piece.laid)
      : adjoined(printer, path, text, piece.laid);
    previous = piece;
  }

  return text;
}

/** The one side `text` is a delimiter on, or null for both or neither. */
function oneSide(printer: Printer, text: string): "left" | "right" | null {
  const left = printer.rules.left.has(text);
  const right = printer.rules.right.includes(text);

  return left === right ? null : left ? "left" : "right";
}

/** An engine piece in the built-in grouping pair. */
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

/**
 * What a piece of display text is: a notation's own token (`∧`, `¬`,
 * `∀`, `⊤`), a grouping bracket, a name — a variable, a constant, the head
 * of an application — or a space between two pieces.
 */
export type PieceKind = "token" | "bracket" | "name" | "space";

/** One piece of display text, and the node of the term it came from. */
export interface PrintedPiece {
  readonly text: string;
  /**
   * The argument indices from the printed term down to the node: `[]` is
   * the term itself, `[1, 0]` its second argument's first. Coercion nodes
   * count, since they are in the tree.
   */
  readonly path: readonly number[];
  readonly kind: PieceKind;
}

/**
 * `term`'s display text as pieces, each attributed to the node it came
 * from: what lets a reader of the text put something under one subterm —
 * a truth table's cell under each atom and connective, a highlight over
 * one subformula. The pieces' texts joined are exactly `printTerm(lang,
 * term)`.
 *
 * A notation's tokens belong to the node the notation writes; a
 * connective's own pair, and the pair a subterm needs to read back in its
 * slot, to the node they enclose; an application's argument brackets to
 * the application; a space to the node whose layout set it. A spec's
 * `@syntax elab` rules then rewrite the text, and each rewritten
 * character keeps the node of the character it came from. Throws
 * {@link UnprintableTermError} as display text does.
 */
export function printPieces(
  lang: SurfaceLanguage,
  term: Term,
): readonly PrintedPiece[] {
  const printed = displayed(lang, term);

  return lang.spec.elabRules.length > 0
    ? reattributed(printed.run, delaborateTracked(lang, printed.text))
    : printed.run;
}

function displayed(lang: SurfaceLanguage, term: Term): Printed {
  const printer: Printer = {
    lang,
    mode: "display",
    rules: lang.scanner.rules,
  };

  return display(printer, term, lang.spec.display.dropOuterParens, []);
}

/**
 * The pieces again over the delaborated text: each run of characters
 * from one piece is a piece, and whitespace is a space wherever it came
 * from.
 */
function reattributed(
  run: readonly PrintedPiece[],
  delaborated: Elaborated,
): PrintedPiece[] {
  const owner: number[] = [];

  run.forEach((piece, index) => {
    for (let at = 0; at < piece.text.length; at += 1) {
      owner.push(index);
    }
  });

  const out: { text: string; from: number; space: boolean }[] = [];
  const { text, origin } = delaborated;

  for (let at = 0; at < text.length; at += 1) {
    const char = text[at] ?? "";
    const from = owner[origin[at] ?? 0] ?? Math.max(0, run.length - 1);
    const space = /\s/.test(char);
    const last = out[out.length - 1];
    // A surrogate pair is one character, and stays in one piece.
    const low = /[\uDC00-\uDFFF]/.test(char);

    if (
      last !== undefined &&
      (low || (last.from === from && last.space === space))
    ) {
      last.text += char;
      continue;
    }

    out.push({ text: char, from, space });
  }

  return out.flatMap(({ text: piece, from, space }) => {
    const source = run[from];

    return source === undefined
      ? []
      : [
          {
            text: piece,
            path: source.path,
            kind: space ? "space" : source.kind,
          },
        ];
  });
}

/** Display text, and the same text as attributed pieces. */
interface Laid {
  readonly text: string;
  readonly run: readonly PrintedPiece[];
}

const NOTHING: Laid = { text: "", run: [] };

function laid(text: string, path: readonly number[], kind: PieceKind): Laid {
  return text.length === 0 ? NOTHING : { text, run: [{ text, path, kind }] };
}

function joined(...parts: readonly Laid[]): Laid {
  return {
    text: parts.map((part) => part.text).join(""),
    run: parts.flatMap((part) => part.run),
  };
}

/**
 * `left` then `right` as {@link adjoin} sets them, the space it adds, if
 * any, set by the node at `path`.
 */
function adjoined(
  printer: Printer,
  path: readonly number[],
  left: Laid,
  right: Laid,
): Laid {
  const text = adjoin(left.text, right.text, printer.rules);

  return text.length === left.text.length + right.text.length
    ? joined(left, right)
    : joined(left, laid(" ", path, "space"), right);
}

/** Display pieces set as tight as the reader's delimiters allow. */
function setTight(
  printer: Printer,
  path: readonly number[],
  ...parts: readonly Laid[]
): Laid {
  return parts.reduce((left, right) => adjoined(printer, path, left, right));
}

/** Display text in the built-in grouping pair, the node at `path`'s. */
function bracketed(
  printer: Printer,
  path: readonly number[],
  inner: Laid,
): Laid {
  return setTight(
    printer,
    path,
    laid("(", path, "bracket"),
    inner,
    laid(")", path, "bracket"),
  );
}

const TIGHTEST = Number.POSITIVE_INFINITY;

/** mm0.md: bare constructor application is `expression(1024)`. */
const APPLICATION_PRECEDENCE = 1024;

/**
 * A piece of display text, with the two facts about it its context needs,
 * both in the parser's own precedence numbers.
 */
interface Printed extends Laid {
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

function atom(text: Laid): Printed {
  return { ...text, head: TIGHTEST, tail: TIGHTEST };
}

/**
 * A piece set in a slot the parser reads at `min`, with an operator of
 * precedence `next` (or nothing) written after it: bare when it re-reads
 * as itself there, parenthesized when it would not. `path` is the piece's
 * own node, whose the pair is.
 */
function fit(
  printer: Printer,
  piece: Printed,
  min: number,
  next: number | null,
  path: readonly number[],
): Printed {
  return piece.head >= min && (next === null || next < piece.tail)
    ? piece
    : atom(bracketed(printer, path, piece));
}

/**
 * `outer` is true, under `@syntax display drop-outer-parens`, for the whole
 * printed term and for a term the sort changes above ({@link outermost}):
 * the one pair a connective would wrap itself in is left off. Coercions
 * pass it through, since they print as what they wrap. `path` is where
 * `term` sits in the term being printed.
 */
function display(
  printer: Printer,
  term: Term,
  outer: boolean,
  path: readonly number[],
): Printed {
  const { lang } = printer;

  if (term.kind === "variable") {
    return atom(laid(term.name, path, "name"));
  }

  // Coercions are the parser's bookkeeping; the reader re-derives them.
  const inner = coerced(lang, term);

  if (inner !== null) {
    return display(printer, inner, outer, [...path, 0]);
  }

  const notation = lang.canonical.get(term.term);

  if (notation === undefined) {
    return displayApplication(printer, term, path);
  }

  const binders = lang.spec.terms.get(term.term)?.binders ?? [];
  const at = (index: number): readonly number[] => [...path, index];

  if (notation.form === "simple" && notation.fixity !== "prefix") {
    const prec = precNum(notation.prec);
    const leftMin = notation.fixity === "infixl" ? prec : prec + 1;
    const rightMin = notation.fixity === "infixl" ? prec + 1 : prec;
    const connective = lang.isConnective(term.term);
    // A connective's operands are compounds of its own sort, which keep
    // their brackets under it: that is the full-paren convention.
    const outerAt = (index: number): boolean =>
      !connective && outermost(printer, term, term.args[index]);
    const left = fitArg(
      printer,
      term.args[0],
      leftMin,
      prec,
      outerAt(0),
      at(0),
    );
    const right = fitArg(
      printer,
      term.args[1],
      rightMin,
      null,
      outerAt(1),
      at(1),
    );
    const tail = Math.min(rightMin, right.tail);
    const pieces = [
      operand(left),
      token(notation.token, path),
      operand(right),
    ];

    // Connectives are spaced and self-parenthesized (the full-paren
    // convention), bar the outermost under drop-outer-parens.
    if (connective) {
      const text = setPieces(printer, pieces, true, path);

      return outer
        ? { ...text, head: prec, tail }
        : atom(bracketed(printer, path, text));
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
      ? setTight(printer, path, left, right)
      : setPieces(printer, pieces, changesSort(lang, term.term), path);

    return { ...text, head: prec, tail };
  }

  if (notation.form === "simple") {
    // mm0.md: a prefix notation's intermediate arguments read at max,
    // its last at the notation's own precedence.
    const prec = precNum(notation.prec);
    const pieces: Piece[] = [token(notation.token, path)];
    let tail = TIGHTEST;

    term.args.forEach((arg, index) => {
      if (binders[index]?.binds === true) {
        pieces.push(operand(display(printer, arg, false, at(index))));
        tail = TIGHTEST;
        return;
      }

      const min = index === term.args.length - 1 ? prec : TIGHTEST;
      const piece = fit(
        printer,
        display(printer, arg, outermost(printer, term, arg), at(index)),
        min,
        null,
        at(index),
      );

      pieces.push(operand(piece));
      tail = Math.min(min, piece.tail);
    });

    return {
      ...setPieces(printer, pieces, changesSort(lang, term.term), path),
      head: prec,
      tail,
    };
  }

  const first = notation.literals[0];

  if (first?.kind !== "constant") {
    return displayApplication(printer, term, path);
  }

  // General notation: the head, then the parser's own slots in order.
  const pieces: Piece[] = [token(first.token, path)];
  let tail = TIGHTEST;

  for (const part of generalParts(notation, first.prec)) {
    if (part.kind === "constant") {
      pieces.push(token(part.token, path));
      tail = TIGHTEST;
      continue;
    }

    const index = part.slot.index;
    const arg = term.args[index];

    if (arg === undefined) {
      continue;
    }

    if (part.slot.binder.binds) {
      pieces.push(operand(display(printer, arg, false, at(index))));
      tail = TIGHTEST;
      continue;
    }

    const piece = fit(
      printer,
      display(printer, arg, outermost(printer, term, arg), at(index)),
      part.slot.prec,
      null,
      at(index),
    );

    pieces.push(operand(piece));
    tail = Math.min(part.slot.prec, piece.tail);
  }

  return {
    ...setPieces(printer, pieces, changesSort(lang, term.term), path),
    head: precNum(first.prec),
    tail,
  };
}

function fitArg(
  printer: Printer,
  arg: Term | undefined,
  min: number,
  next: number | null,
  outer: boolean,
  path: readonly number[],
): Printed {
  return arg === undefined
    ? { ...NOTHING, head: TIGHTEST, tail: TIGHTEST }
    : fit(printer, display(printer, arg, outer, path), min, next, path);
}

/**
 * Whether `arg`, under `parent`, is the outermost formula of its sort:
 * under drop-outer-parens a connective leaves off its own pair wherever
 * the sort changes above it, as it does at the top — `𝕋 A ∧ B`, `A ∧ B ⊢
 * C`. Read through coercions, which change sort without printing. Safe
 * for the same reason the top is: {@link fit} still brackets a compound
 * that would not read back bare in its slot.
 */
function outermost(
  printer: Printer,
  parent: Term & { kind: "app" },
  arg: Term | undefined,
): boolean {
  return (
    arg !== undefined &&
    printer.lang.spec.display.dropOuterParens &&
    uncoerced(printer.lang, arg).sort !== parent.sort
  );
}

/**
 * Whether `name` takes its operands to another sort, returning none of
 * theirs: `=` from terms to a formula, `𝕋` from a formula to a row, `⊢`
 * from a context and a formula to a judgement. Its display is spaced, as
 * a connective's is; `¬`, `∀x` and `,` stay tight.
 */
function changesSort(lang: SurfaceLanguage, name: string): boolean {
  const info = lang.spec.terms.get(name);

  if (info === undefined) {
    return false;
  }

  const sorts = info.binders
    .filter((binder) => !binder.binds)
    .map((binder) => ("sort" in binder.type ? binder.type.sort : ""));

  return sorts.length > 0 && !sorts.includes(info.returnSort);
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
  path: readonly number[],
): Printed {
  const { lang } = printer;
  const head = laid(term.term, path, "name");

  if (term.args.length === 0) {
    // Its one place is the sole argument of a name, which is elided
    // below before it ever gets here.
    if (lang.spec.terms.get(term.term)?.elided === true) {
      throw new UnprintableTermError(term.term);
    }

    return atom(head);
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
      return atom(head);
    }

    const combiner = lang.juxtaposedOf.get(sole.sort);

    if (combiner !== undefined) {
      // The parser folds glued leaves to the left, so only a left-nested
      // tree flattens back into itself: `Rxyz` is `R((x,y),z)`, and a
      // right operand that is itself a combination keeps its brackets.
      const leaves: Laid[] = [];
      const flatten = (node: Term, from: readonly number[]): boolean => {
        const [at, atPath] = peeled(lang, node, from);

        if (at.kind !== "app" || at.term !== combiner.name) {
          leaves.push(display(printer, at, false, atPath));
          return true;
        }

        const [left, right] = at.args;
        const [last, lastPath] =
          right === undefined
            ? [undefined, atPath]
            : peeled(lang, right, [...atPath, 1]);

        if (
          left === undefined ||
          last === undefined ||
          (last.kind === "app" && last.term === combiner.name) ||
          !flatten(left, [...atPath, 0])
        ) {
          return false;
        }

        leaves.push(display(printer, last, false, lastPath));
        return true;
      };

      // Glue only when every leaf is itself glueable — a single token the
      // parser would consume back. A compound element falls back to the
      // parenthesized form.
      if (
        flatten(sole, [...path, 0]) &&
        leaves.every((leaf) => glueablePiece(lang, leaf.text))
      ) {
        return atom(setTight(printer, path, head, ...leaves));
      }
    }
  }

  const binders = lang.spec.terms.get(term.term)?.binders ?? [];
  const binds = term.args.some((_, at) => binders[at]?.binds === true);
  const pieces = term.args.map((arg, at) =>
    binders[at]?.binds === true
      ? display(printer, arg, false, [...path, at])
      : bracketed(
          printer,
          path,
          display(printer, arg, outermost(printer, term, arg), [...path, at]),
        ),
  );

  // A name with a bound binder is read as bare application, which a
  // slot tighter than expression(1024) refuses.
  return {
    ...setTight(printer, path, head, ...pieces),
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
  return peeled(lang, term, [])[0];
}

/** {@link uncoerced}, with the path it ends at from `path`. */
function peeled(
  lang: SurfaceLanguage,
  term: Term,
  path: readonly number[],
): readonly [Term, readonly number[]] {
  let at = term;
  let atPath = path;

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
    atPath = [...atPath, 0];
  }

  return [at, atPath];
}
