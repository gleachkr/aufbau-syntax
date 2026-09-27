/**
 * Segmentation: where one chunk of input ends and the next begins.
 *
 * This is MM0's own tokenizer rule (`MathCursor.readToken` in Aufbau's
 * `src/trusted/parse.zig`) — skip whitespace; consume; break after a *left*
 * delimiter, and before whitespace or a *right* delimiter — generalized in
 * exactly one way: a delimiter is a string rather than a single byte, so
 * `∧`, `->` and `<->` can self-delimit where the engine's `[256]bool` table
 * cannot hold them.
 *
 * The point of keeping it here, apart from the vocabulary: **segmentation
 * never consults the term or notation tables.** A chunk's boundaries come
 * from the delimiter set alone; only afterwards is the chunk classified.
 * That is what MM0 buys by separating `delimiter` from `notation`, and it
 * is what makes declaring a new term unable to silently re-read an existing
 * string.
 *
 * The set is a *parameter*, never a global: engine text is read under the
 * theory's own `delimiter` statement, student input under the wider surface
 * set (see `Spec.surfaceDelimiters`).
 */

/** Delimiters as declared: a left list and a right list, as in MM0. */
export interface DelimiterSet {
  readonly left: ReadonlySet<string>;
  readonly right: ReadonlySet<string>;
}

/** A delimiter set prepared for matching: longest spelling wins. */
export interface DelimiterRules {
  /** Every delimiter, longest first — the units a chunk is built from. */
  readonly all: readonly string[];
  readonly left: ReadonlySet<string>;
  /** Right delimiters, longest first: a chunk breaks *before* one. */
  readonly right: readonly string[];
}

export function delimiterRules(set: DelimiterSet): DelimiterRules {
  const longestFirst = (entries: Iterable<string>): string[] =>
    [...new Set(entries)].sort((a, b) => b.length - a.length);

  return {
    all: longestFirst([...set.left, ...set.right]),
    left: new Set(set.left),
    right: longestFirst(set.right),
  };
}

function matchAt(
  candidates: readonly string[],
  text: string,
  at: number,
): string | null {
  for (const candidate of candidates) {
    if (candidate.length > 0 && text.startsWith(candidate, at)) {
      return candidate;
    }
  }

  return null;
}

/** One whole code point, so an astral character is never split in half. */
function codePointAt(text: string, at: number): string {
  const code = text.codePointAt(at);
  return code === undefined ? (text[at] ?? "") : String.fromCodePoint(code);
}

/**
 * The chunk starting at `start`, which must be a chunk boundary (the start
 * of the text, or the end of the previous chunk). Leading whitespace is not
 * skipped — `segment` does that.
 */
export function chunkAt(
  text: string,
  start: number,
  rules: DelimiterRules,
): string {
  let position = start;

  while (position < text.length) {
    // Always consume something: a delimiter that starts here, else one
    // character. MM0 consumes before it tests, which is what lets a
    // delimiter both open a chunk and close it.
    const unit =
      matchAt(rules.all, text, position) ?? codePointAt(text, position);
    position += unit.length;

    if (rules.left.has(unit)) {
      break;
    }

    if (position >= text.length || /\s/.test(text[position] ?? "")) {
      break;
    }

    if (matchAt(rules.right, text, position) !== null) {
      break;
    }
  }

  return text.slice(start, position);
}

/** Every chunk of `text`, in order, with whitespace dropped. */
export function segment(text: string, rules: DelimiterRules): string[] {
  const chunks: string[] = [];
  let position = 0;

  while (position < text.length) {
    if (/\s/.test(text[position] ?? "")) {
      position += 1;
      continue;
    }

    const chunk = chunkAt(text, position, rules);

    // A zero-length chunk would spin; the rule cannot produce one, but the
    // loop should not depend on that.
    if (chunk.length === 0) {
      break;
    }

    chunks.push(chunk);
    position += chunk.length;
  }

  return chunks;
}

/**
 * Whether `name` can ever be read as a single chunk — i.e. whether a student
 * writing it, with space around it, gets it whole. A name that splits is
 * unreachable: no amount of bracketing recovers it, because segmentation
 * happens before anything knows the name exists.
 */
export function isReachableChunk(
  name: string,
  rules: DelimiterRules,
): boolean {
  return name.length > 0 && chunkAt(name, 0, rules) === name;
}

/**
 * `left` then `right`, written so the text segments into exactly `left`'s
 * chunks followed by `right`'s: tight where the delimiters already cut at
 * the seam, and with one space where they would not. Under letter
 * delimiters `∀` and `x` and `Cube(x)` set tight as `∀xCube(x)`; without
 * them that is one chunk `xCube`, and the seam gets its space —
 * `∀x Cube(x)`.
 *
 * This is what makes printing total: a space always separates, since no
 * delimiter contains whitespace, so whatever the two pieces are, the
 * result reads back as both of them.
 */
export function adjoin(
  left: string,
  right: string,
  rules: DelimiterRules,
): string {
  if (
    left.length === 0 ||
    right.length === 0 ||
    /\s$/.test(left) ||
    /^\s/.test(right)
  ) {
    return left + right;
  }

  const tight = left + right;
  const apart = [...segment(left, rules), ...segment(right, rules)];
  const together = segment(tight, rules);
  const same =
    together.length === apart.length &&
    together.every((chunk, index) => chunk === apart[index]);

  return same ? tight : `${left} ${right}`;
}
