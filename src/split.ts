/**
 * Splitting a list of the language's text at a separator, the way its
 * brackets group it.
 */

import type { SurfaceLanguage } from "./parse.js";

/**
 * Split text at each `separator` outside every grouping pair the language
 * declares (`( )` always, and any `@syntax brackets` adds) — the reading a
 * comma-separated list of the language's formulas needs, since the same
 * comma may separate a predicate's arguments: `R(a, b), F(c)` is two
 * pieces, not three. The pieces come back untrimmed, empty ones included,
 * so `pieces.join(separator)` is the text again.
 *
 * Plain text, not segmented: the separator need not be any token of the
 * language. A close with no open is not counted, so it cannot hide a later
 * separator.
 */
export function splitTopLevel(
  language: SurfaceLanguage,
  text: string,
  separator: string,
): readonly string[] {
  if (separator.length === 0) {
    return [text];
  }

  const pairs = language.spec.groupingPairs;
  const pieces: string[] = [];
  let depth = 0;
  let start = 0;
  let index = 0;

  while (index < text.length) {
    const open = pairs.find(([token]) => text.startsWith(token, index));
    const close =
      open === undefined
        ? pairs.find(([, token]) => text.startsWith(token, index))
        : undefined;

    if (open !== undefined) {
      depth += 1;
      index += open[0].length;
    } else if (close !== undefined) {
      depth = Math.max(0, depth - 1);
      index += close[1].length;
    } else if (depth === 0 && text.startsWith(separator, index)) {
      pieces.push(text.slice(start, index));
      index += separator.length;
      start = index;
    } else {
      index += 1;
    }
  }

  pieces.push(text.slice(start));

  return pieces;
}
