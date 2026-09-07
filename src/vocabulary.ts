/**
 * The surface vocabulary a spec declares: the tokens and the lexicon names
 * a chunk of input can be classified as.
 *
 * Derived, never annotated. The tokens are the constants of every notation
 * plus the grouping brackets. The names are every token in a sort's `@vars`
 * pool, and every declared term that has no notation of its own, binds
 * nothing, and is not a coercion — a term *with* a notation is spelled by
 * that notation; a term without one is spelled by its name, which is MM0's
 * own application rule read character-level.
 *
 * It lives apart from the scanner because the spec reader needs it too: a
 * declared delimiter that names nothing here is an authoring error, and a
 * lexicon name that the delimiters would split is unreachable.
 */

import type { Spec } from "./reader/spec.js";

export type NameRef =
  | { readonly kind: "term"; readonly term: string }
  | { readonly kind: "var"; readonly sort: string };

export interface Vocabulary {
  /** Lexicon names, and what each refers to. */
  readonly names: ReadonlyMap<string, NameRef>;
  /** Notation constants and grouping brackets. */
  readonly tokens: ReadonlySet<string>;
}

export function surfaceVocabulary(spec: Spec): Vocabulary {
  const tokens = new Set<string>();
  const notated = new Set<string>();

  for (const notation of spec.notations) {
    notated.add(notation.term);

    if (notation.form === "simple") {
      tokens.add(notation.token);
    } else {
      for (const literal of notation.literals) {
        if (literal.kind === "constant") {
          tokens.add(literal.token);
        }
      }
    }
  }

  for (const [open, close] of spec.groupingPairs) {
    tokens.add(open);
    tokens.add(close);
  }

  const names = new Map<string, NameRef>();

  for (const sort of spec.sorts.values()) {
    for (const token of sort.vars) {
      names.set(token, { kind: "var", sort: sort.name });
    }
  }

  // Every term is a lexicon name: MM0's `FUNC expression(max){n}` applies
  // any constructor by name, notation or no notation, bound binders or
  // none — `sb x t p` beside `[t / x] p`. A `@vars` token keeps the name.
  for (const term of spec.terms.values()) {
    if (!names.has(term.name)) {
      names.set(term.name, { kind: "term", term: term.name });
    }
  }

  return { names, tokens };
}

/**
 * The terms whose name is their *only* spelling: no notation, not a
 * coercion (inserted silently), no bound binder (a quantifier-shaped term
 * is written by its notation). These are the names the surface delimiters
 * must leave whole; any other term's name is a secondary spelling, MM0's
 * application syntax, and is reachable wherever the engine's own
 * delimiters apply even when a textbook's letter delimiters split it.
 */
export function nameOnlyTerms(spec: Spec): ReadonlySet<string> {
  const notated = new Set(spec.notations.map((notation) => notation.term));
  const coercions = new Set(spec.coercions.map((c) => c.name));

  return new Set(
    [...spec.terms.values()]
      .filter(
        (term) =>
          !notated.has(term.name) &&
          !coercions.has(term.name) &&
          !term.binders.some((binder) => binder.binds),
      )
      .map((term) => term.name),
  );
}
