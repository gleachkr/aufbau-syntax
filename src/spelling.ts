/**
 * Spellings both ways: the tokens a constructor is written with, and what
 * a token a person writes can mean.
 *
 * A consumer naming a symbol the way a reader of the language would — an
 * author restricting a sentence to `∧` and `¬`, an interface showing a
 * turnstile — wants the language's own lexicon, not a table of its own.
 */

import type { SurfaceLanguage } from "./parse.js";
import type { NotationInfo } from "./reader/spec.js";

/**
 * The token a notation is known by: a simple notation's own, or the first
 * constant of a general one (`∀` of `∀ x φ`). Null for a general notation
 * with no constant, which MM0 does not allow.
 */
export function notationToken(notation: NotationInfo): string | null {
  if (notation.form === "simple") {
    return notation.token;
  }

  for (const literal of notation.literals) {
    if (literal.kind === "constant") {
      return literal.token;
    }
  }

  return null;
}

/**
 * The tokens `term` is written with: its canonical notation's first, then
 * each other notation's in declaration order, each once. Empty for a term
 * that has no notation and is spelled by its name. An elab rule's input
 * spelling (`E` written for `∃`) is input only and is not among them.
 */
export function spellingsOf(
  language: SurfaceLanguage,
  term: string,
): readonly string[] {
  const spellings: string[] = [];
  const canonical = language.canonical.get(term);
  const first = canonical === undefined ? null : notationToken(canonical);

  if (first !== null) {
    spellings.push(first);
  }

  for (const notation of language.spec.notations) {
    const token = notation.term === term ? notationToken(notation) : null;

    if (token !== null && !spellings.includes(token)) {
      spellings.push(token);
    }
  }

  return spellings;
}

/** Everything one spelling can stand for in a language. */
export interface SpellingMeanings {
  /**
   * The terms it writes: the term of that name, each term a notation
   * known by it writes, and each term written by a notation token an elab
   * rule's template puts where the spelling stood. In declaration order.
   */
  readonly terms: readonly string[];
  /** The sorts whose `@vars` pool holds it. */
  readonly varSorts: readonly string[];
}

/**
 * What `spelling` can mean, as a person writing the language uses it.
 * Usually one thing, but not always: Calgary's `E` is a predicate letter
 * and, through an elab rule, an ASCII `∃`, told apart only by where it is
 * written, so it means both. Both lists are empty for a spelling the
 * language does not have.
 */
export function spellingMeanings(
  language: SurfaceLanguage,
  spelling: string,
): SpellingMeanings {
  const { spec } = language;
  const terms = new Set<string>();

  if (spec.terms.has(spelling)) {
    terms.add(spelling);
  }

  const tokens = new Set([spelling]);

  for (const rule of spec.elabRules) {
    if (
      rule.pattern.some(
        (element) => element.kind === "literal" && element.token === spelling,
      )
    ) {
      for (const element of rule.template) {
        if (element.kind === "literal") {
          tokens.add(element.token);
        }
      }
    }
  }

  for (const notation of spec.notations) {
    const token = notationToken(notation);

    if (token !== null && tokens.has(token)) {
      terms.add(notation.term);
    }
  }

  const varSorts = [...spec.sorts.values()]
    .filter((sort) => sort.vars.includes(spelling))
    .map((sort) => sort.name);

  return { terms: [...terms], varSorts };
}
