/**
 * Unfolding defs: a term with every `def` application replaced by its
 * definiens, the def's binders filled by the arguments.
 *
 * The engine sees through a def when it matches, so `a ≠ b` and `¬ a = b`
 * are one formula to it. A consumer that compares terms by their shape — a
 * rule's pattern against a row — has to see through it too, or it disagrees
 * with the engine about which rows a rule applies to. Display is the
 * consumer's business: unfold a copy to compare, and print what was read.
 */

import type { SurfaceLanguage } from "./parse.js";
import type { Binder } from "./reader/statements.js";
import type { Term } from "./term.js";
import { substitute, variables } from "./term.js";

/** Each language's def bodies, read once; null for one that does not read. */
const bodies = new WeakMap<SurfaceLanguage, Map<string, Term | null>>();

function sortOf(binder: Binder): string | null {
  return "sort" in binder.type ? binder.type.sort : null;
}

/**
 * A def's definiens, read as engine text over its binders and dummies;
 * null for a term, or a def whose definiens does not read or the proof
 * file supplies.
 */
export function definiens(lang: SurfaceLanguage, name: string): Term | null {
  let cache = bodies.get(lang);

  if (cache === undefined) {
    cache = new Map();
    bodies.set(lang, cache);
  }

  const cached = cache.get(name);

  if (cached !== undefined) {
    return cached;
  }

  const info = lang.spec.terms.get(name);
  const definition = info?.definition ?? null;
  let read: Term | null = null;

  if (info !== undefined && definition !== null) {
    const scope = new Map<string, string>();

    for (const binder of [...info.binders, ...definition.dummies]) {
      const sort = sortOf(binder);

      if (sort !== null) {
        scope.set(binder.name, sort);
      }
    }

    const parsed = lang.parse(definition.text, {
      lints: false,
      mode: "engine",
      scope,
      sort: info.returnSort,
    });

    read = parsed.ok ? parsed.term : null;
  }

  cache.set(name, read);
  return read;
}

/**
 * `term` with every def in it unfolded, innermost first, and the unfolded
 * definiens unfolded again, since a def may use an earlier one. A term with
 * no def in it comes back as the same object.
 *
 * A def's dot-dummies are bound inside its definiens; one whose name an
 * argument also uses is renamed from its sort's `@vars` pool, so that it
 * cannot capture the argument's variable. A def whose definiens does not
 * read, or the proof file supplies, is left folded.
 */
export function unfoldDefinitions(lang: SurfaceLanguage, term: Term): Term {
  if (term.kind === "variable") {
    return term;
  }

  const args = term.args.map((arg) => unfoldDefinitions(lang, arg));
  const unchanged = args.every((arg, at) => arg === term.args[at]);
  const info = lang.spec.terms.get(term.term);
  const body = info?.isDef === true ? definiens(lang, term.term) : null;

  if (info === undefined || body === null) {
    return unchanged ? term : { ...term, args };
  }

  const values = new Map<string, Term>();

  info.binders.forEach((binder, at) => {
    const arg = args[at];

    if (arg !== undefined) {
      values.set(binder.name, arg);
    }
  });

  const used = new Set(args.flatMap((arg) => [...variables(arg).keys()]));
  const taken = new Set([...used, ...variables(body).keys()]);

  for (const dummy of info.definition?.dummies ?? []) {
    const sort = sortOf(dummy);

    if (sort === null || !used.has(dummy.name)) {
      continue;
    }

    const fresh = lang.freshName(sort, taken);

    if (fresh?.kind === "variable") {
      taken.add(fresh.name);
      values.set(dummy.name, { ...fresh, span: body.span });
    }
  }

  return unfoldDefinitions(lang, substitute(body, values));
}
