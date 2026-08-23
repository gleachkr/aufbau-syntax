/**
 * Helpers for handing work to the Aufbau engine.
 *
 * The engine rejects annotations it does not know, so a spec file goes to
 * it with the `@syntax` lines stripped — the library owns that boundary.
 * Everything else in the spec is already the engine's language: the
 * lexicon is ordinary term declarations, and variables are `@vars` pools,
 * which the engine understands natively. `boundVariableBinders` writes
 * the `{x: var}` binder list a theorem statement needs for the variables
 * (bound or free — Calgary's names included) a formula mentions.
 */

import type { Term } from "./term.js";
import { walkTerm } from "./term.js";

/** The spec source with every `@syntax` annotation line removed. */
export function stripSyntaxAnnotations(source: string): string {
  return source
    .split("\n")
    .filter((line) => !line.trim().startsWith("--| @syntax"))
    .join("\n");
}

/**
 * The variable binder list for a theorem statement over these terms,
 * e.g. `{x y: var} {a: name}` — one group per sort, empty string when
 * there are no variables.
 */
export function boundVariableBinders(terms: readonly Term[]): string {
  const bySort = new Map<string, Set<string>>();

  for (const term of terms) {
    walkTerm(term, (node) => {
      if (node.kind === "variable") {
        const names = bySort.get(node.sort) ?? new Set();
        names.add(node.name);
        bySort.set(node.sort, names);
      }
    });
  }

  return [...bySort.entries()]
    .map(([sort, names]) => `{${[...names].join(" ")}: ${sort}}`)
    .join(" ");
}
