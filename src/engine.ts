/**
 * Helpers for handing work to the Aufbau engine.
 *
 * The engine rejects annotations it does not know, so a spec file goes to
 * it with the `@syntax` lines stripped — the library owns that boundary.
 * And because letter families are schemas (the spec declares `_pred`, a
 * student writes `F_12`), whatever a term actually used must be declared
 * before the engine can parse text mentioning it: `elaboratedDeclarations`
 * writes those `term` statements, and `boundVariableBinders` the `{x: var}`
 * binder list a theorem statement needs.
 */

import type { SurfaceLanguage } from "./parse";
import type { Term } from "./term";
import { walkTerm } from "./term";

/** The spec source with every `@syntax` annotation line removed. */
export function stripSyntaxAnnotations(source: string): string {
  return source
    .split("\n")
    .filter((line) => !line.trim().startsWith("--| @syntax"))
    .join("\n");
}

/**
 * One `term` declaration per elaborated letter the terms use, shaped like
 * the letter's template: `term F_12 (s: seq): wff;`.
 */
export function elaboratedDeclarations(
  lang: SurfaceLanguage,
  terms: readonly Term[],
): string {
  const declarations = new Map<string, string>();

  for (const term of terms) {
    walkTerm(term, (node) => {
      if (node.kind !== "app" || node.family === null) {
        return;
      }

      const info = lang.familyInfo.get(node.family);

      if (info === undefined || declarations.has(node.term)) {
        return;
      }

      const binders = info.argBinders
        .map((binder) =>
          "sort" in binder.type
            ? ` (${binder.name}: ${binder.type.sort})`
            : "",
        )
        .join("");

      declarations.set(
        node.term,
        `term ${node.term}${binders}: ${info.sort};`,
      );
    });
  }

  return [...declarations.values()].join("\n");
}

/**
 * The bound-variable binder list for a theorem statement over these terms,
 * e.g. `{x y: var}` — one group per sort, empty string when there are no
 * variables.
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
