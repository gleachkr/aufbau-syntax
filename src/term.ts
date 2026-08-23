/**
 * The term tree a surface parse produces: constructor applications over the
 * spec's signature, with variables as leaves. No hardcoded connective set —
 * what a node *means* is the consumer's business, via `@syntax role`.
 */

import type { Span } from "./diagnostics";

export type Fixity = "general" | "infixl" | "infixr" | "prefix";

export type Term = AppTerm | VariableTerm;

export interface AppTerm {
  readonly kind: "app";
  /** The constructor: a declared term, def, or coercion name. */
  readonly term: string;
  readonly args: readonly Term[];
  readonly sort: string;
  readonly span: Span;
  /** True when the source wrapped this node in its own bracket pair. */
  readonly grouped: boolean;
  /** How the node was written, for printing and for the tree lints. */
  readonly fixity: Fixity | null;
  readonly prec: number | "max" | null;
  /**
   * The notation token as the source spelled it (`->`, not the canonical
   * `→`), so diagnostics can quote what the writer typed. Null when the
   * node was not written through a token: letters and coercions.
   */
  readonly token: string | null;
}

export interface VariableTerm {
  readonly kind: "variable";
  /** The token as written — one of its sort's `@vars` pool. */
  readonly name: string;
  readonly sort: string;
  readonly span: Span;
  readonly grouped: boolean;
  /**
   * True when this occurrence fills a *binding* slot of its parent — the x
   * of `∀x`, which scopes over the arguments after it. Set by the parser
   * from the constructor's binder; the tree shape alone cannot tell `∀x …`
   * from `x = y`.
   */
  readonly binder: boolean;
}

/**
 * Depth-first walk, parents before children. `bound` holds the variable
 * names in scope at each node; a binding occurrence extends it for the
 * arguments that follow it.
 */
export function walkTerm(
  term: Term,
  visit: (node: Term, bound: ReadonlySet<string>) => void,
  bound: ReadonlySet<string> = new Set(),
): void {
  visit(term, bound);

  if (term.kind !== "app") {
    return;
  }

  let scope = bound;

  for (const arg of term.args) {
    if (arg.kind === "variable" && arg.binder) {
      visit(arg, scope);
      const next = new Set(scope);
      next.add(arg.name);
      scope = next;
      continue;
    }

    walkTerm(arg, visit, scope);
  }
}
