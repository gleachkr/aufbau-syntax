/**
 * The term tree a surface parse produces: constructor applications over the
 * spec's signature, with variables as leaves. No hardcoded connective set —
 * what a node *means* is the consumer's business, via `@syntax role`.
 */

import type { Span } from "./diagnostics.js";

export type Fixity = "general" | "infixl" | "infixr" | "prefix";

export type Term = AppTerm | VariableTerm;

export interface AppTerm {
  readonly kind: "app";
  /** The constructor: a declared term, def, or coercion name. */
  readonly term: string;
  readonly args: readonly Term[];
  /**
   * The arguments that bind a variable, and where: the constructor's
   * `TermInfo.bindings`, so a walk can scope a binding without the spec.
   * Empty for a constructor that binds nothing, and for a coercion.
   */
  readonly bindings: readonly Binding[];
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

/**
 * A bound binder that binds: its index among the constructor's arguments,
 * and the indices of the arguments it binds in, in order. mm0.md reads a
 * binding by dependency, not position: `{x}` binds in the arguments whose
 * types depend on x, and not at all when the return sort does.
 */
export interface Binding {
  readonly binder: number;
  readonly scope: readonly number[];
}

/** Whether the argument `at` of a constructor with these `bindings` binds. */
export function bindsAt(bindings: readonly Binding[], at: number): boolean {
  return bindings.some((binding) => binding.binder === at);
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
   * of `∀x`, which scopes over the arguments its parent's `bindings` name.
   * Set by the parser from the constructor's binder; the tree shape alone
   * cannot tell `∀x …` from `x = y`. A bound binder that binds nothing (its
   * return sort depends on it) holds a free occurrence, and this is false.
   */
  readonly binder: boolean;
}

/**
 * Depth-first walk, parents before children. `bound` holds the variable
 * names in scope at each node; a binding occurrence is visited in its
 * parent's scope and extends it for the arguments it binds in.
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

  term.args.forEach((arg, at) => {
    walkTerm(arg, visit, scopeOf(term, at, bound));
  });
}

/**
 * The names in scope at `term`'s argument `at`: `bound`, and each variable
 * its parent's bindings bind there. A binding occurrence is not in its own
 * scope.
 */
export function scopeOf(
  term: AppTerm,
  at: number,
  bound: ReadonlySet<string>,
): ReadonlySet<string> {
  const names = bindersOver(term, at).map((binder) => binder.name);

  return names.length === 0 ? bound : new Set([...bound, ...names]);
}

/** `term`'s binding occurrences that bind in its argument `at`, with their indices. */
function bindersOver(
  term: AppTerm,
  at: number,
): (VariableTerm & { readonly index: number })[] {
  return term.bindings.flatMap((binding) => {
    const binder = term.args[binding.binder];

    return binder?.kind === "variable" && binding.scope.includes(at)
      ? [{ ...binder, index: binding.binder }]
      : [];
  });
}

/** Where a variable occurrence is bound: see {@link bindingSites}. */
export interface BindingSite {
  /** The occurrence: argument indices down from the term, as `printPieces` paths run. */
  readonly path: readonly number[];
  /** The binding occurrence that binds it, the innermost; null when it is free. */
  readonly binder: readonly number[] | null;
}

/**
 * Each variable occurrence in `term` that is not itself a binding one, in
 * order, with the binding occurrence that binds it: the innermost, so in
 * `∀x(Fx ∧ ∀x Gx)` the x of Gx links to the second ∀x. Coercion nodes
 * count in the paths, since they are in the tree.
 */
export function bindingSites(term: Term): BindingSite[] {
  const sites: BindingSite[] = [];
  const visit = (
    node: Term,
    path: readonly number[],
    binders: ReadonlyMap<string, readonly number[]>,
  ): void => {
    if (node.kind === "variable") {
      if (!node.binder) {
        sites.push({ binder: binders.get(node.name) ?? null, path });
      }

      return;
    }

    node.args.forEach((arg, at) => {
      let inner = binders;

      for (const binder of bindersOver(node, at)) {
        inner = new Map(inner).set(binder.name, [...path, binder.index]);
      }

      visit(arg, [...path, at], inner);
    });
  };

  visit(term, [], new Map());

  return sites;
}

/**
 * `term` with each variable `values` names replaced, bound or free: a
 * def's binders by its arguments, a rule's metavariables by what they
 * matched. Binding is the caller's business. A variable replaced by a
 * variable keeps its occurrence's binding flag, since it stands where the
 * occurrence bound.
 */
export function substitute(
  term: Term,
  values: ReadonlyMap<string, Term>,
): Term {
  if (term.kind === "variable") {
    const value = values.get(term.name);

    if (value === undefined) {
      return term;
    }

    return value.kind === "variable" && value.binder !== term.binder
      ? { ...value, binder: term.binder }
      : value;
  }

  return { ...term, args: term.args.map((arg) => substitute(arg, values)) };
}

/**
 * The names of the variables occurring free in `term`: not in a binding
 * slot, and not bound by one around them, by {@link walkTerm}'s scoping.
 */
export function freeVariables(term: Term): Set<string> {
  const free = new Set<string>();

  walkTerm(term, (node, bound) => {
    if (node.kind === "variable" && !node.binder && !bound.has(node.name)) {
      free.add(node.name);
    }
  });

  return free;
}

/**
 * Each variable name in `term`, bound or free and binding occurrences too,
 * with its sort, in the order it first occurs.
 */
export function variables(term: Term): Map<string, string> {
  const found = new Map<string, string>();

  walkTerm(term, (node) => {
    if (node.kind === "variable" && !found.has(node.name)) {
      found.set(node.name, node.sort);
    }
  });

  return found;
}
