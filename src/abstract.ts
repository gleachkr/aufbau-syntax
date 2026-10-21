/**
 * The engine's `@abstract` with bare-name plugs: the one-hole context that
 * explains the difference between two terms, `C[x]` from `C[a]` and
 * `C[b]` (`applyAbstractBinding` in Aufbau's
 * `frontend/derived_bindings.zig`).
 *
 * - The hole and the plugs meet at a sort in the coercion graph
 *   (`meetSort`): of the plugs' own sorts and every coercion's target, in
 *   that order, the first the hole reaches whose routes from the two plugs
 *   are shortest together. A route is the first the engine finds,
 *   depth first in declaration order, not the shortest.
 * - A site is the left plug under its route to that sort on the left, and
 *   the right plug under its route on the right. The hole goes in under
 *   its own route, so `a` sitting in a term as `n2t a` is made `v2t x`.
 * - The two terms are walked in parallel, a site tried before the walk
 *   descends, so the outermost wins. Elsewhere the two must be the same
 *   variable, or the same constructor, whose arguments are walked in turn.
 *   Anything else, or no site at all, is a failure.
 * - A failure is retried once, the terms and plugs first expanded and
 *   normalized as the engine's `preprocessDerivedExpr` does: each def
 *   without dot-dummies opened, children before parents, to a depth of
 *   32. (Normal forms are this library's, which the engine's proof-free
 *   `Canonicalizer` can outrun on a sort with no `@relation`.)
 *
 * Pattern plugs (`$ ¬ (A ∧ B) $`) are not here.
 */

import { Conversion } from "./conversion.js";
import type { NormalOptions } from "./normal.js";
import type { Node, Normalizer } from "./normalizer.js";
import type { SurfaceLanguage } from "./parse.js";
import type { CoercionInfo } from "./reader/spec.js";
import type { Term } from "./term.js";

/** What an `@abstract target left right hole leftPlug rightPlug` walks, solved. */
export interface AbstractSites {
  /** The term holding the left plug. */
  readonly left: Term;
  /**
   * The term holding the right plug where the left has the left. Omitted,
   * it is `left` with every site of the left plug made the right plug: the
   * context then has the hole at every site.
   */
  readonly right?: Term;
  readonly leftPlug: Term;
  readonly rightPlug: Term;
  /** What marks the abstracted position: the hole binder's value. */
  readonly hole: Term;
}

/** The engine's `preprocess_max_depth`. */
const PREPROCESS_DEPTH = 32;

/**
 * The context `@abstract` recovers from `sites`: the left term with each
 * site made the hole. Null where the sorts do not meet, the two terms
 * differ other than at sites, or there is no site. The `variables` are
 * the statement's, as for {@link normalTerm}: the retry's rewrites check
 * dependencies with them. Throws {@link RewriteLimitError} where
 * normalizing for the retry does not terminate.
 */
export function abstractContext(
  lang: SurfaceLanguage,
  sites: AbstractSites,
  options: NormalOptions = {},
): Term | null {
  const { n } = new Conversion(lang, options.variables);
  const frame = plugFrame(lang, n, sites);

  if (frame === null) {
    return null;
  }

  const attempt = (left: Node, right: Node | null, plugs: Plugs) =>
    walk(n, frame, plugs, left, right ?? replaced(n, frame, plugs, left));
  const plugs = {
    left: n.intern(sites.leftPlug),
    right: n.intern(sites.rightPlug),
  };
  const left = n.intern(sites.left);
  const right = sites.right === undefined ? null : n.intern(sites.right);
  const found =
    attempt(left, right, plugs) ??
    attempt(
      preprocess(n, left),
      right === null ? null : preprocess(n, right),
      { left: preprocess(n, plugs.left), right: preprocess(n, plugs.right) },
    );

  return found === null ? null : n.toTerm(found);
}

/** The two plugs' values. */
interface Plugs {
  readonly left: Node;
  readonly right: Node;
}

/** Where the walk substitutes: the hole at the meeting sort, and each plug's route there. */
interface Frame {
  readonly hole: Node;
  readonly leftLift: readonly CoercionInfo[];
  readonly rightLift: readonly CoercionInfo[];
}

/** The frame for `sites`, or null where the hole and plugs meet at no sort. */
function plugFrame(
  lang: SurfaceLanguage,
  n: Normalizer,
  sites: AbstractSites,
): Frame | null {
  const meet = meetSort(
    lang,
    sites.hole.sort,
    sites.leftPlug.sort,
    sites.rightPlug.sort,
  );

  return meet === null
    ? null
    : {
        hole: lift(n, n.intern(sites.hole), meet.hole),
        leftLift: meet.left,
        rightLift: meet.right,
      };
}

/**
 * The sort the hole and both plugs meet at, with the routes there: of the
 * sorts all three reach, the one nearest the plugs, the plugs' own sorts
 * first on a tie.
 */
function meetSort(
  lang: SurfaceLanguage,
  hole: string,
  left: string,
  right: string,
): {
  readonly hole: readonly CoercionInfo[];
  readonly left: readonly CoercionInfo[];
  readonly right: readonly CoercionInfo[];
} | null {
  let best: ReturnType<typeof meetSort> = null;

  for (const candidate of [
    left,
    right,
    ...lang.spec.coercions.map((coercion) => coercion.to),
  ]) {
    const routes = {
      hole: route(lang, hole, candidate),
      left: route(lang, left, candidate),
      right: route(lang, right, candidate),
    };

    if (
      routes.hole !== null &&
      routes.left !== null &&
      routes.right !== null &&
      (best === null ||
        routes.left.length + routes.right.length <
          best.left.length + best.right.length)
    ) {
      best = { hole: routes.hole, left: routes.left, right: routes.right };
    }
  }

  return best;
}

/**
 * The coercions from `from` up to `to`, innermost first, as the engine's
 * `coercionRoute` finds them: depth first, in declaration order, with one
 * more step than there are coercions. Null where there is none.
 */
function route(
  lang: SurfaceLanguage,
  from: string,
  to: string,
  fuel = lang.spec.coercions.length + 1,
): CoercionInfo[] | null {
  if (from === to) {
    return [];
  }

  if (fuel === 0) {
    return null;
  }

  for (const coercion of lang.spec.coercions) {
    if (coercion.from !== from) {
      continue;
    }

    const rest = route(lang, coercion.to, to, fuel - 1);

    if (rest !== null) {
      return [coercion, ...rest];
    }
  }

  return null;
}

/** `node` under the coercions of `lift`, innermost first. */
function lift(
  n: Normalizer,
  node: Node,
  lift: readonly CoercionInfo[],
): Node {
  return lift.reduce(
    (inner, coercion) => n.app(coercion.name, coercion.to, [inner]),
    node,
  );
}

/** The argument under the coercions of `lift`, or null where `node` is not that chain. */
function peel(node: Node, lift: readonly CoercionInfo[]): Node | null {
  let current = node;

  for (let at = lift.length - 1; at >= 0; at -= 1) {
    if (current.term !== lift[at]?.name || current.args.length !== 1) {
      return null;
    }

    current = current.args[0] as Node;
  }

  return current;
}

/** The context the two terms differ by, or null where they do not differ at sites alone. */
function walk(
  n: Normalizer,
  frame: Frame,
  plugs: Plugs,
  left: Node,
  right: Node,
): Node | null {
  let found = false;
  const step = (lhs: Node, rhs: Node): Node | null => {
    if (
      peel(lhs, frame.leftLift) === plugs.left &&
      peel(rhs, frame.rightLift) === plugs.right
    ) {
      found = true;
      return frame.hole;
    }

    if (lhs.term === null || rhs.term === null) {
      return lhs === rhs ? lhs : null;
    }

    if (lhs.term !== rhs.term || lhs.args.length !== rhs.args.length) {
      return null;
    }

    const args: Node[] = [];

    for (const [at, arg] of lhs.args.entries()) {
      const context = step(arg, rhs.args[at] as Node);

      if (context === null) {
        return null;
      }

      args.push(context);
    }

    return n.withArgs(lhs, args);
  };
  const context = step(left, right);

  return found ? context : null;
}

/** `node` with every site of the left plug made the right plug, the outermost first. */
function replaced(
  n: Normalizer,
  frame: Frame,
  plugs: Plugs,
  node: Node,
): Node {
  if (peel(node, frame.leftLift) === plugs.left) {
    return lift(n, plugs.right, frame.rightLift);
  }

  return node.term === null
    ? node
    : n.withArgs(
        node,
        node.args.map((arg) => replaced(n, frame, plugs, arg)),
      );
}

/**
 * `node` as the retry compares it (`preprocessDerivedExpr`): a def without
 * dot-dummies opened, its children so prepared, the result normalized and
 * opened again if it is such a def, to a depth of 32. Each term starts
 * from no normal forms and a fresh budget, as the engine's canonicalizer
 * for it does.
 */
function preprocess(n: Normalizer, node: Node): Node {
  n.reset();

  const inner = (current: Node, depth: number): Node => {
    if (depth >= PREPROCESS_DEPTH) {
      return current;
    }

    const opened = n.unfold(current);

    if (opened !== null && opened !== current) {
      return inner(opened, depth + 1);
    }

    const aligned = n.normalize(
      current.term === null
        ? current
        : n.withArgs(
            current,
            current.args.map((arg) => inner(arg, depth + 1)),
          ),
    );
    const again = n.unfold(aligned);

    return again !== null && again !== aligned
      ? inner(again, depth + 1)
      : aligned;
  };

  return inner(node, 0);
}
