/**
 * Whether the engine converts a statement it has into one it wants: the
 * decision `convertTo` in Aufbau's `compiler/check/matching.zig` makes for
 * a cited line, a rule's conclusion and the theorem's last line alike,
 * with the proofs it writes left out.
 *
 * It is a ladder. The first rung that relates the two decides:
 *
 * 1. The two are the same term.
 * 2. They compare through their defs (`compareTransparent`).
 * 3. Otherwise, unless a def is involved, they must share a normal form,
 *    or no rung below can relate them.
 * 4. The defs `want` keeps folded, folded into `have` where `have` holds
 *    their bodies, then normalized to `want`.
 * 5. The two normalized to a common target: a rearrangement of their
 *    bags' members first, then each side's normal form and the target
 *    between them.
 * 6. `have`'s normal form compares through its defs with `want`.
 * 7. `have` compares through its defs with `want`'s normal form.
 *
 * Each rung starts from a normalizer of its own, as in the engine: no
 * normal forms yet and a fresh step budget. Every rung that normalizes does so by proving, so a step the engine
 * cannot state ({@link Unstatable}) fails that rung, and the next one
 * gets its turn. A rung that runs into the rewrite limit fails the same
 * way; if nothing succeeds and the first failure was the limit, it is
 * thrown, as the engine reports it. A congruence step whose instance
 * breaks its rule's dependencies is another matter: the engine writes it
 * without checking, the rung succeeds, and the line is refused when its
 * proof is checked, with no later rung tried.
 *
 * Rungs 2, 4, 6 and 7 compare through defs without the rewrite registry,
 * as the engine's `canConvertTransparent` does; the normal forms and
 * common targets compare with it ({@link Transparency}).
 *
 * Where the engine searches for a common target, it searches greedily, as
 * written, and this module follows it step for step: which members pair,
 * which a def covers, when a def is opened. The order it pairs members in
 * is its own sort order, which differs from this module's where variables
 * are concerned.
 *
 * Not yet followed: the engine's bounded semantic search for a match
 * through a def, and the fresh variable it may give a dot-dummy the other
 * side never fixes (see `witness.ts`).
 */

import type { Absorber, Node, Variables } from "./normalizer.js";
import { Normalizer, RewriteLimitError, Unstatable } from "./normalizer.js";
import type { SurfaceLanguage } from "./parse.js";
import type { Combiner } from "./rewrite.js";
import type { Term } from "./term.js";
import { Opening } from "./witness.js";

/** One leaf of a bag in a common-target search (`AcuiLeaf`). */
interface Leaf {
  readonly old: Node;
  /** What the leaf becomes on the way to the target. */
  now: Node;
  /** Whether a def with a definiens stands anywhere in it. */
  readonly isDef: boolean;
  /** Paired with a member of the other side, or cancelled against one. */
  exact: boolean;
  /** A def leaf that took the place of members of the other side. */
  claimed: boolean;
}

/** A failure that ends a rung, where the next one gets its turn. */
function failsRung(error: unknown): boolean {
  return error instanceof Unstatable || error instanceof RewriteLimitError;
}

export class Conversion implements Absorber {
  /** The normalizer, whose normal forms absorb members the way this compares them. */
  readonly n: Normalizer;
  /** Through defs as the ladder's own checks compare. */
  private readonly plain: Transparency;
  /** Through defs as the normalizer's def operations compare. */
  private readonly registered: Transparency;
  private readonly folds = new Map<string, Node | null>();
  private readonly openedInBags = new Map<string, Node>();

  constructor(lang: SurfaceLanguage, variables?: Variables) {
    this.n = new Normalizer(lang, this, variables);
    this.plain = new Transparency(this.n, false);
    this.registered = new Transparency(this.n, true);
  }

  alike(lhs: Node, rhs: Node): boolean {
    return this.registered.alike(lhs, rhs);
  }

  /** Whether the engine converts a proof of `have` into one of `want`. */
  converts(have: Node, want: Node): boolean {
    if (have === want || this.plain.alike(want, have)) {
      return true;
    }

    if (!this.mayMeet(have, want)) {
      return false;
    }

    const rungs = [
      () => this.folded(have, want),
      () => this.normalized(have, want),
      () => this.normalizedThenUnfolded(have, want),
      () => this.unfoldedToNormalForm(have, want),
    ];
    let first: unknown = null;

    for (const rung of rungs) {
      // Each rung has a normalizer of its own in the engine.
      this.n.reset();
      this.n.poisoned = false;

      try {
        // The engine commits to the first rung that relates the two, and
        // checks the proof it wrote only then.
        if (rung()) {
          return !this.n.poisoned;
        }
      } catch (error) {
        if (!failsRung(error)) {
          throw error;
        }

        first ??= error;
      }
    }

    if (first instanceof RewriteLimitError) {
      throw first;
    }

    return false;
  }

  /**
   * `mayMeet`: whether the rungs below could relate the two. Without a
   * def on either side, two terms meet only in a shared normal form, or
   * through a def a rewrite brings in.
   */
  private mayMeet(have: Node, want: Node): boolean {
    if (this.n.isDefBearing(have) || this.n.isDefBearing(want)) {
      return true;
    }

    let canonical: [Node, Node];

    try {
      this.n.freshBudget();
      const left = this.n.normalize(have);
      this.n.freshBudget();
      canonical = [left, this.n.normalize(want)];
    } catch (error) {
      // The engine's `mayMeet` takes any failure to normalize, a dot-dummy
      // left without a witness included, as a reason to try the rungs.
      if (failsRung(error)) {
        return true;
      }

      throw error;
    }

    return (
      canonical[0] === canonical[1] ||
      this.n.isDefBearing(canonical[0]) ||
      this.n.isDefBearing(canonical[1])
    );
  }

  // ## Rung 4: folding

  /**
   * `convertFolded`: `want`'s def applications folded into `have` wherever
   * the two walk in step, and the folded statement normalized to `want`.
   */
  private folded(have: Node, want: Node): boolean {
    if (!this.hasDefApp(want)) {
      return false;
    }

    const intermediate = this.fold(have, want);

    // `fold` never gives back `have` itself.
    if (intermediate === null || !this.plain.alike(intermediate, have)) {
      return false;
    }

    return intermediate === want || this.normalized(intermediate, want);
  }

  private hasDefApp(node: Node): boolean {
    return (
      this.n.isDefApp(node) || node.args.some((arg) => this.hasDefApp(arg))
    );
  }

  /** `Folder.fold`: `raw` with `user`'s def applications folded in. */
  private fold(raw: Node, user: Node): Node | null {
    if (raw === user) {
      return null;
    }

    const key = `${raw.id},${user.id}`;

    if (!this.folds.has(key)) {
      this.folds.set(key, this.foldUncached(raw, user));
    }

    return this.folds.get(key) ?? null;
  }

  private foldUncached(raw: Node, user: Node): Node | null {
    if (this.n.isDefApp(user) && this.plain.alike(user, raw)) {
      return user;
    }

    const leaf = this.foldBagLeaf(raw, user);

    if (leaf !== null) {
      return leaf;
    }

    if (
      raw.term === null ||
      raw.term !== user.term ||
      raw.args.length !== user.args.length
    ) {
      return null;
    }

    let changed = false;
    const args = raw.args.map((arg, at) => {
      const folded = this.fold(arg, user.args[at] as Node);

      if (folded === null) {
        return arg;
      }

      changed = true;
      return folded;
    });

    return changed ? this.n.withArgs(raw, args) : null;
  }

  /**
   * `foldAcuiLeaf`: under a combiner both sides share, the first leaf of
   * `raw` that a def member of `user` unfolds to, replaced by that member.
   */
  private foldBagLeaf(raw: Node, user: Node): Node | null {
    const combiner = this.sharedCombiner(raw, user);

    if (combiner === null) {
      return null;
    }

    const defs = this.n
      .setItems(user, combiner)
      .filter((item) => this.n.isDefApp(item));

    if (defs.length === 0) {
      return null;
    }

    for (const leaf of this.n.leaves(raw, combiner)) {
      for (const def of defs) {
        if (leaf !== def && this.plain.alike(def, leaf)) {
          return this.replaceFirstLeaf(raw, combiner, leaf, def).node;
        }
      }
    }

    return null;
  }

  private replaceFirstLeaf(
    node: Node,
    combiner: Combiner,
    old: Node,
    now: Node,
  ): { node: Node; replaced: boolean } {
    if (node === old) {
      return { node: now, replaced: true };
    }

    if (!this.n.isBag(node, combiner)) {
      return { node, replaced: false };
    }

    const left = this.replaceFirstLeaf(
      node.args[0] as Node,
      combiner,
      old,
      now,
    );
    const right = left.replaced
      ? { node: node.args[1] as Node, replaced: false }
      : this.replaceFirstLeaf(node.args[1] as Node, combiner, old, now);

    return {
      node: this.n.withArgs(node, [left.node, right.node]),
      replaced: left.replaced || right.replaced,
    };
  }

  /**
   * `sharedStructuralCombiner`: the combiner heading either side, where
   * the other has its sort; else the one combiner of the sort both have.
   */
  private sharedCombiner(lhs: Node, rhs: Node): Combiner | null {
    const left = this.n.combinerNamed(lhs.term);

    if (left !== null && left.sort === rhs.sort) {
      return left;
    }

    const right = this.n.combinerNamed(rhs.term);

    if (right !== null && right.sort === lhs.sort) {
      return right;
    }

    return lhs.sort === rhs.sort ? this.n.combinerForSort(lhs.sort) : null;
  }

  // ## Rung 5: normal forms and a common target

  /**
   * `buildNormalizedConversion`: a rearrangement of the two, or their
   * normal forms and a common target between them.
   */
  private normalized(actual: Node, expected: Node): boolean {
    if (!this.n.hasRelation(actual.sort)) {
      return false;
    }

    // A rearrangement that fails takes the lines it wrote with it.
    const poisoned = this.n.poisoned;

    try {
      if (this.rearrangement(actual, expected)) {
        return true;
      }
    } catch (error) {
      if (!failsRung(error)) {
        throw error;
      }
    }

    this.n.poisoned = poisoned;

    // The engine clears its normalizer before the normal forms below
    // (`cache.clearRetainingCapacity(); step_count = 0`), which then share
    // one budget.
    this.n.reset();

    const left = this.n.proved(actual);
    const right = this.n.proved(expected);

    return this.commonTarget(left, right) !== null;
  }

  /**
   * `buildCommonTarget`: a term both normal forms convert to. Inside a bag
   * of `enclosing`, two members do not meet again as bags of it: they would
   * be one-member bags of it, paired here once more without end.
   */
  private commonTarget(
    lhs: Node,
    rhs: Node,
    enclosing: Combiner | null = null,
  ): Node | null {
    if (lhs === rhs) {
      return lhs;
    }

    const throughDef = this.defCommonTarget(lhs, rhs);

    if (throughDef !== null) {
      return throughDef;
    }

    const combiner = this.sharedCombiner(lhs, rhs);

    if (combiner !== null && combiner.term !== enclosing?.term) {
      const bag = this.bagCommonTarget(lhs, rhs);

      if (bag !== null) {
        return bag;
      }

      // Two bags of a commutative combiner have just been compared member
      // by member; the descent below would pair the same members in one
      // fixed order.
      if (
        combiner.commutative &&
        this.n.isBag(lhs, combiner) &&
        this.n.isBag(rhs, combiner)
      ) {
        return null;
      }
    }

    return this.argumentCommonTarget(lhs, rhs);
  }

  /**
   * `buildDefCommonTarget`: one side through its defs, or a def opened
   * toward the other side and normalized on its own.
   */
  private defCommonTarget(lhs: Node, rhs: Node): Node | null {
    if (!this.n.isDefBearing(lhs) && !this.n.isDefBearing(rhs)) {
      return null;
    }

    if (!this.n.hasRelation(lhs.sort)) {
      return null;
    }

    if (this.registered.alike(lhs, rhs)) {
      return rhs;
    }

    if (this.registered.alike(rhs, lhs)) {
      return lhs;
    }

    return this.fromDef(lhs, rhs) ?? this.fromDef(rhs, lhs);
  }

  /** `buildSemanticCommonTargetFromDef`. */
  private fromDef(def: Node, other: Node): Node | null {
    const witness = this.registered.opening.open(def, other);

    if (witness === null) {
      return null;
    }

    const normal = this.n.proved(witness);

    return this.commonTarget(normal, other);
  }

  /**
   * `buildNonAcuiCommonTarget`: one head, a common target for each
   * argument that differs, and the congruence steps to it on both sides.
   */
  private argumentCommonTarget(lhs: Node, rhs: Node): Node | null {
    if (
      lhs.term === null ||
      lhs.term !== rhs.term ||
      lhs.args.length !== rhs.args.length
    ) {
      return null;
    }

    const args: Node[] = [];

    for (const [at, arg] of lhs.args.entries()) {
      const other = rhs.args[at] as Node;
      const target = this.commonTarget(arg, other);

      if (target === null) {
        return null;
      }

      args.push(target);
    }

    const target = this.n.withArgs(lhs, args);

    this.n.congruence(lhs, target);
    this.n.congruence(rhs, target);
    return target;
  }

  /**
   * `buildAcuiCommonTarget`: two bags of one combiner matched member by
   * member. Members alike cancel; the rest pair where they have a common
   * target of their own, in order, each with the first it meets; a def
   * member takes the place of members of the other side it covers; and a
   * def member nothing covered is opened, and the comparison run again on
   * the opened bags.
   */
  private bagCommonTarget(lhs: Node, rhs: Node): Node | null {
    if (!this.n.hasRelation(lhs.sort)) {
      return null;
    }

    const combiner = this.sharedCombiner(lhs, rhs);

    if (combiner === null) {
      return null;
    }

    const left = this.leavesOf(lhs, combiner);
    const right = this.leavesOf(rhs, combiner);
    const common: Node[] = [];

    this.cancelAlike(left, right, common);

    for (const one of left) {
      if (one.exact) {
        continue;
      }

      for (const other of right) {
        if (other.exact) {
          continue;
        }

        // `buildMemberCommonTarget`.
        const target = this.commonTarget(one.old, other.old, combiner);

        if (target === null) {
          continue;
        }

        one.exact = true;
        other.exact = true;
        one.now = target;
        other.now = target;
        common.push(target);
        break;
      }
    }

    this.claimCovered(left, right, combiner);
    this.claimCovered(right, left, combiner);

    if (this.uncoveredDef(left) || this.uncoveredDef(right)) {
      return this.openedCommonTarget(lhs, rhs, left, right, combiner);
    }

    const items = [...common];

    for (const leaves of [left, right]) {
      for (const leaf of leaves) {
        if (leaf.exact) {
          continue;
        }

        if (leaf.isDef) {
          items.push(leaf.old);
        } else if (leaf.now === leaf.old) {
          return null;
        }
      }
    }

    const target = this.n.canonicalOf(items, combiner);

    // The engine writes both sides' steps before it compares either.
    const leftTarget = this.rewriteLeaves(lhs, combiner, left);
    const rightTarget = this.rewriteLeaves(rhs, combiner, right);

    return leftTarget === target && rightTarget === target ? target : null;
  }

  private leavesOf(node: Node, combiner: Combiner): Leaf[] {
    return this.n.leaves(node, combiner).map((leaf) => ({
      claimed: false,
      exact: false,
      isDef: this.n.isDefBearing(leaf),
      now: leaf,
      old: leaf,
    }));
  }

  /** `cancelExactAcuiItems`: the members both sorted bags hold, in one pass. */
  private cancelAlike(left: Leaf[], right: Leaf[], common: Node[]): void {
    let at = 0;
    let other = 0;

    while (at < left.length && other < right.length) {
      const one = left[at] as Leaf;
      const two = right[other] as Leaf;
      const order = this.n.compare(one.old, two.old);

      if (order < 0) {
        at += 1;
      } else if (order > 0) {
        other += 1;
      } else {
        one.exact = true;
        two.exact = true;
        common.push(one.old);
        at += 1;
        other += 1;
      }
    }
  }

  /**
   * `claimOppositeConcreteLeaves`: each def member of `owners` takes the
   * place of every member of `concretes`, holding no def, that it covers.
   */
  private claimCovered(
    owners: Leaf[],
    concretes: Leaf[],
    combiner: Combiner,
  ): void {
    for (const owner of owners) {
      if (owner.exact || !owner.isDef) {
        continue;
      }

      for (const concrete of concretes) {
        if (
          concrete.exact ||
          concrete.isDef ||
          concrete.now !== concrete.old
        ) {
          continue;
        }

        if (this.covers(owner.old, concrete.old, combiner)) {
          concrete.now = owner.old;
          owner.claimed = true;
        }
      }
    }
  }

  /**
   * `buildConcreteToDefCoverProof`: whether a member holding no def can be
   * converted to a def member, argument by argument or by opening the def
   * into a bag of the combiner that comes to just that member. The steps
   * it takes are charged whether or not it succeeds, as the engine writes
   * them.
   */
  covers(def: Node, concrete: Node, combiner: Combiner): boolean {
    if (this.argumentCommonTarget(def, concrete) !== null) {
      return true;
    }

    const witness = this.registered.opening.openTowardMember(
      def,
      concrete,
      combiner,
    );

    if (witness === null || witness === concrete) {
      return witness !== null;
    }

    return (
      this.n.isBag(witness, combiner) &&
      this.n.exact(witness, combiner) === concrete
    );
  }

  private uncoveredDef(leaves: readonly Leaf[]): boolean {
    return leaves.some((leaf) => leaf.isDef && !leaf.exact && !leaf.claimed);
  }

  /**
   * `buildOpenedDefCommonTarget`: the comparison again, with each def
   * member nothing covered opened into the bag.
   */
  private openedCommonTarget(
    lhs: Node,
    rhs: Node,
    left: readonly Leaf[],
    right: readonly Leaf[],
    combiner: Combiner,
  ): Node | null {
    const leftNext = this.openUncovered(lhs, left, combiner) ?? lhs;
    const rightNext = this.openUncovered(rhs, right, combiner) ?? rhs;

    // Normalizing can fold an opened copy straight back into a def member
    // it equals; a round that changes neither side would not end.
    if (leftNext === lhs && rightNext === rhs) {
      return null;
    }

    return this.bagCommonTarget(leftNext, rightNext);
  }

  private openUncovered(
    node: Node,
    leaves: readonly Leaf[],
    combiner: Combiner,
  ): Node | null {
    let any = false;
    const opened = leaves.map((leaf): Leaf => {
      const body =
        leaf.isDef && !leaf.exact && !leaf.claimed
          ? this.n.unfold(leaf.old)
          : null;

      any ||= body !== null;
      return { ...leaf, now: body ?? leaf.old };
    });

    return any ? this.rewriteLeaves(node, combiner, opened) : null;
  }

  /** {@link Normalizer.rewriteLeaves}, each leaf replaced by what it becomes. */
  private rewriteLeaves(
    node: Node,
    combiner: Combiner,
    leaves: readonly Leaf[],
  ): Node {
    return this.n.rewriteLeaves(
      node,
      combiner,
      leaves.map((leaf) => leaf.now),
    );
  }

  // ## Rung 5: rearranging members

  /**
   * `buildRearrangement`: whether the two differ only in how their
   * commutative bags' members are ordered, grouped and repeated: as
   * written, with the defs standing in their bags opened, or with each
   * member then normalized where it stands. Throws {@link Unstatable}
   * where the moves cannot be lifted.
   */
  private rearrangement(lhs: Node, rhs: Node): boolean {
    if (this.isRearrangement(lhs, rhs)) {
      this.rearrange(lhs, rhs);
      return true;
    }

    const leftOpen = this.openInBags(lhs, false);
    const rightOpen = this.openInBags(rhs, false);

    if (
      (leftOpen !== lhs || rightOpen !== rhs) &&
      this.isRearrangement(leftOpen, rightOpen)
    ) {
      this.rearrange(leftOpen, rightOpen);
      return true;
    }

    const normalized = new Map<number, Node | null>();
    const left = this.normalizeMembers(leftOpen, normalized);
    const right =
      left === null ? null : this.normalizeMembers(rightOpen, normalized);

    if (
      left === null ||
      right === null ||
      (left === leftOpen && right === rightOpen) ||
      !this.isRearrangement(left, right)
    ) {
      return false;
    }

    this.rearrange(left, right);
    return true;
  }

  /** A commutative bag: a binary application of a combiner that commutes. */
  private commutativeOf(node: Node): Combiner | null {
    const combiner = this.n.combinerOf(node);

    return combiner?.commutative ? combiner : null;
  }

  /**
   * `isRearrangement`: the same term outside the commutative bags, and
   * bags holding the same members, none of them the unit.
   */
  private isRearrangement(lhs: Node, rhs: Node): boolean {
    if (lhs === rhs) {
      return true;
    }

    if (
      lhs.term === null ||
      lhs.term !== rhs.term ||
      lhs.args.length !== rhs.args.length
    ) {
      return false;
    }

    const combiner = this.n.combinerOf(lhs);

    if (combiner !== null) {
      return (
        combiner.commutative &&
        this.n.sameMembers(lhs, rhs, combiner) &&
        !this.n
          .leaves(lhs, combiner)
          .some((leaf) => this.n.isUnit(leaf, combiner))
      );
    }

    return lhs.args.every((arg, at) =>
      this.isRearrangement(arg, rhs.args[at] as Node),
    );
  }

  /**
   * `openDefs`: each def standing in a commutative bag opened, as a member
   * of one or as a def whose body is one.
   */
  private openInBags(node: Node, inBag: boolean): Node {
    const key = `${node.id},${inBag}`;
    let found = this.openedInBags.get(key);

    if (found === undefined) {
      found = this.openInBagsUncached(node, inBag);
      this.openedInBags.set(key, found);
    }

    return found;
  }

  private openInBagsUncached(node: Node, inBag: boolean): Node {
    if (node.term === null) {
      return node;
    }

    if (this.commutativeOf(node) !== null) {
      return this.n.withArgs(
        node,
        node.args.map((arg) => this.openInBags(arg, true)),
      );
    }

    const body = this.n.unfold(node);

    if (body !== null && (inBag || this.commutativeOf(body) !== null)) {
      return this.openInBags(body, true);
    }

    return this.n.withArgs(
      node,
      node.args.map((arg) => this.openInBags(arg, false)),
    );
  }

  /**
   * `normalizeMembers`: the term normalized but for the order of its
   * commutative bags, each member normalized where it stands. Null where
   * it holds no commutative bag.
   */
  private normalizeMembers(
    node: Node,
    normalized: Map<number, Node | null>,
  ): Node | null {
    if (normalized.has(node.id)) {
      return normalized.get(node.id) ?? null;
    }

    let result: Node | null = null;

    if (node.term !== null) {
      const members = node.args.map((arg) =>
        this.normalizeMembers(arg, normalized),
      );

      if (
        this.commutativeOf(node) !== null ||
        members.some((member) => member !== null)
      ) {
        result = this.n.withArgs(
          node,
          node.args.map((arg, at) => members[at] ?? this.n.proved(arg)),
        );
        this.n.congruence(node, result);
      }
    }

    normalized.set(node.id, result);
    return result;
  }

  /**
   * `rearrange`: the moves from `lhs` to `rhs`, which differ only by a
   * rearrangement, lifted out of the terms around them.
   */
  private rearrange(lhs: Node, rhs: Node): void {
    if (lhs === rhs) {
      return;
    }

    const combiner = this.n.combinerOf(lhs);

    if (combiner !== null) {
      if (!this.n.hasRelation(lhs.sort)) {
        throw new Unstatable();
      }

      new Mover(this.n, combiner).permute(lhs, rhs);
      return;
    }

    lhs.args.forEach((arg, at) => {
      this.rearrange(arg, rhs.args[at] as Node);
    });
    this.n.congruence(lhs, rhs);
  }

  // ## Rungs 6 and 7

  /** `convertNormalizedThenUnfolded`: `have` normalizes to what unfolds to `want`. */
  private normalizedThenUnfolded(have: Node, want: Node): boolean {
    const normal = this.expectedNormalization(have);

    return normal !== null && this.plain.alike(want, normal);
  }

  /** `convertUnfoldedToNormalForm`: `have` unfolds to `want`'s normal form. */
  private unfoldedToNormalForm(have: Node, want: Node): boolean {
    const normal = this.expectedNormalization(want);

    return normal !== null && this.plain.alike(normal, have);
  }

  /** `buildExpectedNormalization`: a normal form other than the term itself. */
  private expectedNormalization(node: Node): Node | null {
    if (!this.n.hasRelation(node.sort)) {
      return null;
    }

    const normal = this.n.proved(node);

    return normal === node ? null : normal;
  }
}

/**
 * `compareTransparent` in one of the engine's two def contexts: with the
 * rewrite registry, as its normalizer's def operations run it, or without,
 * as the ladder's own checks do (`canConvertTransparent`). They differ in
 * where a dot-dummy's witness may come from: only with the registry do the
 * members of a bag guide it. (Other registry-only behaviour prunes the
 * search, or belongs to the semantic search, which is not followed.)
 */
class Transparency {
  private readonly results = new Map<string, boolean>();
  readonly opening: Opening;

  constructor(
    private readonly n: Normalizer,
    registry: boolean,
  ) {
    this.opening = new Opening(
      n,
      (lhs, rhs) => this.alike(lhs, rhs),
      registry,
    );
  }

  /**
   * `compareTransparent`: the two alike once defs are opened where they
   * stand. Two applications of one head compare argument by argument; a
   * def application facing anything else is opened toward it. Nothing is
   * reordered and nothing rewritten.
   */
  alike(lhs: Node, rhs: Node): boolean {
    if (lhs === rhs) {
      return true;
    }

    const key = `${lhs.id},${rhs.id}`;
    let found = this.results.get(key);

    if (found === undefined) {
      found = this.alikeUncached(lhs, rhs);
      this.results.set(key, found);
    }

    return found;
  }

  private alikeUncached(lhs: Node, rhs: Node): boolean {
    if (
      lhs.term !== null &&
      lhs.term === rhs.term &&
      lhs.args.length === rhs.args.length
    ) {
      const differs = lhs.args.findIndex(
        (arg, at) => !this.alike(arg, rhs.args[at] as Node),
      );

      if (differs < 0) {
        return true;
      }

      // A def may drop or bury the argument that differs, so opening it
      // can still reconcile the two; not where the head forces it.
      if (this.argDetermined(lhs.term, differs, 0)) {
        return false;
      }
    }

    const left = this.opening.open(lhs, rhs);

    if (left !== null && this.alike(left, rhs)) {
      return true;
    }

    const right = this.opening.open(rhs, lhs);

    return right !== null && this.alike(lhs, right);
  }

  /**
   * `head_class.argDetermined`: whether two applications of `head` alike
   * through their defs must have that argument alike. True for a rigid
   * head, and for a def whose body keeps the argument under heads that
   * force it in turn.
   */
  private argDetermined(head: string, at: number, depth: number): boolean {
    // Def bodies refer only to earlier terms; this is a guard, not a limit.
    if (depth >= 64) {
      return false;
    }

    const kind = this.n.headClass(head);

    if (kind === "rigid") {
      return true;
    }

    if (kind !== "def") {
      return false;
    }

    const definition = this.n.definitionOf(head);
    const param = definition?.binders[at];

    return (
      definition !== null &&
      param !== undefined &&
      this.determinedPath(definition.body, param, depth + 1)
    );
  }

  private determinedPath(body: Term, param: string, depth: number): boolean {
    if (body.kind === "variable") {
      return body.name === param;
    }

    return body.args.some(
      (arg, at) =>
        this.determinedPath(arg, param, depth) &&
        this.argDetermined(body.term, at, depth),
    );
  }
}

/**
 * The moves of one bag's combiner between two bags holding the same
 * members (`Mover` in `normalizer/acui/rearrange.zig`), for the one thing
 * the decision needs from them: whether each congruence step they take,
 * one changing a part of a bag, can be stated. Associativity,
 * commutativity and idempotence steps need only their rules, which a
 * combiner has.
 */
class Mover {
  constructor(
    private readonly n: Normalizer,
    private readonly combiner: Combiner,
  ) {}

  private split(node: Node): [Node, Node] | null {
    return this.n.isBag(node, this.combiner)
      ? [node.args[0] as Node, node.args[1] as Node]
      : null;
  }

  private join(lhs: Node, rhs: Node): Node {
    return this.n.app(this.combiner.term, this.combiner.sort, [lhs, rhs]);
  }

  /** Whether `member` is `bag` or a node of its spine. */
  private contains(bag: Node, member: Node): boolean {
    if (bag === member) {
      return true;
    }

    const parts = this.split(bag);

    return (
      parts !== null &&
      (this.contains(parts[0], member) || this.contains(parts[1], member))
    );
  }

  /** `old[0] ; old[1]` = `now[0] ; now[1]`, lifted through the combiner. */
  private congruence(old: [Node, Node], now: [Node, Node]): void {
    if (old[0] !== now[0] || old[1] !== now[1]) {
      this.n.congruence(this.join(old[0], old[1]), this.join(now[0], now[1]));
    }
  }

  permute(lhs: Node, rhs: Node): void {
    if (lhs === rhs) {
      return;
    }

    const rhsParts = this.split(rhs);

    if (rhsParts === null) {
      this.contract(lhs, rhs);
      return;
    }

    const lhsParts = this.split(lhs);

    if (
      lhsParts !== null &&
      this.n.sameMembers(lhsParts[0], rhsParts[0], this.combiner) &&
      this.n.sameMembers(lhsParts[1], rhsParts[1], this.combiner)
    ) {
      this.permute(lhsParts[0], rhsParts[0]);
      this.permute(lhsParts[1], rhsParts[1]);
      this.congruence(lhsParts, rhsParts);
      return;
    }

    const [front, rest] = rhsParts;
    const back = this.split(rest);

    if (back !== null) {
      // `front ; (b ; c)` read as `(front ; b) ; c`.
      this.permute(lhs, this.join(this.join(front, back[0]), back[1]));
      return;
    }

    const last = rest;

    if (this.combiner.idempotent && this.contains(front, last)) {
      this.absorb(front, last);
      this.permute(lhs, front);
      return;
    }

    if (lhsParts !== null) {
      const deep = this.split(lhsParts[1]);

      if (deep !== null && this.contains(deep[1], last)) {
        // `a ; (b ; c)` read as `(a ; b) ; c`.
        this.permute(
          this.join(this.join(lhsParts[0], deep[0]), deep[1]),
          rhs,
        );
        return;
      }
    }

    const outOfPlace = this.lastOutOfPlace(lhs, rhs);

    if (outOfPlace !== null) {
      const placed = this.extract(rhs, outOfPlace[1]);

      this.permute(outOfPlace[0], placed);
      this.congruence(outOfPlace, [placed, outOfPlace[1]]);
      return;
    }

    const extracted = this.extract(lhs, last);

    this.permute(extracted, front);
    this.congruence([extracted, last], rhsParts);
  }

  /**
   * The parts of `lhs` when its last member is the one to move: taking it
   * out of both sides leaves them ending alike for longer.
   */
  private lastOutOfPlace(lhs: Node, rhs: Node): [Node, Node] | null {
    const lhsParts = this.split(lhs);

    if (lhsParts === null || this.split(lhsParts[1]) !== null) {
      return null;
    }

    if (this.combiner.idempotent && this.contains(lhsParts[0], lhsParts[1])) {
      return null;
    }

    const left = this.n.leaves(lhs, this.combiner);
    const right = this.n.leaves(rhs, this.combiner);
    const leftLast = left.length - 1;
    const rightLast = right.length - 1;
    const leftMoves = endingAlike(
      left,
      leftLast,
      right,
      right.lastIndexOf(left[leftLast] as Node),
    );
    const rightMoves = endingAlike(
      left,
      left.lastIndexOf(right[rightLast] as Node),
      right,
      rightLast,
    );

    return leftMoves > rightMoves ? lhsParts : null;
  }

  /** `bag` = `member`, a bag whose members are all `member`. */
  private contract(bag: Node, member: Node): void {
    if (bag === member) {
      return;
    }

    const parts = this.split(bag);

    if (parts === null) {
      throw new Unstatable();
    }

    this.contract(parts[0], member);
    this.contract(parts[1], member);
    this.congruence(parts, [member, member]);
  }

  /** `bag ; member` = `bag`, for a `bag` that holds `member`. */
  private absorb(bag: Node, member: Node): void {
    if (bag === member) {
      return;
    }

    const taken = this.extractOne(bag, member);

    this.mergeTaken(bag, member, taken);
  }

  /** The rest of `bag` once `member` is taken out: every repeat where they merge. */
  private extract(bag: Node, member: Node): Node {
    let rest = this.extractOne(bag, member);

    if (!this.combiner.idempotent) {
      return rest;
    }

    while (this.contains(rest, member)) {
      const taken = this.extractOne(rest, member);

      this.mergeTaken(rest, member, taken);
      rest = taken;
    }

    return rest;
  }

  /** `bag ; member` = `rest ; member`, given that `bag` = `rest ; member`. */
  private mergeTaken(bag: Node, member: Node, rest: Node): void {
    const reappended = this.join(rest, member);

    this.congruence([bag, member], [reappended, member]);
    this.congruence([rest, this.join(member, member)], [rest, member]);
  }

  /** The rest of `bag` once one occurrence of `member` is taken out. */
  private extractOne(bag: Node, member: Node): Node {
    const parts = this.split(bag);

    if (parts === null) {
      throw new Unstatable();
    }

    const [front, back] = parts;

    if (back === member) {
      return front;
    }

    if (this.split(back) !== null && this.contains(back, member)) {
      // `front ; back` = `front ; (inner ; m)` = `(front ; inner) ; m`
      const inner = this.extractOne(back, member);

      this.congruence(parts, [front, this.join(inner, member)]);
      return this.join(front, inner);
    }

    return this.lead(bag, member);
  }

  /** The rest of `bag` once one occurrence of `member` is brought to its front. */
  private lead(bag: Node, member: Node): Node {
    const parts = this.split(bag);

    if (parts === null) {
      throw new Unstatable();
    }

    const [front, back] = parts;

    if (front === member) {
      return back;
    }

    if (back === member) {
      return front;
    }

    if (!this.contains(front, member)) {
      return this.extractOne(bag, member);
    }

    // `(m ; inner) ; back` = `m ; (inner ; back)`
    const inner = this.lead(front, member);

    this.congruence(parts, [this.join(member, inner), back]);
    return this.join(inner, back);
  }
}

/** How many members two lists end with alike, each without its `skip` index. */
function endingAlike(
  lhs: readonly Node[],
  lhsSkip: number,
  rhs: readonly Node[],
  rhsSkip: number,
): number {
  let left = lhs.length;
  let right = rhs.length;
  let count = 0;

  for (;;) {
    if (left > 0 && left - 1 === lhsSkip) {
      left -= 1;
    }

    if (right > 0 && right - 1 === rhsSkip) {
      right -= 1;
    }

    if (left === 0 || right === 0) {
      return count;
    }

    left -= 1;
    right -= 1;

    if (lhs[left] !== rhs[right]) {
      return count;
    }

    count += 1;
  }
}
