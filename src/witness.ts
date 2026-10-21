/**
 * Opening a def toward a term: its definiens over its arguments, with each
 * dot-dummy given the variable the term writes in its place. This is the
 * engine's `instantiateDefTowardExpr` (Aufbau's
 * `def_ops/symbolic_engine/transparent_match.zig`), with the conversion
 * plans it builds left out.
 *
 * The def's body is matched against the term with each dummy a slot. A
 * slot takes a variable of its sort, bound where the dummy is, that its
 * def's arguments do not mention (MMB's `UDummy` would capture it
 * otherwise), and that no sibling dummy of the same opening has taken. A
 * def met inside the body, or on the term's side, is opened in turn with
 * slots of its own, and two slots that meet are made one. A match that
 * fails is undone. Where the match as a whole fails, the arguments that
 * match on their own still guide the witnesses (`ViaTargetGuidance`).
 *
 * Not yet followed: the engine's bounded semantic search, which may also
 * rewrite or reorder on the way to a match, and the fresh variable it may
 * give a dummy the term never fixes.
 */

import type { Node, Normalizer } from "./normalizer.js";
import { Unstatable } from "./normalizer.js";
import type { Combiner } from "./rewrite.js";
import type { Term } from "./term.js";

/** A term under construction: concrete parts, dummy slots, and applications of them. */
type Sym =
  | { readonly kind: "fixed"; readonly node: Node }
  | { readonly kind: "dummy"; readonly slot: number }
  | {
      readonly kind: "app";
      readonly term: string;
      readonly args: readonly Sym[];
    };

interface Slot {
  readonly sort: string;
  /** The bound variables the expansion's arguments use, which a witness may not be. */
  readonly forbidden: ReadonlySet<string>;
  /** The expansion it came from: its siblings must stay distinct. */
  readonly group: number;
  /** All of the above as a number, for {@link Session.key}. */
  readonly id: number;
}

/**
 * The slots and witnesses of one matching attempt, undone by restoring a
 * snapshot. A match that fails leaves the session as it found it; only a
 * partial success needs one undone (the app cases, and `guide`).
 */
class Session {
  slots: Slot[] = [];
  /** Keyed by root slot. */
  witnesses = new Map<number, Node>();
  aliases = new Map<number, number>();
  /**
   * The symbolic matches that failed, with the state they failed in
   * (`sym_match_neg`): without it, two sides that keep opening defs
   * re-explore the same pairs exponentially. Shared by every snapshot,
   * since a key names its state.
   */
  failures = new Set<string>();

  snapshot(): Session {
    const copy = new Session();

    copy.failures = this.failures;

    copy.slots = [...this.slots];
    copy.witnesses = new Map(this.witnesses);
    copy.aliases = new Map(this.aliases);
    return copy;
  }

  restore(saved: Session): void {
    this.slots = [...saved.slots];
    this.witnesses = new Map(saved.witnesses);
    this.aliases = new Map(saved.aliases);
  }

  /**
   * The state a match depends on, for {@link failures}: all of it, as the
   * engine's `hashMatchSessionForSearch` has it, since a slot number is
   * reused once a failed expansion is undone.
   */
  key(): string {
    const parts = this.slots.map((slot) => `${slot.id}`);

    for (const [slot, witness] of this.witnesses) {
      parts.push(`${slot}=${witness.id}`);
    }

    for (const [slot, root] of this.aliases) {
      parts.push(`${slot}>${root}`);
    }

    return parts.join(",");
  }

  root(slot: number): number {
    let current = slot;

    for (;;) {
      const next = this.aliases.get(current);

      if (next === undefined) {
        return current;
      }

      current = next;
    }
  }

  witness(slot: number): Node | undefined {
    return this.witnesses.get(this.root(slot));
  }

  /** Whether some slot of one expansion stands for `a` and a sibling for `b`. */
  mustStayDistinct(a: number, b: number): boolean {
    return this.slots.some(
      (one, at) =>
        this.root(at) === a &&
        this.slots.some(
          (other, there) =>
            other.group === one.group && this.root(there) === b,
        ),
    );
  }
}

/** How many rounds target guidance may take; the engine's loop has no bound. */
const GUIDANCE_ROUNDS = 64;

export class Opening {
  private readonly toward = new Map<string, Node | null>();
  private readonly symKeys = new WeakMap<Sym, string>();
  private readonly slotIds = new Map<string, number>();

  constructor(
    private readonly n: Normalizer,
    private readonly transparent: (lhs: Node, rhs: Node) => boolean,
    /** Whether a bag's members may guide the witnesses: only with the engine's rewrite registry. */
    private readonly bags: boolean,
  ) {}

  /**
   * `instantiateDefTowardExpr`: `def` opened toward `target`, its dummies
   * named by what `target` writes there. Null where `def` is no def with
   * a definiens, or a dummy finds no witness.
   */
  open(def: Node, target: Node): Node | null {
    const key = `${def.id},${target.id}`;

    if (!this.toward.has(key)) {
      this.toward.set(key, this.openUncached(def, target));
    }

    return this.toward.get(key) ?? null;
  }

  private openUncached(def: Node, target: Node): Node | null {
    const definition =
      def.term === null ? null : this.n.definitionOf(def.term);

    if (definition === null) {
      return null;
    }

    // Without dummies there is nothing to choose: every path the engine
    // takes gives the plain unfolding.
    if (definition.dummies.length === 0) {
      return this.n.unfold(def);
    }

    const searched = new Session();
    const symbolic = this.expandDef(def, searched);

    if (
      symbolic !== null &&
      this.matchSymToExpr(symbolic, target, searched)
    ) {
      const witness = this.materialize(symbolic, searched);

      if (witness !== null) {
        return witness;
      }
    }

    const guided = new Session();
    const again = this.expandDef(def, guided);

    if (again === null) {
      return null;
    }

    for (let round = 0; round < GUIDANCE_ROUNDS; round += 1) {
      const witness = this.materialize(again, guided);

      if (witness !== null) {
        return witness;
      }

      if (!this.guide(again, target, guided)) {
        return null;
      }
    }

    return null;
  }

  /**
   * `instantiateDefTowardAcuiItem`: `def` opened toward one member of a
   * bag of `combiner`, which a leaf of its body is to match. Throws
   * {@link Unstatable} where the match leaves a dummy without a witness,
   * as the engine's `UnresolvedDummyWitness` aborts the comparison.
   */
  openTowardMember(def: Node, item: Node, combiner: Combiner): Node | null {
    const session = new Session();
    const symbolic = this.expandDef(def, session);

    if (
      symbolic === null ||
      !this.matchLeaf(symbolic, item, combiner, session)
    ) {
      return null;
    }

    const witness = this.materialize(symbolic, session);

    if (witness === null) {
      throw new Unstatable();
    }

    return witness;
  }

  // ## Expanding

  /** `expandConcreteDef`: a def application's body, its arguments fixed and its dummies fresh slots. */
  private expandDef(node: Node, session: Session): Sym | null {
    return node.term === null
      ? null
      : this.expandSym(
          {
            args: node.args.map((arg) => ({ kind: "fixed", node: arg })),
            kind: "app",
            term: node.term,
          },
          session,
        );
  }

  /** `expandSymbolicApp`: a def met inside a body, opened with slots of its own. */
  private expandSym(
    sym: Extract<Sym, { kind: "app" }>,
    session: Session,
  ): Sym | null {
    const definition = this.n.definitionOf(sym.term);

    if (definition === null) {
      return null;
    }

    // What a dummy's witness may not be; only a dummy reads it.
    const forbidden = new Set<string>();

    if (definition.dummies.length > 0) {
      for (const arg of sym.args) {
        this.fixedDependencies(arg, forbidden);
      }
    }

    const values = new Map<string, Sym>();

    definition.binders.forEach((name, at) => {
      const arg = sym.args[at];

      if (arg !== undefined) {
        values.set(name, arg);
      }
    });

    const group = session.slots.length;

    for (const dummy of definition.dummies) {
      values.set(dummy.name, { kind: "dummy", slot: session.slots.length });
      session.slots.push(this.slot(dummy.sort, forbidden, group));
    }

    return this.fromTerm(definition.body, values);
  }

  private slot(
    sort: string,
    forbidden: ReadonlySet<string>,
    group: number,
  ): Slot {
    const key = `${sort}:${group}:${[...forbidden].sort().join(" ")}`;
    let id = this.slotIds.get(key);

    if (id === undefined) {
      id = this.slotIds.size;
      this.slotIds.set(key, id);
    }

    return { forbidden, group, id, sort };
  }

  private fromTerm(term: Term, values: ReadonlyMap<string, Sym>): Sym {
    if (term.kind === "variable") {
      return (
        values.get(term.name) ?? {
          kind: "fixed",
          node: this.n.node(null, term.name, term.sort, []),
        }
      );
    }

    return {
      args: term.args.map((arg) => this.fromTerm(arg, values)),
      kind: "app",
      term: term.term,
    };
  }

  /** `fixedSymbolicDeps`: the bound variables the concrete parts use. */
  private fixedDependencies(sym: Sym, into: Set<string>): void {
    if (sym.kind === "fixed") {
      for (const name of this.n.dependencies(sym.node)) {
        into.add(name);
      }
    } else if (sym.kind === "app") {
      for (const arg of sym.args) {
        this.fixedDependencies(arg, into);
      }
    }
  }

  private sortOf(sym: Sym, session: Session): string {
    return sym.kind === "fixed"
      ? sym.node.sort
      : sym.kind === "dummy"
        ? (session.slots[sym.slot] as Slot).sort
        : this.n.returnSort(sym.term);
  }

  // ## Matching

  /** `matchSymbolicToExprState`. */
  private matchSymToExpr(sym: Sym, actual: Node, session: Session): boolean {
    if (sym.kind === "fixed") {
      return this.transparent(sym.node, actual);
    }

    if (sym.kind === "dummy") {
      return this.matchDummy(sym.slot, actual, session);
    }

    const saved = session.snapshot();

    if (
      actual.term === sym.term &&
      actual.args.length === sym.args.length &&
      sym.args.every((arg, at) =>
        this.matchSymToExpr(arg, actual.args[at] as Node, session),
      )
    ) {
      return true;
    }

    session.restore(saved);

    const expanded = this.expandSym(sym, session);

    if (expanded !== null && this.matchSymToExpr(expanded, actual, session)) {
      return true;
    }

    session.restore(saved);

    const opened = this.expandDef(actual, session);

    if (opened !== null && this.matchSymToSym(sym, opened, session)) {
      return true;
    }

    session.restore(saved);
    return false;
  }

  /** `matchExprToSymbolic`. */
  private matchExprToSym(actual: Node, sym: Sym, session: Session): boolean {
    if (sym.kind === "fixed") {
      return this.transparent(actual, sym.node);
    }

    if (sym.kind === "dummy") {
      return this.matchDummy(sym.slot, actual, session);
    }

    const saved = session.snapshot();

    if (
      actual.term === sym.term &&
      actual.args.length === sym.args.length &&
      sym.args.every((arg, at) =>
        this.matchExprToSym(actual.args[at] as Node, arg, session),
      )
    ) {
      return true;
    }

    session.restore(saved);

    const opened = this.expandDef(actual, session);

    if (opened !== null && this.matchSymToSym(opened, sym, session)) {
      return true;
    }

    session.restore(saved);

    const expanded = this.expandSym(sym, session);

    if (expanded !== null && this.matchExprToSym(actual, expanded, session)) {
      return true;
    }

    session.restore(saved);
    return false;
  }

  /** `matchSymbolicToSymbolicState`, remembering where it failed. */
  private matchSymToSym(lhs: Sym, rhs: Sym, session: Session): boolean {
    const key = `${this.symKey(lhs)}|${this.symKey(rhs)}|${session.key()}`;

    if (session.failures.has(key)) {
      return false;
    }

    const matched = this.matchSymToSymUncached(lhs, rhs, session);

    if (!matched) {
      session.failures.add(key);
    }

    return matched;
  }

  private symKey(sym: Sym): string {
    let key = this.symKeys.get(sym);

    if (key === undefined) {
      key =
        sym.kind === "fixed"
          ? `#${sym.node.id}`
          : sym.kind === "dummy"
            ? `$${sym.slot}`
            : `(${sym.term} ${sym.args.map((arg) => this.symKey(arg)).join(" ")})`;
      this.symKeys.set(sym, key);
    }

    return key;
  }

  private matchSymToSymUncached(
    lhs: Sym,
    rhs: Sym,
    session: Session,
  ): boolean {
    if (lhs.kind === "fixed") {
      return this.matchExprToSym(lhs.node, rhs, session);
    }

    if (lhs.kind === "dummy") {
      if (rhs.kind === "fixed") {
        return this.matchDummy(lhs.slot, rhs.node, session);
      }

      // A dummy takes only a variable, and an app is none (as in the
      // engine's `matchDummyToSymbolic`).
      return rhs.kind === "dummy" && this.align(lhs.slot, rhs.slot, session);
    }

    const saved = session.snapshot();

    if (
      rhs.kind === "app" &&
      rhs.term === lhs.term &&
      rhs.args.length === lhs.args.length &&
      lhs.args.every((arg, at) =>
        this.matchSymToSym(arg, rhs.args[at] as Sym, session),
      )
    ) {
      return true;
    }

    session.restore(saved);

    const expandedLeft = this.expandSym(lhs, session);

    if (
      expandedLeft !== null &&
      this.matchSymToSym(expandedLeft, rhs, session)
    ) {
      return true;
    }

    session.restore(saved);

    if (rhs.kind === "app") {
      const expandedRight = this.expandSym(rhs, session);

      if (
        expandedRight !== null &&
        this.matchSymToSym(lhs, expandedRight, session)
      ) {
        return true;
      }

      session.restore(saved);
    }

    return false;
  }

  /**
   * `matchSymbolicAcuiLeafToExprState`: `actual` matched against a leaf
   * of the bag `sym` builds, the first that matches.
   */
  private matchLeaf(
    sym: Sym,
    actual: Node,
    combiner: Combiner,
    session: Session,
  ): boolean {
    if (
      sym.kind === "app" &&
      sym.term === combiner.term &&
      sym.args.length === 2
    ) {
      return sym.args.some((part) =>
        this.matchLeaf(part, actual, combiner, session),
      );
    }

    return this.matchSymToExpr(sym, actual, session);
  }

  /**
   * `matchSymbolicDummyState`: a slot takes a variable of its sort, bound,
   * that its expansion's arguments do not use and no sibling has taken.
   */
  private matchDummy(slot: number, actual: Node, session: Session): boolean {
    const root = session.root(slot);
    const info = session.slots[root] as Slot;

    if (
      actual.term !== null ||
      !this.n.isBound(actual.name) ||
      actual.sort !== info.sort ||
      [...this.n.dependencies(actual)].some((name) =>
        info.forbidden.has(name),
      ) ||
      !this.respectsDistinctness(root, actual, session)
    ) {
      return false;
    }

    const existing = session.witnesses.get(root);

    if (existing !== undefined) {
      return existing === actual;
    }

    session.witnesses.set(root, actual);
    return true;
  }

  private respectsDistinctness(
    root: number,
    actual: Node,
    session: Session,
  ): boolean {
    for (const [other, witness] of session.witnesses) {
      if (
        witness === actual &&
        other !== root &&
        session.mustStayDistinct(root, other)
      ) {
        return false;
      }
    }

    return true;
  }

  /** `alignDummySlots`: two slots that meet made one, where their expansions allow. */
  private align(lhs: number, rhs: number, session: Session): boolean {
    const left = session.root(lhs);
    const right = session.root(rhs);

    if (left === right) {
      return true;
    }

    const leftInfo = session.slots[left] as Slot;
    const rightInfo = session.slots[right] as Slot;

    if (
      leftInfo.sort !== rightInfo.sort ||
      session.mustStayDistinct(left, right)
    ) {
      return false;
    }

    const leftWitness = session.witnesses.get(left);
    const rightWitness = session.witnesses.get(right);

    if (
      leftWitness !== undefined &&
      rightWitness !== undefined &&
      leftWitness !== rightWitness
    ) {
      return false;
    }

    const forbidden = new Set([
      ...leftInfo.forbidden,
      ...rightInfo.forbidden,
    ]);

    for (const witness of [leftWitness, rightWitness]) {
      if (witness === undefined) {
        continue;
      }

      if (
        [...this.n.dependencies(witness)].some((name) =>
          forbidden.has(name),
        ) ||
        !this.respectsDistinctness(left, witness, session) ||
        !this.respectsDistinctness(right, witness, session)
      ) {
        return false;
      }
    }

    const winner =
      leftWitness !== undefined
        ? left
        : rightWitness !== undefined
          ? right
          : Math.min(left, right);
    const loser = winner === left ? right : left;

    // A loser's witness, if it has one, is the winner's.
    session.witnesses.delete(loser);

    const won = session.slots[winner] as Slot;

    session.slots[winner] = this.slot(won.sort, forbidden, won.group);
    session.aliases.set(loser, winner);
    return true;
  }

  /** `materializeResolvedSymbolic`: the term, once every slot has its witness. */
  private materialize(sym: Sym, session: Session): Node | null {
    if (sym.kind === "fixed") {
      return sym.node;
    }

    if (sym.kind === "dummy") {
      return session.witness(sym.slot) ?? null;
    }

    const args: Node[] = [];

    for (const arg of sym.args) {
      const value = this.materialize(arg, session);

      if (value === null) {
        return null;
      }

      args.push(value);
    }

    return this.n.app(sym.term, this.n.returnSort(sym.term), args);
  }

  // ## Guidance

  /**
   * `guideSymbolicWitnessesFromTarget`: witnesses from the arguments that
   * match on their own, where the whole does not.
   */
  private guide(sym: Sym, target: Node, session: Session): boolean {
    if (sym.kind !== "app") {
      return false;
    }

    if (
      target.term !== null &&
      target.term === sym.term &&
      target.args.length === sym.args.length
    ) {
      const saved = session.snapshot();
      let progress = false;
      let failed = false;

      for (const [at, arg] of sym.args.entries()) {
        const other = target.args[at] as Node;

        if (this.matchSymToExpr(arg, other, session)) {
          continue;
        }

        if (!this.guide(arg, other, session)) {
          failed = true;
          break;
        }

        progress = true;
      }

      if (!failed && progress) {
        return true;
      }

      session.restore(saved);
    }

    return this.bags && this.guideFromBag(sym, target, session);
  }

  /** `guideSymbolicWitnessesFromAcuiTarget`: a leaf matched against a member of the target. */
  private guideFromBag(sym: Sym, target: Node, session: Session): boolean {
    const combiner = this.n.combinerForSort(this.sortOf(sym, session));

    return (
      combiner !== null &&
      combiner.sort === target.sort &&
      this.n
        .setItems(target, combiner)
        .some((item) => this.matchLeaf(sym, item, combiner, session))
    );
  }
}
