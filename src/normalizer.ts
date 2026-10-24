/**
 * The engine's normal form over hash-consed terms: `Canonicalizer` and
 * `Normalizer` in Aufbau's `normalizer.zig`, which agree on the form and
 * differ in whether they prove it. This one computes the form and records
 * whether a proof could state every step to it, which is where the two
 * differ in what they accept.
 *
 * - Children are normalized first.
 * - A bag of an `@acui` combiner is flattened. A member folds into a def
 *   member of the same bag that covers it, or that it is alike to through
 *   their defs (`applySameSideAbsorption`). The unit is dropped where a
 *   unit law allows. Members are sorted when the combiner commutes and
 *   merged when it is idempotent, one at a time as the engine's
 *   `mergeCanonical` does, so that the steps a proof would lift through
 *   the combiner's `@congr` are known. It is rebuilt nested to the right.
 * - Then the `@rewrite` rules headed by the term's constructor are tried in
 *   declaration order. The first whose left side matches, with its binders'
 *   sorts, boundness and dependencies respected, fires, and its result is
 *   normalized in turn. There is no backtracking.
 * - A rewrite that leads back to a term still being normalized, or a
 *   thousandth step, is a {@link RewriteLimitError}, as it is in the engine.
 *
 * Defs stay folded: the normalizer never opens one to find a redex, and a
 * member absorbed into a def member takes the def's place.
 *
 * Bags are sorted in this module's own order: variables, by their place in
 * the variables given and then by name, before applications, which go by
 * the constructor's declaration order, then arity, then arguments. The
 * engine's order differs where two variables are concerned, so a normal
 * form compares with the engine's member for member, not textually.
 */

import type { SurfaceLanguage } from "./parse.js";
import type { Definition, TermInfo } from "./reader/spec.js";
import type {
  Combiner,
  RewriteRule,
  RuleBinder,
  VariableInfo,
} from "./rewrite.js";
import { rewriteSystem } from "./rewrite.js";
import type { AppTerm, Term } from "./term.js";
import { bindsAt } from "./term.js";
import { definiens } from "./unfold.js";

export type { VariableInfo } from "./rewrite.js";

/** A scope's variables, in binder order. */
export type Variables = ReadonlyMap<string, VariableInfo>;

/** A normalization the engine also gives up on: a rewrite cycle, or its step limit. */
export class RewriteLimitError extends Error {
  readonly reason: "cycle" | "step-limit";
  /** The rule whose step closed the cycle or went past the limit. */
  readonly rule: string | null;

  constructor(reason: "cycle" | "step-limit", rule: string | null) {
    super(
      reason === "cycle"
        ? `the rewrite rules cycle${rule === null ? "" : ` at ${rule}`}`
        : `the rewrite rules take more than ${STEP_LIMIT} steps${rule === null ? "" : `, the last by ${rule}`}`,
    );
    this.name = "RewriteLimitError";
    this.reason = reason;
    this.rule = rule;
  }
}

/**
 * A step the engine could not state as a proof, so the comparison taking
 * it fails: `MissingCongruenceRule`, `DepViolation` or missing structural
 * metadata in the engine. Thrown where the engine throws, since a caller
 * that would go on to another candidate on a plain failure does not go on
 * past one of these.
 */
export class Unstatable extends Error {
  constructor() {
    super("the engine cannot state this step");
    this.name = "Unstatable";
  }
}

/** The engine's step limit, per normalization. */
const STEP_LIMIT = 1000;

/** A hash-consed term: one node per distinct term, so identity is `===`. */
export interface Node {
  readonly id: number;
  /** The constructor, or null for a variable. */
  readonly term: string | null;
  /** The variable's name; the constructor's for an application. */
  readonly name: string;
  readonly sort: string;
  readonly args: readonly Node[];
}

/** A def's definiens with what fills it: its arguments' names in order, and its dot-dummies. */
export interface DefBody {
  readonly body: Term;
  readonly binders: readonly string[];
  readonly dummies: readonly {
    readonly name: string;
    readonly sort: string;
  }[];
}

/** What a proof of some steps needs: whether it can state them, and whether one breaks its rule's dependencies. */
export interface Account {
  stated: boolean;
  violated: boolean;
}

/** A node's normalization. */
interface Normal extends Readonly<Account> {
  readonly node: Node;
}

/**
 * What same-side absorption asks of the conversion it serves: whether two
 * def members are alike through their defs (`compareTransparent`), and
 * whether a member holding no def folds into a def member
 * (`buildConcreteToDefCoverProof`). Both run inside a normalization, so
 * the steps a cover needs are entered in its account, whether or not the
 * cover is found: the proof-producing normalizer throws at the first it
 * cannot state.
 */
export interface Absorber {
  alike(lhs: Node, rhs: Node): boolean;
  covers(def: Node, concrete: Node, combiner: Combiner): boolean;
}

const IN_PROGRESS = Symbol("in progress");

/** Whether a term is a def with a definiens. */
function hasDefiniens(
  info: TermInfo | undefined,
): info is TermInfo & { readonly definition: Definition } {
  return info?.isDef === true && info.definition !== null;
}

/** A sorted list without its adjacent repeats. */
function distinct<T>(sorted: readonly T[]): T[] {
  return sorted.filter((item, at) => at === 0 || sorted[at - 1] !== item);
}

/**
 * One language's normal forms over one scope's variables. Its memo tables
 * hold every term it meets, so it lives no longer than a request: a
 * long-lived language would otherwise keep every term it was ever asked
 * about.
 */
export class Normalizer {
  private readonly nodes = new Map<string, Node>();
  private readonly normals = new Map<number, Normal | typeof IN_PROGRESS>();
  private readonly keys = new Map<number, string>();
  private readonly deps = new Map<number, ReadonlySet<string>>();
  private readonly defBearing = new Map<number, boolean>();
  private readonly definitions = new Map<string, DefBody | null>();
  private readonly termOrder: ReadonlyMap<string, number>;
  private readonly variableOrder = new Map<string, number>();
  private readonly rewrites: ReadonlyMap<string, readonly RewriteRule[]>;
  private readonly combiners: ReadonlyMap<string, Combiner>;
  private readonly combinersBySort: ReadonlyMap<string, Combiner | null>;
  private readonly congruences: ReadonlyMap<string, readonly RuleBinder[]>;
  private steps = 0;
  /**
   * Whether a step proved since this was last cleared breaks a congruence
   * rule's dependencies. The engine does not check them as it writes the
   * step, so the comparison that takes one goes on, and succeeds; the line
   * is refused when the proof is checked afterwards.
   */
  poisoned = false;
  /** The rule whose result is being normalized, which names a cycle. */
  private lastRule: string | null = null;
  /** Where a normalization under way keeps what its steps need, rather than throwing. */
  private recording: Account | null = null;

  constructor(
    private readonly lang: SurfaceLanguage,
    /** The conversion this normalizer serves, whose comparisons absorption asks. */
    private readonly absorber: Absorber,
    private readonly variables: Variables = new Map(),
  ) {
    const system = rewriteSystem(lang);

    this.rewrites = system.rewrites;
    this.combiners = system.combiners;
    this.combinersBySort = system.combinersBySort;
    this.congruences = system.congruences;
    this.termOrder = system.termOrder;
    [...variables.keys()].forEach((name, at) => {
      this.variableOrder.set(name, at);
    });
  }

  /** A fresh step budget, as each of the engine's normalizers starts with. */
  freshBudget(): void {
    this.steps = 0;
    this.lastRule = null;
  }

  /**
   * No normal forms yet and a fresh budget, as a new `Normalizer` of the
   * engine's starts: work done before does not count against it, and
   * costs it nothing either.
   */
  reset(): void {
    this.normals.clear();
    this.freshBudget();
  }

  node(
    term: string | null,
    name: string,
    sort: string,
    args: readonly Node[],
  ): Node {
    const key =
      term === null ? `$${name}` : `${term}(${args.map((a) => a.id).join()})`;
    let found = this.nodes.get(key);

    if (found === undefined) {
      found = { args, id: this.nodes.size, name, sort, term };
      this.nodes.set(key, found);
    }

    return found;
  }

  app(term: string, sort: string, args: readonly Node[]): Node {
    return this.node(term, term, sort, args);
  }

  /** `node` with `args` in place of its own. */
  withArgs(node: Node, args: readonly Node[]): Node {
    return args.every((arg, at) => arg === node.args[at])
      ? node
      : this.node(node.term, node.name, node.sort, args);
  }

  intern(term: Term): Node {
    return term.kind === "variable"
      ? this.node(null, term.name, term.sort, [])
      : this.app(
          term.term,
          term.sort,
          term.args.map((arg) => this.intern(arg)),
        );
  }

  toTerm(node: Node): Term {
    if (node.term === null) {
      return this.variableTerm(node, false);
    }

    const bindings = this.lang.spec.terms.get(node.term)?.bindings ?? [];
    const term: AppTerm = {
      args: node.args.map((arg, at) =>
        arg.term === null && bindsAt(bindings, at)
          ? this.variableTerm(arg, true)
          : this.toTerm(arg),
      ),
      bindings,
      fixity: null,
      grouped: false,
      kind: "app",
      prec: null,
      sort: node.sort,
      span: { end: 0, start: 0 },
      term: node.term,
      token: null,
    };

    return term;
  }

  private variableTerm(node: Node, binder: boolean): Term {
    return {
      binder,
      grouped: false,
      kind: "variable",
      name: node.name,
      sort: node.sort,
      span: { end: 0, start: 0 },
    };
  }

  keyOf(node: Node): string {
    let key = this.keys.get(node.id);

    if (key === undefined) {
      // `?` starts no identifier, so a variable never shares a key with a
      // constant of its name.
      key =
        node.term === null
          ? `?${node.name}`
          : node.args.length === 0
            ? node.term
            : `(${node.term} ${node.args.map((arg) => this.keyOf(arg)).join(" ")})`;
      this.keys.set(node.id, key);
    }

    return key;
  }

  /** Whether the theory declares a `@relation` for `sort`. */
  hasRelation(sort: string): boolean {
    return this.lang.spec.relations.has(sort);
  }

  // ## Normalizing

  /**
   * The normal form, whether or not a proof could state it: the
   * proof-producing normalizer's, with a step it cannot state entered in
   * the account rather than thrown. (The engine's proof-free
   * `Canonicalizer` can go further on a sort with no `@relation`, which
   * this does not follow; neither verdict depends on it.)
   */
  normalize(node: Node): Node {
    return this.normal(node).node;
  }

  private normal(node: Node): Normal {
    const cached = this.normals.get(node.id);

    if (cached === IN_PROGRESS) {
      throw new RewriteLimitError("cycle", this.lastRule);
    }

    if (cached !== undefined) {
      return cached;
    }

    this.normals.set(node.id, IN_PROGRESS);

    try {
      const result = this.normalizeUncached(node);

      this.normals.set(node.id, result);
      return result;
    } catch (error) {
      this.normals.delete(node.id);
      throw error;
    }
  }

  /** Whether a proof of `node`'s normalization would state every step and check. */
  stated(node: Node): boolean {
    const normal = this.normal(node);

    return normal.stated && !normal.violated;
  }

  /**
   * The normal form the proof-producing normalizer reaches, which throws
   * {@link Unstatable} where it cannot state a step, and marks the proof
   * {@link poisoned} where a step breaks a congruence's dependencies.
   */
  proved(node: Node): Node {
    const normal = this.normal(node);

    this.charge(normal);
    return normal.node;
  }

  private normalizeUncached(node: Node): Normal {
    const outer = this.recording;
    const account: Account = { stated: true, violated: false };

    this.recording = account;

    try {
      return { node: this.reduce(node), ...account };
    } finally {
      this.recording = outer;
    }
  }

  /** The normal form, each step charged as {@link charge} says. */
  private reduce(node: Node): Node {
    if (node.term === null) {
      return node;
    }

    let current = this.withArgs(
      node,
      node.args.map((arg) => this.proved(arg)),
    );

    this.congruence(node, current);

    // The structural pass, until it changes nothing: a bag can come out a
    // single member, headed by something else.
    for (;;) {
      const combiner = this.combinerOf(current);

      if (combiner === null) {
        break;
      }

      const bag = this.structural(current, combiner);

      if (bag === current) {
        break;
      }

      current = bag;
    }

    // The first rule that applies fires, and its result is normalized in
    // turn. A normal form is a term no rule of its head applies to, so
    // that is the whole of it.
    const rules =
      current.term === null ? undefined : this.rewrites.get(current.term);

    for (const rule of rules ?? []) {
      const result = this.applyRule(rule, current);

      if (result === null) {
        continue;
      }

      if (this.steps >= STEP_LIMIT) {
        throw new RewriteLimitError("step-limit", rule.name);
      }

      this.steps += 1;

      const outer = this.lastRule;

      this.lastRule = rule.name;
      const normal = this.proved(result);
      this.lastRule = outer;
      return normal;
    }

    return current;
  }

  /**
   * What a step needs: entered in the account of the normalization under
   * way, if there is one; otherwise, outside one, {@link Unstatable} where
   * it cannot be stated, and a {@link poisoned} proof where it breaks its
   * rule's dependencies, as the proof-producing normalizer meets it. A
   * violated step can so mark the proof before a later step throws; every
   * caller that catches the throw resets or restores {@link poisoned}.
   */
  private charge(account: Readonly<Account>): void {
    if (this.recording !== null) {
      this.recording.stated &&= account.stated;
      this.recording.violated ||= account.violated;
      return;
    }

    if (!account.stated) {
      throw new Unstatable();
    }

    if (account.violated) {
      this.poisoned = true;
    }
  }

  /** `rule`'s right side at `node`, where its left side matches; else null. */
  private applyRule(rule: RewriteRule, node: Node): Node | null {
    const bindings = new Map<string, Node>();
    const names = new Set(rule.binders.map((binder) => binder.name));

    if (!this.matchTemplate(rule.lhs, node, names, bindings)) {
      return null;
    }

    const values: Node[] = [];

    for (const binder of rule.binders) {
      const value = bindings.get(binder.name);

      // A binder the left side does not mention has no value to give.
      if (value === undefined) {
        return null;
      }

      values.push(value);
    }

    return this.admits(rule.binders, values)
      ? this.instantiate(rule.rhs, bindings)
      : null;
  }

  /**
   * What the engine's step from `before` to `after`, which differ in their
   * arguments, needs as an instance of the term's `@congr` rule. It cannot
   * be stated without one, where a bound argument changes, or where a sort
   * it relates has no `@relation` (the unchanged arguments' included, for
   * the reflexivity steps they take): the engine throws there. It is
   * violated where the instance breaks the rule's dependencies, which the
   * engine finds only when it checks the finished proof.
   */
  private liftOf(before: Node, after: Node): Account {
    const missing: Account = { stated: false, violated: false };
    const info =
      before.term === null
        ? undefined
        : this.lang.spec.terms.get(before.term);
    const congruence =
      before.term === null ? undefined : this.congruences.get(before.term);
    const relations = this.lang.spec.relations;

    if (
      info === undefined ||
      congruence === undefined ||
      !relations.has(info.returnSort)
    ) {
      return missing;
    }

    const values: Node[] = [];

    for (const [at, binder] of info.binders.entries()) {
      const old = before.args[at] as Node;
      const now = after.args[at] as Node;

      if (binder.binds) {
        if (old !== now) {
          return missing;
        }

        values.push(old);
        continue;
      }

      if (
        old === now &&
        !relations.has("sort" in binder.type ? binder.type.sort : "")
      ) {
        return missing;
      }

      values.push(old, now);
    }

    if (values.length !== congruence.length) {
      return missing;
    }

    return { stated: true, violated: !this.admits(congruence, values) };
  }

  /**
   * The congruence step from `before` to `after`, the same head with other
   * arguments, as the engine emits one: nothing where nothing changed,
   * {@link Unstatable} where it cannot state the step, and a
   * {@link poisoned} proof where the step breaks its rule's dependencies.
   */
  congruence(before: Node, after: Node): void {
    if (before !== after) {
      this.charge(this.liftOf(before, after));
    }
  }

  private matchTemplate(
    template: Term,
    node: Node,
    binders: ReadonlySet<string>,
    bindings: Map<string, Node>,
  ): boolean {
    if (template.kind === "variable" && binders.has(template.name)) {
      const bound = bindings.get(template.name);

      if (bound === undefined) {
        bindings.set(template.name, node);
        return true;
      }

      return bound === node;
    }

    if (template.kind === "variable") {
      return node.term === null && node.name === template.name;
    }

    return (
      node.term === template.term &&
      node.args.length === template.args.length &&
      template.args.every((arg, at) =>
        this.matchTemplate(arg, node.args[at] as Node, binders, bindings),
      )
    );
  }

  private instantiate(
    template: Term,
    bindings: ReadonlyMap<string, Node>,
  ): Node {
    if (template.kind === "variable") {
      return (
        bindings.get(template.name) ??
        this.node(null, template.name, template.sort, [])
      );
    }

    return this.app(
      template.term,
      template.sort,
      template.args.map((arg) => this.instantiate(arg, bindings)),
    );
  }

  /**
   * MMB's rule for a rule's arguments, as the engine checks a rewrite's:
   * each has its binder's sort, a bound binder's is a bound variable, a
   * bound binder's variable occurs in no earlier argument, and a regular
   * argument mentions no earlier bound binder's variable unless the binder
   * says it may.
   */
  private admits(
    binders: readonly RuleBinder[],
    values: readonly Node[],
  ): boolean {
    const earlier = new Set<string>();
    const bound = new Map<string, ReadonlySet<string>>();

    for (const [at, binder] of binders.entries()) {
      const value = values[at] as Node;
      const deps = this.dependencies(value);

      if (value.sort !== binder.sort) {
        return false;
      }

      if (binder.bound) {
        if (value.term !== null || !this.isBound(value.name)) {
          return false;
        }

        if ([...deps].some((name) => earlier.has(name))) {
          return false;
        }

        bound.set(binder.name, deps);
      } else {
        for (const [name, used] of bound) {
          if (
            !binder.dependencies.includes(name) &&
            [...used].some((one) => deps.has(one))
          ) {
            return false;
          }
        }
      }

      for (const name of deps) {
        earlier.add(name);
      }
    }

    return true;
  }

  isBound(name: string): boolean {
    return this.variables.get(name)?.bound ?? true;
  }

  /** The bound variables a term mentions or depends on, bound occurrences included. */
  dependencies(node: Node): ReadonlySet<string> {
    let found = this.deps.get(node.id);

    if (found === undefined) {
      if (node.term === null) {
        const info = this.variables.get(node.name);

        found =
          info === undefined || info.bound
            ? new Set([node.name])
            : new Set(info.dependencies);
      } else {
        const union = new Set<string>();

        for (const arg of node.args) {
          for (const name of this.dependencies(arg)) {
            union.add(name);
          }
        }

        found = union;
      }

      this.deps.set(node.id, found);
    }

    return found;
  }

  // ## Bags

  /** The combiner a binary application of one heads. */
  combinerOf(node: Node): Combiner | null {
    return node.term === null || node.args.length !== 2
      ? null
      : (this.combiners.get(node.term) ?? null);
  }

  /** The combiner `term` is, at any arity. */
  combinerNamed(term: string | null): Combiner | null {
    return term === null ? null : (this.combiners.get(term) ?? null);
  }

  /** The one combiner returning `sort`; null for none, or for two. */
  combinerForSort(sort: string): Combiner | null {
    return this.combinersBySort.get(sort) ?? null;
  }

  /** Whether `node` is a binary application of `combiner`. */
  isBag(node: Node, combiner: Combiner): boolean {
    return node.term === combiner.term && node.args.length === 2;
  }

  /** The leaves of a bag's spine, left to right, its units included. */
  leaves(node: Node, combiner: Combiner, into: Node[] = []): Node[] {
    if (this.isBag(node, combiner)) {
      this.leaves(node.args[0] as Node, combiner, into);
      this.leaves(node.args[1] as Node, combiner, into);
    } else {
      into.push(node);
    }

    return into;
  }

  isUnit(node: Node, combiner: Combiner): boolean {
    return node.term === combiner.unit && node.args.length === 0;
  }

  /**
   * A bag's canonical form, its members as they are
   * (`canonicalizeAcuiExact`). Without commutativity the order stands:
   * each member is put in front of the bag after it, where a unit law can
   * drop a unit and idempotence a member the bag already starts with.
   */
  canonicalBag(node: Node, combiner: Combiner): Node {
    const leaves = this.leaves(node, combiner);

    if (combiner.commutative) {
      return this.canonicalOf(leaves, combiner);
    }

    // Only the form is wanted here, not what a proof of it needs.
    const outer = this.recording;

    this.recording = { stated: true, violated: false };

    try {
      return leaves.reduceRight((canon, item) =>
        this.insert(this.join(combiner, item, canon), item, canon, combiner),
      );
    } finally {
      this.recording = outer;
    }
  }

  /**
   * The canonical bag of a commutative combiner holding `items`: the unit
   * dropped, the rest sorted, and repeats merged when it is idempotent.
   */
  canonicalOf(items: readonly Node[], combiner: Combiner): Node {
    const members = items
      .filter((item) => !(combiner.leftUnit && this.isUnit(item, combiner)))
      .sort((a, b) => this.compare(a, b));

    return this.build(
      combiner.idempotent ? distinct(members) : members,
      combiner,
    );
  }

  /**
   * `collectConcreteSetItems`: a term's canonical members as a set, the
   * unit left out only where both unit laws can remove it.
   */
  setItems(node: Node, combiner: Combiner): Node[] {
    // A commutative bag's members are sorted and merged below anyway.
    const canonical =
      !combiner.commutative && this.isBag(node, combiner)
        ? this.canonicalBag(node, combiner)
        : node;
    const skipUnit = combiner.leftUnit && combiner.rightUnit;

    return distinct(
      this.leaves(canonical, combiner)
        .filter((leaf) => !(skipUnit && this.isUnit(leaf, combiner)))
        .sort((a, b) => this.compare(a, b)),
    );
  }

  /** Whether two bags hold the same members: as a multiset, or a set where they merge. */
  sameMembers(lhs: Node, rhs: Node, combiner: Combiner): boolean {
    if (lhs === rhs) {
      return true;
    }

    const members = (node: Node): Node[] => {
      const sorted = this.leaves(node, combiner).sort((a, b) => a.id - b.id);

      return combiner.idempotent ? distinct(sorted) : sorted;
    };
    const left = members(lhs);
    const right = members(rhs);

    return (
      left.length === right.length &&
      left.every((member, at) => member === right[at])
    );
  }

  /**
   * `normalizeStructural`: one pass over a bag whose arguments are
   * normal. Members fold into the def members they are alike to, and the
   * bag is rewritten with them.
   */
  private structural(bag: Node, combiner: Combiner): Node {
    return this.rewriteLeaves(
      bag,
      combiner,
      this.absorbed(this.leaves(bag, combiner), combiner),
    );
  }

  /**
   * `applySameSideAbsorption`: each member but the unit folded into the
   * least def member of the bag that it is alike to through their defs (a
   * def member) or that covers it (a member holding no def). A def member
   * folds only into a lesser one.
   */
  private absorbed(leaves: readonly Node[], combiner: Combiner): Node[] {
    const owners = distinct(
      leaves
        .filter((leaf) => this.isDefBearing(leaf))
        .sort((a, b) => this.compare(a, b)),
    );

    return leaves.map((leaf) => {
      if (owners.length === 0 || this.isUnit(leaf, combiner)) {
        return leaf;
      }

      const isDef = this.isDefBearing(leaf);

      for (const owner of owners) {
        if (owner === leaf) {
          break;
        }

        if (
          isDef
            ? this.absorber.alike(leaf, owner)
            : this.absorber.covers(owner, leaf, combiner)
        ) {
          return owner;
        }
      }

      return leaf;
    });
  }

  /**
   * `buildAcuiRewriteConversion`: the bag with its leaves, left to right,
   * replaced by `leaves`, its two parts normalized, and the result merged
   * into its canonical form ({@link exact}).
   */
  rewriteLeaves(
    node: Node,
    combiner: Combiner,
    leaves: readonly Node[],
  ): Node {
    let next = 0;
    const replace = (at: Node): Node => {
      if (!this.isBag(at, combiner)) {
        next += 1;
        return leaves[next - 1] as Node;
      }

      const rebuilt = this.withArgs(at, [
        replace(at.args[0] as Node),
        replace(at.args[1] as Node),
      ]);

      this.congruence(at, rebuilt);
      return rebuilt;
    };
    const replaced = replace(node);
    const rewritten = this.withArgs(
      replaced,
      replaced.args.map((arg) => this.proved(arg)),
    );

    this.congruence(replaced, rewritten);
    return this.exact(rewritten, combiner);
  }

  /**
   * `normalizeStructuralExact`: a bag merged member by member into its
   * canonical form, which takes it there where its right part is
   * canonical already. Anything else is left as it is.
   */
  exact(node: Node, combiner: Combiner): Node {
    return this.isBag(node, combiner)
      ? this.merge(node, node.args[0] as Node, node.args[1] as Node, combiner)
      : node;
  }

  private join(combiner: Combiner, left: Node, right: Node): Node {
    return this.app(combiner.term, combiner.sort, [left, right]);
  }

  /**
   * `mergeCanonical`: `current`, which is `left ; right` with `right`
   * canonical, as one canonical bag. A bag on the left is reassociated
   * and its parts merged in from the last.
   */
  private merge(
    current: Node,
    left: Node,
    right: Node,
    combiner: Combiner,
  ): Node {
    if (combiner.leftUnit && this.isUnit(left, combiner)) {
      return right;
    }

    if (!this.isBag(left, combiner)) {
      return this.insert(current, left, right, combiner);
    }

    const [first, rest] = left.args as [Node, Node];
    const tail = this.join(combiner, rest, right);
    const merged = this.merge(tail, rest, right, combiner);
    const afterTail = this.join(combiner, first, merged);

    this.congruence(this.join(combiner, first, tail), afterTail);
    return this.insert(afterTail, first, merged, combiner);
  }

  /**
   * `insertItem`: `current`, which is `item ; canon` with `canon`
   * canonical, with `item` moved to its place. A step inside `canon` is
   * lifted through the combiner's congruence; a unit law, or a step
   * against a single member, needs none.
   */
  private insert(
    current: Node,
    item: Node,
    canon: Node,
    combiner: Combiner,
  ): Node {
    if (combiner.leftUnit && this.isUnit(item, combiner)) {
      return canon;
    }

    if (combiner.rightUnit && this.isUnit(canon, combiner)) {
      return item;
    }

    if (!this.isBag(canon, combiner)) {
      // `insertIntoAtom`.
      const order = this.compare(item, canon);

      if (order === 0 && combiner.idempotent) {
        return canon;
      }

      return order > 0 && combiner.commutative
        ? this.join(combiner, canon, item)
        : current;
    }

    const [head, rest] = canon.args as [Node, Node];
    const order = this.compare(item, head);

    if (order === 0 && combiner.idempotent) {
      this.congruence(
        this.join(combiner, this.join(combiner, item, head), rest),
        this.join(combiner, item, rest),
      );
      return canon;
    }

    if (order <= 0 || !combiner.commutative) {
      return current;
    }

    this.congruence(
      this.join(combiner, this.join(combiner, item, head), rest),
      this.join(combiner, this.join(combiner, head, item), rest),
    );

    const before = this.join(combiner, item, rest);
    const placed = this.insert(before, item, rest, combiner);

    this.congruence(
      this.join(combiner, head, before),
      this.join(combiner, head, placed),
    );
    return this.join(combiner, head, placed);
  }

  /** `members` as one term: the unit when there are none, nested to the right. */
  private build(members: readonly Node[], combiner: Combiner): Node {
    if (members.length === 0) {
      return this.app(combiner.unit, combiner.sort, []);
    }

    let result = members[members.length - 1] as Node;

    for (let at = members.length - 2; at >= 0; at -= 1) {
      result = this.app(combiner.term, combiner.sort, [
        members[at] as Node,
        result,
      ]);
    }

    return result;
  }

  compare(a: Node, b: Node): number {
    if (a === b) {
      return 0;
    }

    if (a.term === null || b.term === null) {
      if (a.term !== null) {
        return 1;
      }

      if (b.term !== null) {
        return -1;
      }

      const order =
        (this.variableOrder.get(a.name) ?? Number.MAX_SAFE_INTEGER) -
        (this.variableOrder.get(b.name) ?? Number.MAX_SAFE_INTEGER);

      return order !== 0 ? order : a.name < b.name ? -1 : 1;
    }

    const order =
      (this.termOrder.get(a.term) ?? Number.MAX_SAFE_INTEGER) -
      (this.termOrder.get(b.term) ?? Number.MAX_SAFE_INTEGER);

    if (order !== 0) {
      return order;
    }

    // Constructors the spec does not declare, as in hand-built terms.
    if (a.term !== b.term) {
      return a.term < b.term ? -1 : 1;
    }

    if (a.args.length !== b.args.length) {
      return a.args.length - b.args.length;
    }

    for (const [at, arg] of a.args.entries()) {
      const order = this.compare(arg, b.args[at] as Node);

      if (order !== 0) {
        return order;
      }
    }

    return 0;
  }

  // ## Defs

  /** Whether `node` is headed by a def, with a definiens or without. */
  isDefApp(node: Node): boolean {
    return (
      node.term !== null &&
      this.lang.spec.terms.get(node.term)?.isDef === true
    );
  }

  /** Whether a def with a definiens heads `node` or any term inside it. */
  isDefBearing(node: Node): boolean {
    let found = this.defBearing.get(node.id);

    if (found === undefined) {
      found =
        (node.term !== null &&
          hasDefiniens(this.lang.spec.terms.get(node.term))) ||
        node.args.some((arg) => this.isDefBearing(arg));
      this.defBearing.set(node.id, found);
    }

    return found;
  }

  /**
   * `head_class.classify`: how conversion can change an application of
   * `term`. A `@rewrite` head can reduce to another; a combiner's
   * arguments can move; a def with a definiens unfolds; anything else is
   * rigid.
   */
  headClass(term: string): "rigid" | "def" | "acui" | "rewrite" | "unknown" {
    const info = this.lang.spec.terms.get(term);

    if (info === undefined) {
      return "unknown";
    }

    if (this.rewrites.has(term)) {
      return "rewrite";
    }

    if (info.acui !== null) {
      return "acui";
    }

    return hasDefiniens(info) ? "def" : "rigid";
  }

  /** The sort a term's applications have. */
  returnSort(term: string): string {
    return this.lang.spec.terms.get(term)?.returnSort ?? "";
  }

  /**
   * A def's definiens with what fills it. Null for a term, or a def without
   * a definiens.
   */
  definitionOf(term: string): DefBody | null {
    let found = this.definitions.get(term);

    if (found === undefined) {
      found = this.readDefinition(term);
      this.definitions.set(term, found);
    }

    return found;
  }

  private readDefinition(term: string): DefBody | null {
    const info = this.lang.spec.terms.get(term);

    if (!hasDefiniens(info)) {
      return null;
    }

    const body = definiens(this.lang, term);

    return body === null
      ? null
      : {
          binders: info.binders.map((binder) => binder.name),
          body,
          dummies: info.definition.dummies.map((dummy) => ({
            name: dummy.name,
            sort: "sort" in dummy.type ? dummy.type.sort : "",
          })),
        };
  }

  /**
   * A def application's definiens over its arguments: the one unfolding a
   * def without dot-dummies has (`unfoldConcreteDef`). Null for anything
   * else.
   */
  unfold(node: Node): Node | null {
    const definition =
      node.term === null ? null : this.definitionOf(node.term);

    if (definition === null || definition.dummies.length > 0) {
      return null;
    }

    const values = new Map<string, Node>();

    definition.binders.forEach((name, at) => {
      const arg = node.args[at];

      if (arg !== undefined) {
        values.set(name, arg);
      }
    });

    return this.instantiate(definition.body, values);
  }
}
