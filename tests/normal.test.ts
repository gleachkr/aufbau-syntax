import { describe, expect, test } from "bun:test";
import type { AssertStatement, Term } from "../src/index";
import {
  normalTerm,
  parseSpec,
  RewriteLimitError,
  SurfaceLanguage,
  sameTerm,
  statementVariables,
  termKey,
  Unstatable,
} from "../src/index";
import { shape } from "./helpers/mm0-corpus";

/**
 * Normal forms and identity on small theories, one engine behaviour each.
 * `normal-engine.test.ts` checks the same functions against the compiler
 * on whole theories.
 */

function language(source: string): SurfaceLanguage {
  const { spec, diagnostics } = parseSpec(source);

  expect(diagnostics.filter((one) => one.severity === "error")).toEqual([]);

  return new SurfaceLanguage(spec);
}

const BASE = `delimiter $ ( ) $;
provable sort jdg;
--| @vars x y
sort var;
sort tm;
term v (x: var): tm;
coercion v: var > tm;
term a: tm;
term b: tm;
term f (t: tm): tm;
term g (t: tm): tm;
term h (t: tm): tm;
term sb {x: var} (t: tm x) (u: tm x): tm;
term teq (s t: tm): jdg;
--| @relation tm teq teq_refl teq_trans teq_sym _
axiom teq_refl (s: tm): $ teq s s $;
axiom teq_trans (s t u: tm): $ teq s t $ > $ teq t u $ > $ teq s u $;
axiom teq_sym (s t: tm): $ teq s t $ > $ teq t s $;
--| @congr
axiom f_congr (s t: tm): $ teq s t $ > $ teq (f s) (f t) $;
--| @congr
axiom g_congr (s t: tm): $ teq s t $ > $ teq (g s) (g t) $;
--| @congr
axiom sb_congr {x: var} (s t u w: tm x): $ teq s t $ > $ teq u w $ > $ teq (sb x s u) (sb x t w) $;
`;

const REWRITES = `${BASE}--| @rewrite
axiom f_a: $ teq (f a) b $;
--| @rewrite
axiom f_any (t: tm): $ teq (f t) (g t) $;
--| @rewrite
axiom sb_var {x: var} (t: tm x): $ teq (sb x t (v x)) t $;
--| @rewrite
axiom sb_irrel {x: var} (t: tm x) (u: tm): $ teq (sb x t u) u $;
--| @rewrite
axiom sb_f {x: var} (t: tm x) (u: tm x): $ teq (sb x t (f u)) (f (sb x t u)) $;
--| @rewrite
axiom g_h (t: tm): $ teq (g (h t)) t $;
def k (t: tm): tm = $ h t $;
def dbl (t: tm): tm = $ f (f t) $;
`;

function read(lang: SurfaceLanguage, text: string, sort = "tm"): Term {
  const result = lang.parse(text, { mode: "engine", sort });

  if (!result.ok) {
    throw new Error(`${text}: ${result.diagnostics[0]?.message}`);
  }

  return result.term;
}

function normal(lang: SurfaceLanguage, text: string, sort = "tm"): string {
  return shape(normalTerm(lang, read(lang, text, sort)));
}

function same(
  lang: SurfaceLanguage,
  left: string,
  right: string,
  sort = "tm",
): boolean {
  return sameTerm(lang, read(lang, left, sort), read(lang, right, sort));
}

describe("rewrites", () => {
  const lang = language(REWRITES);

  test("the first rule in declaration order fires, and its result is normalized again", () => {
    expect(normal(lang, "f a")).toBe("b");
    expect(normal(lang, "f b")).toBe("(g b)");
    expect(normal(lang, "f (f a)")).toBe("(g b)");
  });

  test("a rule fires only where its binders' dependencies allow", () => {
    // `sb_irrel`'s `u` may not mention `x`, bound occurrences included.
    expect(normal(lang, "sb x a (h b)")).toBe("(h b)");
    expect(normal(lang, "sb x a (v x)")).toBe("a");
    expect(normal(lang, "sb x a (h (v x))")).toBe("(sb x a (h (v x)))");
    // Children first: `f (v x)` is already `g (v x)` when `sb_f` could
    // have pushed the substitution into it.
    expect(normal(lang, "sb x a (f (v x))")).toBe("(sb x a (g (v x)))");
  });

  test("a rewrite cycle, and a runaway one, are refused as the engine refuses them", () => {
    const cycle = language(`${BASE}--| @rewrite
axiom f_g (t: tm): $ teq (f t) (g t) $;
--| @rewrite
axiom g_f (t: tm): $ teq (g t) (f t) $;
`);
    const runaway = language(`${BASE}--| @rewrite
axiom f_up (t: tm): $ teq (f t) (f (g t)) $;
`);

    expect(() => normalTerm(cycle, read(cycle, "f a"))).toThrow(
      RewriteLimitError,
    );
    expect(() => normalTerm(runaway, read(runaway, "f a"))).toThrow(
      /more than 1000 steps/,
    );
  });
});

describe("defs", () => {
  const lang = language(REWRITES);

  test("an opened def is normalized on its own", () => {
    // `dbl a` opens to `f (f a)`, whose own redexes fire.
    expect(same(lang, "dbl a", "g b")).toBe(true);
    // Folded, the normal form leaves it alone.
    expect(normal(lang, "dbl a")).toBe("(dbl a)");
  });

  test("nothing is rewritten across the edge of an opened def", () => {
    // `g (k a)` is `g (h a)` once `k` is opened, but `g_h` would need the
    // `g` outside the def and the `h` inside it, as the engine never sees.
    expect(same(lang, "g (h a)", "a")).toBe(true);
    expect(same(lang, "g (k a)", "a")).toBe(false);
    expect(same(lang, "g (k a)", "g (h a)")).toBe(true);
  });
});

describe("defs with dot-dummies", () => {
  const lang = language(`${BASE}def self {.x: var}: tm = $ sb x a (v x) $;
def under (t: tm) {.x: var}: tm = $ sb x t (v x) $;
def pair {.x .y: var}: tm = $ sb x (v y) (v x) $;
`);

  test("a dummy takes the variable the other side writes", () => {
    expect(same(lang, "self", "sb y a (v y)")).toBe(true);
    expect(same(lang, "sb y a (v y)", "self")).toBe(true);
    expect(same(lang, "self", "sb y a (v x)")).toBe(false);
  });

  test("not a variable the def's arguments use, which the unfolding would capture", () => {
    expect(same(lang, "under (v x)", "sb y (v x) (v y)")).toBe(true);
    expect(same(lang, "under (v y)", "sb y (v y) (v y)")).toBe(false);
  });

  test("and not one a sibling dummy has taken", () => {
    expect(same(lang, "pair", "sb x (v y) (v x)")).toBe(true);
    expect(same(lang, "pair", "sb x (v x) (v x)")).toBe(false);
  });
});

describe("steps the engine cannot state", () => {
  const lang = language(REWRITES);

  test("no rewrite inside a term with no @congr", () => {
    // `h` has no congruence, so `f a` cannot become `b` inside it.
    expect(normal(lang, "h (f a)")).toBe("(h b)");
    expect(same(lang, "h (f a)", "h b")).toBe(false);
    expect(termKey(lang, read(lang, "h (f a)")).startsWith("!")).toBe(true);
    // The same term written twice is still the same.
    expect(same(lang, "h (f a)", "h (f a)")).toBe(true);
  });

  test("no step a congruence's dependencies refuse", () => {
    const strict = language(
      REWRITES.replace(
        "axiom sb_congr {x: var} (s t u w: tm x)",
        "axiom sb_congr {x: var} (s t: tm) (u w: tm x)",
      ),
    );
    const left = "sb x (f (v x)) (h (v x))";
    const right = "sb x (g (v x)) (h (v x))";

    // `f (v x)` becomes `g (v x)` in the substituted slot. Lifting that
    // through `sb` binds `s` to a term mentioning `x`, which the strict
    // rule's `(s: tm)` refuses.
    expect(same(lang, left, right)).toBe(true);
    expect(same(strict, left, right)).toBe(false);
  });
});

const BAGS = `${BASE}sort ctx;
term emp: ctx;
term hyp (t: tm): ctx;
term join (c d: ctx): ctx;
term ceq (c d: ctx): jdg;
--| @relation ctx ceq ceq_refl ceq_trans ceq_sym _
axiom ceq_refl (c: ctx): $ ceq c c $;
axiom ceq_trans (c d e: ctx): $ ceq c d $ > $ ceq d e $ > $ ceq c e $;
axiom ceq_sym (c d: ctx): $ ceq c d $ > $ ceq d c $;
--| @congr
axiom hyp_congr (s t: tm): $ teq s t $ > $ ceq (hyp s) (hyp t) $;
--| @congr
axiom join_congr (c d e w: ctx): $ ceq c d $ > $ ceq e w $ > $ ceq (join c e) (join d w) $;
axiom join_assoc (c d e: ctx): $ ceq (join (join c d) e) (join c (join d e)) $;
axiom join_comm (c d: ctx): $ ceq (join c d) (join d c) $;
axiom join_idem (c: ctx): $ ceq (join c c) c $;
`;

function bags(acui: string, extra = "", base = BAGS): SurfaceLanguage {
  return language(
    base.replace(
      "term join (c d: ctx): ctx;",
      `${acui}\nterm join (c d: ctx): ctx;`,
    ) + extra,
  );
}

describe("@acui bags", () => {
  test("a commutative bag is its members, in any order and grouping", () => {
    const lang = bags("--| @acui join_assoc join_comm emp _");

    expect(
      same(
        lang,
        "join (hyp b) (join (hyp a) (hyp b))",
        "join (join (hyp b) (hyp b)) (hyp a)",
        "ctx",
      ),
    ).toBe(true);
    // Not idempotent: a repeated member counts.
    expect(same(lang, "join (hyp a) (hyp a)", "hyp a", "ctx")).toBe(false);
    // Members are normalized first.
    expect(
      same(lang, "join (hyp (f a)) (hyp a)", "join (hyp a) (hyp b)", "ctx"),
    ).toBe(false);
  });

  test("an idempotent bag holds each member once", () => {
    const lang = bags("--| @acui join_assoc join_comm emp join_idem");

    expect(
      same(
        lang,
        "join (hyp a) (join (hyp b) (hyp a))",
        "join (hyp b) (hyp a)",
        "ctx",
      ),
    ).toBe(true);
  });

  test("the unit drops only where a declared rule of unit-law shape allows", () => {
    const without = bags("--| @acui join_assoc join_comm emp _");
    const withLaw = bags(
      "--| @acui join_assoc join_comm emp _",
      "axiom join_emp (c: ctx): $ ceq (join emp c) c $;\n",
    );

    expect(same(without, "join emp (hyp a)", "hyp a", "ctx")).toBe(false);
    // One side's law and commutativity drop it on either side.
    expect(same(withLaw, "join emp (hyp a)", "hyp a", "ctx")).toBe(true);
    expect(same(withLaw, "join (hyp a) emp", "hyp a", "ctx")).toBe(true);
  });

  test("a bag that does not commute keeps its order, and each unit law its side", () => {
    const lang = bags(
      "--| @acui join_assoc _ emp _",
      "axiom join_emp (c: ctx): $ ceq (join emp c) c $;\n",
    );

    expect(
      same(
        lang,
        "join (join (hyp a) (hyp b)) (hyp a)",
        "join (hyp a) (join (hyp b) (hyp a))",
        "ctx",
      ),
    ).toBe(true);
    expect(
      same(lang, "join (hyp a) (hyp b)", "join (hyp b) (hyp a)", "ctx"),
    ).toBe(false);
    expect(same(lang, "join emp (hyp a)", "hyp a", "ctx")).toBe(true);
    expect(same(lang, "join (hyp a) emp", "hyp a", "ctx")).toBe(false);
  });

  test("a member folds into a def member of its bag that covers it", () => {
    const lang = bags(
      "--| @acui join_assoc join_comm emp join_idem",
      `def dh (t: tm): ctx = $ hyp t $;
term fc (c: ctx): ctx;
--| @congr
axiom fc_congr (c d: ctx): $ ceq c d $ > $ ceq (fc c) (fc d) $;
--| @rewrite
axiom fc_dh (t: tm): $ ceq (fc (dh t)) emp $;
`,
    );

    // `hyp a` folds into `dh a`, the two merge, and the rewrite fires.
    expect(normal(lang, "fc (join (hyp a) (dh a))", "ctx")).toBe("emp");
    expect(same(lang, "fc (join (hyp a) (dh a))", "emp", "ctx")).toBe(true);
    expect(same(lang, "emp", "fc (join (hyp a) (dh a))", "ctx")).toBe(true);
  });

  test("without the combiner's @congr, only steps inside a bag go unstated", () => {
    const lang = bags(
      "--| @acui join_assoc join_comm emp join_idem",
      "axiom join_emp (c: ctx): $ ceq (join emp c) c $;\n",
      BAGS.replace("--| @congr\naxiom join_congr", "axiom join_congr"),
    );

    // A unit law, or a merge or swap against a single member, needs no
    // congruence.
    expect(same(lang, "join (hyp a) (hyp a)", "hyp a", "ctx")).toBe(true);
    expect(same(lang, "join emp (hyp a)", "hyp a", "ctx")).toBe(true);
    expect(
      same(lang, "join (hyp b) (hyp a)", "join (hyp a) (hyp b)", "ctx"),
    ).toBe(true);
    // A step inside the rest of a bag does.
    expect(
      same(
        lang,
        "join (hyp a) (join (hyp b) (hyp a))",
        "join (hyp a) (hyp b)",
        "ctx",
      ),
    ).toBe(false);
  });
});

const RING = `delimiter $ ( ) $;
provable sort wff;
sort R;
term bi (a b: wff): wff;
infixl bi: $<->$ prec 20;
term eq (a b: R): wff;
infixl eq: $=$ prec 50;
term zero: R;
term one: R;
--| @acui add_assoc add_comm zero _
term add (a b: R): R;
infixl add: $+$ prec 64;
--| @acui mul_assoc mul_comm one _
term mul (a b: R): R;
infixl mul: $*$ prec 70;
--| @relation wff bi bi_refl bi_trans bi_symm mpbi
axiom bi_refl (a: wff): $ a <-> a $;
axiom bi_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
axiom bi_symm (a b: wff): $ a <-> b $ > $ b <-> a $;
axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
--| @relation R eq eq_refl eq_trans eq_symm _
axiom eq_refl (a: R): $ a = a $;
axiom eq_trans (a b c: R): $ a = b $ > $ b = c $ > $ a = c $;
axiom eq_symm (a b: R): $ a = b $ > $ b = a $;
--| @congr
axiom add_congr (a b c d: R): $ a = b $ > $ c = d $ > $ a + c = b + d $;
--| @congr
axiom mul_congr (a b c d: R): $ a = b $ > $ c = d $ > $ a * c = b * d $;
axiom add_assoc (a b c: R): $ (a + b) + c = a + (b + c) $;
axiom add_comm (a b: R): $ a + b = b + a $;
axiom mul_assoc (a b c: R): $ (a * b) * c = a * (b * c) $;
axiom mul_comm (a b: R): $ a * b = b * a $;
def three: R = $ one + one + one $;
`;

describe("common targets", () => {
  const lang = language(RING);
  const flat = "one + one + one + one + one + one";

  test("a def member of a bag opens into the bag", () => {
    expect(same(lang, "three + three", flat, "R")).toBe(true);
  });

  test("and inside a member of a bag of another combiner", () => {
    // Members of the product that are sums still meet as bags of `+`.
    expect(
      same(lang, "(three + three) * zero", `(${flat}) * zero`, "R"),
    ).toBe(true);
    expect(
      same(
        lang,
        "(three + one) * zero",
        "(one + one + one + one) * zero",
        "R",
      ),
    ).toBe(true);
  });
});

const CUPS = `delimiter $ ( ) $;
sort s;
provable sort p;
term eq (a b: s): p;
term emp: s;
--| @acui cup_assoc cup_comm emp cup_idem
term cup (a b: s): s;
term g (a b: s): s;
term h (a: s): s;
term k: s;
term x: s;
term y: s;
def d: s = $ cup k emp $;
--| @relation s eq refl trans sym _
axiom refl (a: s): $ eq a a $;
axiom trans (a b c: s): $ eq a b $ > $ eq b c $ > $ eq a c $;
axiom sym (a b: s): $ eq a b $ > $ eq b a $;
axiom cup_assoc (a b c: s): $ eq (cup (cup a b) c) (cup a (cup b c)) $;
axiom cup_comm (a b: s): $ eq (cup a b) (cup b a) $;
axiom cup_idem (a: s): $ eq (cup a a) a $;
axiom cup_unit (a: s): $ eq (cup emp a) a $;
--| @congr
axiom cup_congr (a b c e: s): $ eq a b $ > $ eq c e $ > $ eq (cup a c) (cup b e) $;
--| @congr
axiom g_congr (a b c e: s): $ eq a b $ > $ eq c e $ > $ eq (g a c) (g b e) $;
`;

describe("absorption's edges", () => {
  test("a cover that fails still needs the steps it tried", () => {
    // Trying to cover `g (h k) y` by `g (h d) x` lifts a step through
    // `h`, which has no @congr, before `x` and `y` refuse the cover.
    // The engine's normalizer throws there, so no rung normalizes.
    const without = language(CUPS);
    const withH = language(
      `${CUPS}--| @congr
axiom h_congr (a b: s): $ eq a b $ > $ eq (h a) (h b) $;
`,
    );
    const left = "cup (g (h d) x) (g (h k) y)";
    const right = "cup (g (h d) x) (cup (g (h k) y) emp)";

    expect(same(without, left, right, "s")).toBe(false);
    expect(same(without, right, left, "s")).toBe(false);
    expect(same(withH, left, right, "s")).toBe(true);
  });

  test("a dot-dummy a cover leaves without a witness ends the normal form", () => {
    const lang = language(`delimiter $ ( ) $;
sort s;
sort v;
provable sort p;
term eq (a b: s): p;
term emp: s;
--| @acui cup_assoc cup_comm emp cup_idem
term cup (a b: s): s;
term k: s;
term m: s;
term q {z: v}: s;
def dd (a: s) (.z: v): s = $ cup a (q z) $;
term r (a: s): s;
--| @relation s eq refl trans sym _
axiom refl (a: s): $ eq a a $;
axiom trans (a b c: s): $ eq a b $ > $ eq b c $ > $ eq a c $;
axiom sym (a b: s): $ eq a b $ > $ eq b a $;
axiom cup_assoc (a b c: s): $ eq (cup (cup a b) c) (cup a (cup b c)) $;
axiom cup_comm (a b: s): $ eq (cup a b) (cup b a) $;
axiom cup_idem (a: s): $ eq (cup a a) a $;
axiom cup_unit (a: s): $ eq (cup emp a) a $;
--| @congr
axiom cup_congr (a b c e: s): $ eq a b $ > $ eq c e $ > $ eq (cup a c) (cup b e) $;
--| @congr
axiom r_congr (a b: s): $ eq a b $ > $ eq (r a) (r b) $;
--| @rewrite
axiom r_def (a: s): $ eq (r a) (cup (dd a) a) $;
`);
    const term = read(lang, "r k", "s");

    expect(() => normalTerm(lang, term)).toThrow(Unstatable);
    expect(termKey(lang, term).startsWith("!")).toBe(true);
    // The engine's `mayMeet` lets the rungs try, and each fails.
    expect(same(lang, "r k", "m", "s")).toBe(false);
  });
});

describe("the step limit", () => {
  const lang = language(`delimiter $ ( ) $;
provable sort wff;
sort nat;
term z: nat;
term s (n: nat): nat;
term add (a b: nat): nat;
term neq (a b: nat): wff;
--| @relation nat neq neq_refl neq_trans neq_sym _
axiom neq_refl (a: nat): $ neq a a $;
axiom neq_trans (a b c: nat): $ neq a b $ > $ neq b c $ > $ neq a c $;
axiom neq_sym (a b: nat): $ neq a b $ > $ neq b a $;
--| @congr
axiom s_congr (a b: nat): $ neq a b $ > $ neq (s a) (s b) $;
--| @congr
axiom add_congr (a b c d: nat): $ neq a b $ > $ neq c d $ > $ neq (add a c) (add b d) $;
--| @rewrite
axiom add_z (b: nat): $ neq (add z b) b $;
--| @rewrite
axiom add_s (a b: nat): $ neq (add (s a) b) (s (add a b)) $;
`);
  const numeral = (n: number): string =>
    `${"(s ".repeat(n)}z${")".repeat(n)}`;
  const pair = (n: number): [string, string] => [
    `add ${numeral(n)} z`,
    `add ${numeral(n - 1)} (s z)`,
  ];

  test("counts both sides of a line, as the engine's one normalizer does", () => {
    // About 400 steps a side passes; about 500 does not, though each side
    // alone stays under the thousand.
    expect(same(lang, ...pair(401), "nat")).toBe(true);
    expect(() => same(lang, ...pair(501), "nat")).toThrow(RewriteLimitError);
  });
});

describe("termKey", () => {
  test("keys a variable apart from a constant of its name", () => {
    const lang = language(REWRITES);
    const variable: Term = {
      binder: false,
      grouped: false,
      kind: "variable",
      name: "a",
      sort: "tm",
      span: { end: 0, start: 0 },
    };
    const variables = new Map([
      ["a", { bound: false, dependencies: [], sort: "tm" }],
    ]);
    const constant = read(lang, "a");

    expect(termKey(lang, variable, { variables })).not.toBe(
      termKey(lang, constant, { variables }),
    );
    expect(sameTerm(lang, variable, constant, { variables })).toBe(false);
  });
});

describe("statementVariables", () => {
  test("a statement's binders, bound or with their dependencies", () => {
    const lang = language(REWRITES);
    const statement = lang.spec.statements.find(
      (one): one is AssertStatement =>
        one.kind === "axiom" && one.name === "sb_irrel",
    );

    expect(statement && [...statementVariables(statement)]).toEqual([
      ["x", { bound: true, dependencies: [], sort: "var" }],
      ["t", { bound: false, dependencies: ["x"], sort: "tm" }],
      ["u", { bound: false, dependencies: [], sort: "tm" }],
    ]);
  });
});
