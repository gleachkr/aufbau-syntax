import { describe, expect, test } from "bun:test";
import { readFile } from "node:fs/promises";
import type { AssertStatement } from "../src/index";
import { parseSpec } from "../src/index";

const zachPath = new URL("./fixtures/zach.mm0", import.meta.url).pathname;

/** Diagnostic ids only — the assertion shape used all over this file. */
function ids(result: ReturnType<typeof parseSpec>): string[] {
  return result.diagnostics.map((d) => d.id);
}

describe("reading a real theory", () => {
  test("zach.mm0 reads clean and complete", async () => {
    const source = await readFile(zachPath, "utf8");
    const { spec, diagnostics } = parseSpec(source);

    expect(diagnostics).toEqual([]);

    expect([...spec.sorts.keys()].sort()).toEqual([
      "ctx",
      "name",
      "seq",
      "tm",
      "var",
      "wff",
    ]);
    expect(spec.terms.size).toBe(22);
    expect(spec.coercions.map((c) => c.name).sort()).toEqual([
      "hyp",
      "n2t",
      "t2s",
      "v2t",
    ]);
    expect(spec.notations).toHaveLength(12);
    expect([...spec.delimiters.left].sort()).toEqual(
      ["(", ")", ",", "/", ";", "[", "]"].sort(),
    );

    // The sequent turnstile: infixl nd: $⊢$ prec 0.
    const nd = spec.notations.find(
      (n) => n.form === "simple" && n.term === "nd",
    );
    expect(nd).toMatchObject({ fixity: "infixl", prec: 0, token: "⊢" });

    // The substitution mixfix keeps its literal shape.
    const sbf = spec.notations.find(
      (n) => n.form === "general" && n.term === "sb_f",
    );
    expect(sbf?.form === "general" && sbf.literals[0]).toMatchObject({
      kind: "constant",
      token: "[",
      prec: 41,
    });

    // A quantifier's binder structure survives: {x: var} (p: wff x).
    const all = spec.terms.get("all");
    expect(all?.binders).toHaveLength(2);
    expect(all?.binders[0]).toMatchObject({ binds: true, name: "x" });
    expect(all?.binders[1]?.type).toMatchObject({
      sort: "wff",
      dependencies: ["x"],
    });

    // Foreign annotations pass through where they were written.
    const scomma = spec.terms.get("scomma");
    expect(scomma?.foreignAnnotations.map((a) => a.text)).toEqual([
      "@acui seq_assoc _ snil _",
    ]);
    expect(
      spec.sorts.get("var")?.foreignAnnotations.map((a) => a.text),
    ).toEqual(["@vars x y z"]);

    // …and `@vars` is *also* read: the engine's variable pools are the
    // surface lexicon's variables.
    expect(spec.sorts.get("var")?.vars).toEqual(["x", "y", "z"]);
    expect(spec.sorts.get("name")?.vars).toEqual(["a", "b", "c", "d"]);

    // Axioms and theorems ride along opaque, annotations intact.
    const axioms = spec.statements.filter(
      (s): s is AssertStatement => s.kind === "axiom",
    );
    expect(axioms.length).toBeGreaterThan(20);
    const allIntro = axioms.find((s) => s.name === "all_intro");
    expect(allIntro?.annotations.map((a) => a.text.split(" ")[0])).toEqual([
      "@view",
      "@recover",
    ]);
  });
});

describe("@syntax annotations", () => {
  const CALGARYISH = `
delimiter $ ( ) $;
provable sort wff;
--| @vars x y z
sort var;
--| @vars a b c d e
sort name;
sort tm;
sort seq;
term v2t (x: var): tm;
coercion v2t: var > tm;
term t2s (t: tm): seq;
coercion t2s: tm > seq;
term n2t (a: name): tm;
coercion n2t: name > tm;
--| @syntax elided
term snil: seq;
--| @syntax juxtaposed
term scomma (s t: seq): seq;
infixl scomma: $,$ prec 10;
--| @syntax role predicate
term F (s: seq): wff;
term G (s: seq): wff;
--| @syntax role conditional
--| @syntax forbid chain nest
term imp (p q: wff): wff;
infixr imp: $->$ prec 25;
infixr imp: $→$ prec 25;
term and (p q: wff): wff;
infixl and: $/\\$ prec 30;
infixl and: $∧$ prec 30;
--| @syntax brackets ( ) [ ]
--| @syntax lint parenthesize-binary-only
--| @syntax lint closed-sentences
--| @syntax display drop-outer-parens
--| @syntax elab $ ?F:wff ?ts:tm+ $ => $ ?F ( ?ts,* ) $
term all {x: var} (p: wff x): wff;
prefix all: $∀$ prec 46;
`;

  test("a spec fragment carries every axis", () => {
    const { spec, diagnostics } = parseSpec(CALGARYISH);

    expect(diagnostics).toEqual([]);

    // The lexicon: `@vars` pools on the sorts, ordinary declarations for
    // the letters, and the two per-term flags.
    expect(spec.sorts.get("var")?.vars).toEqual(["x", "y", "z"]);
    expect(spec.sorts.get("name")?.vars).toEqual(["a", "b", "c", "d", "e"]);
    expect(spec.terms.get("snil")).toMatchObject({
      elided: true,
      juxtaposed: false,
    });
    expect(spec.terms.get("scomma")).toMatchObject({
      elided: false,
      juxtaposed: true,
    });
    expect(spec.terms.get("F")?.returnSort).toBe("wff");

    expect(spec.groupingPairs).toEqual([
      ["(", ")"],
      ["[", "]"],
    ]);
    // The refusal flags ride onto their term, one relation each.
    expect([...(spec.terms.get("imp")?.refuses ?? [])].sort()).toEqual([
      "chain",
      "nest",
    ]);
    expect(spec.terms.get("and")?.refuses.size ?? 0).toBe(0);
    expect(spec.lints).toEqual([
      "parenthesize-binary-only",
      "closed-sentences",
    ]);
    expect(spec.display.dropOuterParens).toBe(true);
    expect(spec.display.rotateBrackets).toBeNull();

    // The role rode the annotation onto its term.
    expect(spec.terms.get("imp")?.roles).toEqual(["conditional"]);
    expect(spec.terms.get("F")?.roles).toEqual(["predicate"]);

    // Alias spellings are plain repeated notations; order is declaration
    // order, so the printer's canonical pick (last) is the Unicode one.
    const imps = spec.notations.filter((n) => n.term === "imp");
    expect(imps.map((n) => (n.form === "simple" ? n.token : ""))).toEqual([
      "->",
      "→",
    ]);

    // The elab rule parsed structurally.
    expect(spec.elabRules).toHaveLength(1);
    expect(spec.elabRules[0]?.pattern).toEqual([
      { kind: "capture", name: "F", class: "wff", quantifier: "" },
      { kind: "capture", name: "ts", class: "tm", quantifier: "+" },
    ]);
    expect(spec.elabRules[0]?.template).toEqual([
      { kind: "reference", name: "F", separator: null },
      { kind: "literal", token: "(" },
      { kind: "reference", name: "ts", separator: "," },
      { kind: "literal", token: ")" },
    ]);
    expect(spec.elabRules[0]?.inputOnly).toBe(false);
  });
});

describe("spec validation", () => {
  const WFF = "provable sort wff;\n";

  test("duplicate declarations are reported", () => {
    const result = parseSpec(`${WFF}sort wff;`);
    expect(ids(result)).toEqual(["duplicate_declaration"]);
  });

  test("an unknown sort in a term is reported", () => {
    const result = parseSpec(`${WFF}term p (a: gap): wff;`);
    expect(ids(result)).toEqual(["unknown_sort"]);
  });

  test("a notation for an undeclared term is reported", () => {
    const result = parseSpec(`${WFF}infixl ghost: $+$ prec 30;`);
    expect(ids(result)).toEqual(["unknown_term"]);
  });

  test("an infix notation on a non-binary term is reported", () => {
    const result = parseSpec(
      `${WFF}term neg (p: wff): wff;\ninfixl neg: $-$ prec 30;`,
    );
    expect(ids(result)).toEqual(["infix_arity"]);
  });

  test("one token cannot carry two precedences", () => {
    const result = parseSpec(
      `${WFF}term a (p q: wff): wff;\nterm b (p q: wff): wff;\n` +
        "infixl a: $+$ prec 30;\ninfixl b: $+$ prec 40;",
    );
    expect(ids(result)).toEqual(["token_conflict"]);
  });

  test("a precedence level cannot mix associativities", () => {
    const result = parseSpec(
      `${WFF}term a (p q: wff): wff;\nterm b (p q: wff): wff;\n` +
        "infixl a: $+$ prec 30;\ninfixr b: $*$ prec 30;",
    );
    expect(ids(result)).toEqual(["precedence_mixed_associativity"]);
  });

  test("a grouping bracket cannot also be a notation token", () => {
    const result = parseSpec(
      `${WFF}term box (p: wff): wff;\nprefix box: $[$ prec 40;\n` +
        "--| @syntax brackets [ ]\nsort other;",
    );
    expect(ids(result)).toEqual(["grouping_token_conflict"]);
  });

  test("elab rules must be invertible unless marked input-only", () => {
    const dropped = parseSpec(
      `${WFF}--| @syntax elab $ ?a:wff ?b:wff $ => $ ?a $\nsort s2;`,
    );
    expect(ids(dropped)).toEqual(["elab_not_invertible"]);

    const marked = parseSpec(
      `${WFF}--| @syntax elab $ ?a:wff ?b:wff $ => $ ?a $ input-only\nsort s2;`,
    );
    expect(ids(marked)).toEqual([]);

    const unknown = parseSpec(
      `${WFF}--| @syntax elab $ ?a:wff $ => $ ?a ?b $\nsort s2;`,
    );
    expect(ids(unknown)).toEqual(["elab_unknown_reference"]);

    const duplicated = parseSpec(
      `${WFF}--| @syntax elab $ ?a:wff ?a:wff $ => $ ?a $ input-only\nsort s2;`,
    );
    expect(ids(duplicated)).toEqual(["elab_duplicate_capture"]);
  });

  test("juxtaposed demands a binary homogeneous term with a notation", () => {
    const onSort = parseSpec(`--| @syntax juxtaposed\n${WFF}`);
    expect(ids(onSort)).toEqual(["juxtaposed_target"]);

    const onUnary = parseSpec(
      `${WFF}--| @syntax juxtaposed\nterm neg (p: wff): wff;`,
    );
    expect(ids(onUnary)).toEqual(["juxtaposed_target"]);

    const mixedSorts = parseSpec(
      `${WFF}sort tm;\n--| @syntax juxtaposed\nterm eq (s t: tm): wff;\ninfixl eq: $=$ prec 50;`,
    );
    expect(ids(mixedSorts)).toEqual(["juxtaposed_target"]);

    // No notation: the engine could never read what adjacency means.
    const unnotated = parseSpec(
      `${WFF}--| @syntax juxtaposed\nterm both (p q: wff): wff;`,
    );
    expect(ids(unnotated)).toEqual(["juxtaposed_needs_notation"]);

    const twice = parseSpec(
      `${WFF}--| @syntax juxtaposed\nterm a (p q: wff): wff;\ninfixl a: $+$ prec 30;\n` +
        "--| @syntax juxtaposed\nterm b (p q: wff): wff;\ninfixl b: $*$ prec 40;",
    );
    expect(ids(twice)).toEqual(["juxtaposed_duplicate"]);
  });

  test("elided demands a nullary term, one per sort", () => {
    const onUnary = parseSpec(
      `${WFF}--| @syntax elided\nterm neg (p: wff): wff;`,
    );
    expect(ids(onUnary)).toEqual(["elided_target"]);

    const twice = parseSpec(
      `${WFF}--| @syntax elided\nterm t1: wff;\n--| @syntax elided\nterm t2: wff;`,
    );
    expect(ids(twice)).toEqual(["elided_duplicate"]);
  });

  test("role annotations check their attachment", () => {
    const onAxiom = parseSpec(
      `${WFF}term t: wff;\n--| @syntax role sentence\naxiom ax: $ t $;`,
    );
    expect(ids(onAxiom)).toEqual(["role_target"]);
  });

  test("a role sits on a sort as readily as on a term, uninterpreted", () => {
    const { spec, diagnostics } = parseSpec(
      "--| @syntax role sentence\nsort wff;\n--| @syntax role falsum\nterm bot: wff;",
    );
    expect(diagnostics).toEqual([]);
    expect(spec.sorts.get("wff")?.roles).toEqual(["sentence"]);
    expect(spec.terms.get("bot")?.roles).toEqual(["falsum"]);
  });

  test("a @vars token cannot also be a declared term", () => {
    const conflict = parseSpec(`--| @vars a b\nsort wff;\nterm a: wff;`);
    expect(ids(conflict)).toEqual(["vars_term_conflict"]);
  });

  test("malformed @syntax lines name their problem", () => {
    expect(ids(parseSpec("--| @syntax banana\nsort wff;"))).toEqual([
      "syntax_unknown_subcommand",
    ]);
    expect(ids(parseSpec("--| @syntax lint tidy-desk\nsort wff;"))).toEqual([
      "syntax_unknown_lint",
    ]);
    expect(ids(parseSpec("--| @syntax elab nope\nsort wff;"))).toEqual([
      "syntax_bad_elab",
    ]);
    expect(ids(parseSpec("--| @syntax brackets (\nsort wff;"))).toEqual([
      "syntax_bad_brackets",
    ]);
    expect(ids(parseSpec("--| @syntax forbid\nsort wff;"))).toEqual([
      "syntax_bad_forbid",
    ]);
    expect(
      ids(parseSpec("--| @syntax forbid chain wobble\nsort wff;")),
    ).toEqual(["syntax_bad_forbid"]);
  });

  test("@syntax forbid must sit somewhere it can bite", () => {
    // A sort, a nullary term, an infix-less term: in each case there is no
    // operand for it to refuse, so it would read clean and quietly do
    // nothing. That silence is what the diagnostic is for.
    const connective =
      "provable sort wff;\nterm and (p q: wff): wff;\ninfixl and: $/\\$ prec 30;\n";

    expect(
      ids(parseSpec(`${connective}--| @syntax forbid chain\nsort other;`)),
    ).toEqual(["refusal_target"]);
    expect(
      ids(parseSpec(`${connective}--| @syntax forbid chain\nterm bot: wff;`)),
    ).toEqual(["refusal_target"]);
    expect(
      ids(
        parseSpec(
          `${connective}--| @syntax forbid chain\nterm nay (p q: wff): wff;`,
        ),
      ),
    ).toEqual(["refusal_target"]);

    // On a real infix connective it lands, and accumulates across lines.
    const { diagnostics, spec } = parseSpec(
      "provable sort wff;\n--| @syntax forbid chain\n--| @syntax forbid mix nest\nterm and (p q: wff): wff;\ninfixl and: $/\\$ prec 30;",
    );

    expect(diagnostics).toEqual([]);
    expect([...(spec.terms.get("and")?.refuses ?? [])].sort()).toEqual([
      "chain",
      "mix",
      "nest",
    ]);
  });

  test("engine limits are enforced on delimiters", () => {
    expect(ids(parseSpec("delimiter $ ( ) λ $;"))).toEqual([
      "multibyte_delimiter",
    ]);
  });

  test("a broken statement is skipped, not fatal", () => {
    const result = parseSpec(
      "term orphan (p: ): wff;\nprovable sort wff;\nsort tm;",
    );

    expect(result.diagnostics.length).toBeGreaterThan(0);
    expect([...result.spec.sorts.keys()].sort()).toEqual(["tm", "wff"]);
  });
});

describe("surface delimiters", () => {
  /**
   * Small but complete: an elided term whose name the letters would split
   * (`snil` against the `s n i l` variable pool), two letters, and operator
   * spellings of one, two, and three characters.
   */
  const BASE = `
delimiter $ ( ) $;
provable sort wff;
--| @vars s n i l
sort var;
sort tm;
sort seq;
term v2t (x: var): tm;
coercion v2t: var > tm;
term t2s (t: tm): seq;
coercion t2s: tm > seq;
--| @syntax elided
term snil: seq;
term F (s: seq): wff;
term G (s: seq): wff;
term not (p: wff): wff;
prefix not: $~$ prec 40;
term and (p q: wff): wff;
infixl and: $/\\$ prec 30;
infixl and: $∧$ prec 30;
`;

  /** Everything `BASE` declares, written out one entry at a time. */
  const FULL = "F G s n i l ( ) ~ /\\ ∧";

  const declaring = (entries: string) =>
    parseSpec(`--| @syntax delimiter $ ${entries} $\n${BASE}`);

  test("a spec that declares none is read under the theory's own set", () => {
    const { spec, diagnostics } = parseSpec(BASE);

    expect(diagnostics).toEqual([]);
    expect([...spec.surfaceDelimiters.left].sort()).toEqual(["(", ")"]);
    expect([...spec.surfaceDelimiters.right].sort()).toEqual(["(", ")"]);
  });

  test("a declaration unions with the theory's own delimiters", () => {
    const { spec, diagnostics } = declaring(FULL);

    expect(diagnostics).toEqual([]);

    // The theory's set is untouched — engine text still reads under it.
    expect([...spec.delimiters.left].sort()).toEqual(["(", ")"]);

    expect([...spec.surfaceDelimiters.left].sort()).toEqual(
      ["(", ")", "/\\", "F", "G", "i", "l", "n", "s", "~", "∧"].sort(),
    );
  });

  test("a surface delimiter may be a string, where the engine's cannot", () => {
    // `delimiter $ ∧ $;` is rejected as multibyte — the engine splits on
    // bytes. The surface set has no such limit.
    expect(ids(parseSpec("delimiter $ ∧ $;"))).toEqual([
      "multibyte_delimiter",
    ]);

    const { spec } = declaring(FULL);
    expect(spec.surfaceDelimiters.left.has("∧")).toBe(true);
    expect(spec.surfaceDelimiters.left.has("/\\")).toBe(true);
  });

  test("the two-list form splits left from right", () => {
    const { spec, diagnostics } = parseSpec(
      `--| @syntax delimiter $ F G s n i l ( ~ /\\ ∧ $ $ ) $\n${BASE}`,
    );

    expect(diagnostics).toEqual([]);
    expect(spec.surfaceDelimiters.left.has(")")).toBe(true); // from the statement
    expect(spec.surfaceDelimiters.right.has("~")).toBe(false);
    expect(spec.surfaceDelimiters.right.has(")")).toBe(true);
  });

  test("malformed declarations name their problem", () => {
    expect(ids(parseSpec(`--| @syntax delimiter F G\n${BASE}`))).toEqual([
      "syntax_bad_delimiter",
    ]);
    expect(ids(parseSpec(`--| @syntax delimiter $  $\n${BASE}`))).toEqual([
      "syntax_empty_delimiter",
    ]);
    expect(
      ids(parseSpec(`--| @syntax delimiter $ F $ $  $\n${BASE}`)),
    ).toEqual(["syntax_empty_delimiter"]);
  });

  test("a delimiter that names nothing is an error", () => {
    // Including a range shorthand written by an author who assumed one
    // exists: `A-Z` is a three-character delimiter, and nothing else.
    const result = declaring(`${FULL} FG A-Z`);

    expect(ids(result)).toEqual(["delimiter_unknown", "delimiter_unknown"]);
    expect(result.diagnostics.map((d) => d.params.token)).toEqual([
      "FG",
      "A-Z",
    ]);
  });

  test("a token left out of the declaration warns, and only warns", () => {
    const result = declaring("F G s n i l ( ) /\\ ∧");

    expect(result.diagnostics).toHaveLength(1);
    expect(result.diagnostics[0]).toMatchObject({
      id: "delimiter_token_not_delimited",
      params: { token: "~" },
      severity: "warning",
    });
  });

  test("a name the delimiters would split can never be read", () => {
    const result = parseSpec(
      `--| @syntax delimiter $ ${FULL} $\n${BASE}\nterm sn (s: seq): wff;\n`,
    );

    expect(ids(result)).toEqual(["delimiter_unreachable_name"]);
    expect(result.diagnostics[0]).toMatchObject({
      params: { chunks: "s n", name: "sn" },
      severity: "error",
    });
  });

  test("an elided term is exempt: nobody types it", () => {
    // `snil` splits into `s n i l` under the same declaration, and that is
    // fine — the parser supplies it and the printer drops it.
    expect(ids(declaring(FULL))).toEqual([]);
    expect(declaring(FULL).spec.terms.get("snil")?.elided).toBe(true);
  });

  test("nothing is checked until a spec opts in", () => {
    // No declaration, so no claim that input can be written tight — and no
    // complaint that `~` and `∧` are not delimiters, which they are not.
    expect(ids(parseSpec(`${BASE}\nterm sn (s: seq): wff;\n`))).toEqual([]);
  });
});
