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
--| @syntax family var x-z subscripts
sort var;
sort name;
sort tm;
sort seq;
term v2t (x: var): tm;
coercion v2t: var > tm;
term t2s (t: tm): seq;
coercion t2s: tm > seq;
--| @syntax family const a-e
term _const: name;
term n2t (a: name): tm;
coercion n2t: name > tm;
--| @syntax family pred F-H
--| @syntax role predicate
term _pred (s: seq): wff;
--| @syntax role conditional
term imp (p q: wff): wff;
infixr imp: $->$ prec 25;
infixr imp: $→$ prec 25;
term and (p q: wff): wff;
infixl and: $/\\$ prec 30;
infixl and: $∧$ prec 30;
--| @syntax brackets ( ) [ ]
--| @syntax assoc-none 25
--| @syntax lint parenthesize-binary-only
--| @syntax lint closed-sentences
--| @syntax display drop-outer-parens
--| @syntax rewrite $ ?F:pred ?ts:tm+ $ => $ ?F ( ?ts,* ) $
term all {x: var} (p: wff x): wff;
prefix all: $∀$ prec 46;
`;

  test("a spec fragment carries every axis", () => {
    const { spec, diagnostics } = parseSpec(CALGARYISH);

    expect(diagnostics).toEqual([]);

    expect(spec.families).toHaveLength(3);
    expect(spec.families[0]).toMatchObject({
      class: "var",
      subscripts: "underscore",
      target: { kind: "sort", sort: "var" },
    });
    expect([...(spec.families[0]?.letters ?? [])].sort()).toEqual([
      "x",
      "y",
      "z",
    ]);
    expect(spec.families[1]).toMatchObject({
      class: "const",
      subscripts: "none",
      target: { kind: "template", term: "_const" },
    });
    expect(spec.families[2]?.target).toEqual({
      kind: "template",
      term: "_pred",
    });

    expect(spec.groupingPairs).toEqual([
      ["(", ")"],
      ["[", "]"],
    ]);
    expect([...spec.assocNone]).toEqual([25]);
    expect(spec.lints).toEqual([
      "parenthesize-binary-only",
      "closed-sentences",
    ]);
    expect(spec.display.dropOuterParens).toBe(true);
    expect(spec.display.rotateBrackets).toBeNull();

    // The role rode the annotation onto its term.
    expect(spec.terms.get("imp")?.roles).toEqual(["conditional"]);
    expect(spec.terms.get("_pred")?.roles).toEqual(["predicate"]);

    // Alias spellings are plain repeated notations; order is declaration
    // order, so the printer's canonical pick (last) is the Unicode one.
    const imps = spec.notations.filter((n) => n.term === "imp");
    expect(imps.map((n) => (n.form === "simple" ? n.token : ""))).toEqual([
      "->",
      "→",
    ]);

    // The juxtaposition rule parsed structurally.
    expect(spec.rewrites).toHaveLength(1);
    expect(spec.rewrites[0]?.pattern).toEqual([
      { kind: "capture", name: "F", class: "pred", quantifier: "" },
      { kind: "capture", name: "ts", class: "tm", quantifier: "+" },
    ]);
    expect(spec.rewrites[0]?.template).toEqual([
      { kind: "reference", name: "F", separator: null },
      { kind: "literal", token: "(" },
      { kind: "reference", name: "ts", separator: "," },
      { kind: "literal", token: ")" },
    ]);
    expect(spec.rewrites[0]?.inputOnly).toBe(false);
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

  test("rewrite rules must be invertible unless marked input-only", () => {
    const dropped = parseSpec(
      `${WFF}--| @syntax rewrite $ ?a:wff ?b:wff $ => $ ?a $\nsort s2;`,
    );
    expect(ids(dropped)).toEqual(["rewrite_not_invertible"]);

    const marked = parseSpec(
      `${WFF}--| @syntax rewrite $ ?a:wff ?b:wff $ => $ ?a $ input-only\nsort s2;`,
    );
    expect(ids(marked)).toEqual([]);

    const unknown = parseSpec(
      `${WFF}--| @syntax rewrite $ ?a:wff $ => $ ?a ?b $\nsort s2;`,
    );
    expect(ids(unknown)).toEqual(["rewrite_unknown_reference"]);

    const duplicated = parseSpec(
      `${WFF}--| @syntax rewrite $ ?a:wff ?a:wff $ => $ ?a $ input-only\nsort s2;`,
    );
    expect(ids(duplicated)).toEqual(["rewrite_duplicate_capture"]);
  });

  test("family and role annotations check their attachment", () => {
    const onAxiom = parseSpec(
      `${WFF}--| @syntax family pred A-C\naxiom truth: $ t $;`,
    );
    expect(ids(onAxiom)).toEqual(["family_target"]);

    const roleOnSort = parseSpec("--| @syntax role conditional\nsort wff;");
    expect(ids(roleOnSort)).toEqual(["role_target"]);

    const twice = parseSpec(
      `--| @syntax family v a-c\nsort wff;\n--| @syntax family v d-f\nsort tm;`,
    );
    expect(ids(twice)).toEqual(["duplicate_family_class"]);
  });

  test("malformed @syntax lines name their problem", () => {
    expect(ids(parseSpec("--| @syntax banana\nsort wff;"))).toEqual([
      "syntax_unknown_subcommand",
    ]);
    expect(ids(parseSpec("--| @syntax lint tidy-desk\nsort wff;"))).toEqual([
      "syntax_unknown_lint",
    ]);
    expect(ids(parseSpec("--| @syntax rewrite nope\nsort wff;"))).toEqual([
      "syntax_bad_rewrite",
    ]);
    expect(ids(parseSpec("--| @syntax brackets (\nsort wff;"))).toEqual([
      "syntax_bad_brackets",
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
