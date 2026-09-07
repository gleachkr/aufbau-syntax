import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import type {
  Binder,
  MathString,
  ParseResult,
  Spec,
  SurfaceLanguage,
  Term,
} from "../../src/index";
import { printTerm } from "../../src/index";

/**
 * The MM0 corpus under `tests/fixtures/mm0/`: reference files from the
 * upstream MM0 examples and from the Aufbau repository, read whole.
 * `tests/fixtures/mm0/README.md` says where each comes from.
 */
export const CORPUS_DIR = join(import.meta.dir, "..", "fixtures", "mm0");

export function corpusFiles(): readonly string[] {
  return readdirSync(CORPUS_DIR)
    .filter((name) => name.endsWith(".mm0"))
    .sort();
}

export function corpusSource(name: string): string {
  return readFileSync(join(CORPUS_DIR, name), "utf8");
}

/** One math string a file states, with what it takes to read it. */
export interface CorpusFormula {
  /** The declaring statement's name. */
  readonly statement: string;
  readonly role: "binder" | "conclusion" | "definiens" | "hypothesis";
  readonly math: MathString;
  /** The statement's binders, name to sort — the parse's `scope`. */
  readonly scope: ReadonlyMap<string, string>;
  /** The sorts the string may have; a hypothesis is any provable one. */
  readonly sorts: readonly string[];
}

function scopeOf(binders: readonly Binder[]): Map<string, string> {
  const scope = new Map<string, string>();

  for (const binder of binders) {
    if ("sort" in binder.type && binder.name !== "_") {
      scope.set(binder.name, binder.type.sort);
    }
  }

  return scope;
}

/**
 * Every math string in the file's assertions and definitions. mm0.md:
 * "All formulas appearing in axioms and theorems (between `$`) must have
 * a provable sort", so those are tried at each provable sort (or, in a
 * file that marks none, at every sort); a definiens is at the def's own
 * return sort. `input`/`output` items are the verifier's and are not
 * read.
 */
export function corpusFormulas(spec: Spec): readonly CorpusFormula[] {
  const provable = [...spec.sorts.values()]
    .filter((sort) => sort.modifiers.includes("provable"))
    .map((sort) => sort.name);
  const assertable = provable.length > 0 ? provable : [...spec.sorts.keys()];
  const formulas: CorpusFormula[] = [];

  for (const statement of spec.statements) {
    if (statement.kind === "axiom" || statement.kind === "theorem") {
      const scope = scopeOf(statement.binders);
      const base = { statement: statement.name, scope, sorts: assertable };

      for (const binder of statement.binders) {
        if ("text" in binder.type) {
          formulas.push({ ...base, role: "binder", math: binder.type });
        }
      }

      for (const hypothesis of statement.hypotheses) {
        if ("text" in hypothesis) {
          formulas.push({ ...base, role: "hypothesis", math: hypothesis });
        }
      }

      formulas.push({
        ...base,
        role: "conclusion",
        math: statement.conclusion,
      });
    }

    if (statement.kind === "def" && statement.definiens !== null) {
      const returnSort =
        statement.returnChain[statement.returnChain.length - 1]?.sort;

      formulas.push({
        statement: statement.name,
        role: "definiens",
        math: statement.definiens,
        scope: scopeOf(statement.binders),
        sorts: returnSort === undefined ? [] : [returnSort],
      });
    }
  }

  return formulas;
}

/**
 * Read one corpus formula as the engine would: engine mode (the file's
 * own delimiters, no elaboration, no lints), in the statement's scope,
 * at the first of its candidate sorts that takes it.
 */
export function readCorpusFormula(
  lang: SurfaceLanguage,
  formula: CorpusFormula,
): ParseResult {
  let last: ParseResult | null = null;

  for (const sort of formula.sorts) {
    const result = lang.parse(formula.math.text, {
      mode: "engine",
      scope: formula.scope,
      sort,
    });

    if (result.ok) {
      return result;
    }

    last = result;
  }

  return last ?? { ok: false, diagnostics: [] };
}

/** A term's tree with spans and printing hints dropped: what it *is*. */
export function shape(term: Term): string {
  if (term.kind === "variable") {
    return term.name;
  }

  return term.args.length === 0
    ? term.term
    : `(${term.term} ${term.args.map(shape).join(" ")})`;
}

/**
 * The file as a statement-only specification the compiler can take with
 * an empty proof script: every `theorem` becomes an `axiom` (same
 * statement, no proof owed) and every bodyless `def` a `term`. With
 * `rewrite`, each math string is replaced by the text `rewrite` returns
 * for it — the library's engine-mode printing, for the identity check —
 * and the two spellings compile to the same bytes exactly when the
 * library and the engine read them alike.
 */
export function axiomized(
  source: string,
  spec: Spec,
  rewrite?: (formula: CorpusFormula) => string | null,
): string {
  const edits: { start: number; end: number; text: string }[] = [];
  const formulas = corpusFormulas(spec);

  for (const statement of spec.statements) {
    if (statement.kind === "theorem") {
      const at = keywordAt(source, statement.span.start);
      edits.push({ start: at, end: at + "theorem".length, text: "axiom" });
    }

    if (statement.kind === "def" && statement.definiens === null) {
      const at = keywordAt(source, statement.span.start);
      edits.push({ start: at, end: at + "def".length, text: "term" });
    }
  }

  if (rewrite !== undefined) {
    for (const formula of formulas) {
      const text = rewrite(formula);

      if (text !== null) {
        edits.push({
          start: formula.math.span.start,
          end: formula.math.span.end,
          text: `$ ${text} $`,
        });
      }
    }
  }

  edits.sort((a, b) => b.start - a.start);

  let out = source;

  for (const edit of edits) {
    out = out.slice(0, edit.start) + edit.text + out.slice(edit.end);
  }

  // An Aufbau `@conversion` rule may not carry hypotheses once it is an
  // axiom; the annotation is the engine's rewriting policy, not syntax,
  // and dropping it leaves every statement to be parsed as before.
  return out
    .split("\n")
    .filter((line) => !line.trim().startsWith("--| @conversion"))
    .join("\n");
}

/**
 * Where a statement's keyword sits: its span opens on any doc comment
 * above it, and a comment may well contain the word `def`.
 */
function keywordAt(source: string, from: number): number {
  let at = from;

  for (;;) {
    while (at < source.length && /\s/.test(source[at] ?? "")) {
      at += 1;
    }

    if (source.startsWith("--", at)) {
      const eol = source.indexOf("\n", at);
      at = eol === -1 ? source.length : eol + 1;
      continue;
    }

    return at;
  }
}

/** The engine-mode spelling of a formula the library read, or null. */
export function enginePrinting(
  lang: SurfaceLanguage,
  formula: CorpusFormula,
): string | null {
  const result = readCorpusFormula(lang, formula);

  return result.ok ? printTerm(lang, result.term, "engine") : null;
}
