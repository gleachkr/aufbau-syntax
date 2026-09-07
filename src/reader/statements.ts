/**
 * The MM0 statement parser: file tokens in, statements out.
 *
 * The grammar is the upstream one (mm0.md), in the subset Aufbau reads —
 * summarized in the manual's appendix-grammars.md. Math strings are carried
 * through opaque: scanning their contents is the surface layer's job, and an
 * axiom's body never needs it at all.
 *
 * On a malformed statement the parser records one diagnostic and skips to
 * the next `;`, so a spec author sees every broken statement at once.
 */

import { type Diagnostic, diagnostic, type Span } from "../diagnostics.js";
import { type FileToken, lexFile } from "./lex.js";

/** A math string, with the span of the whole `$ … $` lexeme. */
export interface MathString {
  readonly span: Span;
  readonly text: string;
}

/** An annotation line's payload, e.g. `@acui seq_assoc _ snil _`. */
export interface Annotation {
  readonly span: Span;
  readonly text: string;
}

/** A sort name applied to the bound variables the value may depend on. */
export interface TypeRef {
  readonly dependencies: readonly string[];
  readonly sort: string;
  readonly span: Span;
}

export interface Binder {
  /** `{x: s}` binders bind; `(a: s)` binders are regular. */
  readonly binds: boolean;
  /** True for a `.`-prefixed dummy on a `def`. */
  readonly dummy: boolean;
  readonly name: string;
  readonly span: Span;
  /** A hypothesis binder `(h: $ … $)` carries a formula instead. */
  readonly type: TypeRef | MathString;
}

export type Precedence = number | "max";

/** One slot of a general notation: a constant literal or a variable. */
export type NotationLiteral =
  | {
      readonly kind: "constant";
      readonly prec: Precedence;
      readonly token: string;
      readonly span: Span;
    }
  | { readonly kind: "variable"; readonly name: string; readonly span: Span };

interface StatementBase {
  readonly annotations: readonly Annotation[];
  readonly span: Span;
}

export interface SortStatement extends StatementBase {
  readonly kind: "sort";
  readonly modifiers: readonly string[];
  readonly name: string;
}

export interface TermStatement extends StatementBase {
  readonly kind: "term";
  readonly name: string;
  readonly binders: readonly Binder[];
  /** The `:`-side arrow chain; the last entry is the return type. */
  readonly returnChain: readonly TypeRef[];
}

export interface DefStatement extends StatementBase {
  readonly kind: "def";
  readonly name: string;
  readonly binders: readonly Binder[];
  /**
   * The `:`-side arrow chain; the last entry is the return type. mm0.md
   * gives `def` a plain type here, but the reference examples (hol.mm0's
   * `def all: type > term`) use the arrow sugar as on a `term`.
   */
  readonly returnChain: readonly TypeRef[];
  /** Absent on a bodyless def (definiens supplied by the proof file). */
  readonly definiens: MathString | null;
}

export interface AssertStatement extends StatementBase {
  readonly kind: "axiom" | "theorem";
  readonly name: string;
  readonly binders: readonly Binder[];
  /** The `>`-chain: hypotheses (types or formulas), then the conclusion. */
  readonly hypotheses: readonly (TypeRef | MathString)[];
  readonly conclusion: MathString;
}

export interface DelimiterStatement extends StatementBase {
  readonly kind: "delimiter";
  /** The one-list form fills both sides with the same characters. */
  readonly left: readonly string[];
  readonly right: readonly string[];
}

export interface SimpleNotationStatement extends StatementBase {
  readonly kind: "simple-notation";
  readonly fixity: "infixl" | "infixr" | "prefix";
  readonly term: string;
  readonly token: string;
  readonly prec: Precedence;
}

export interface CoercionStatement extends StatementBase {
  readonly kind: "coercion";
  readonly name: string;
  readonly from: string;
  readonly to: string;
}

/**
 * An `input` or `output` statement — mm0.md's optional verifier I/O,
 * `output string: $ hello $;`. Read so a file that has one still reads;
 * the items are the verifier's business and are carried, not interpreted.
 */
export interface InOutStatement extends StatementBase {
  readonly kind: "input" | "output";
  /** The I/O kind identifier, e.g. `string`, `s_expr`. */
  readonly ioKind: string;
  readonly items: readonly (MathString | string)[];
}

export interface GenNotationStatement extends StatementBase {
  readonly kind: "notation";
  readonly term: string;
  readonly binders: readonly Binder[];
  readonly returnType: TypeRef;
  readonly literals: readonly NotationLiteral[];
}

export type Statement =
  | AssertStatement
  | CoercionStatement
  | DefStatement
  | DelimiterStatement
  | GenNotationStatement
  | InOutStatement
  | SimpleNotationStatement
  | SortStatement
  | TermStatement;

export interface StatementParse {
  readonly statements: readonly Statement[];
  readonly diagnostics: readonly Diagnostic[];
}

const SORT_MODIFIERS = new Set(["pure", "strict", "provable", "free"]);

const TEMPLATES: Record<string, string> = {
  lex_unexpected_character: "unexpected character",
  lex_unterminated_math: "unterminated math string",
  expected_token: "expected {expected} but found {found}",
  unknown_statement: "unknown statement keyword {keyword}",
  bad_precedence: "expected a precedence (a number or max)",
  empty_delimiter: "a delimiter math string must list characters",
  multibyte_delimiter:
    "delimiter {token} is not a single byte; the engine cannot split on it",
  notation_leading_variable:
    "the first literal of a notation must be a constant",
};

class Cursor {
  readonly diagnostics: Diagnostic[] = [];
  private position = 0;

  constructor(
    private readonly tokens: readonly FileToken[],
    private readonly sourceLength: number,
  ) {}

  peek(): FileToken | null {
    return this.tokens[this.position] ?? null;
  }

  next(): FileToken | null {
    const token = this.tokens[this.position] ?? null;
    if (token !== null) {
      this.position += 1;
    }
    return token;
  }

  atEnd(): boolean {
    return this.position >= this.tokens.length;
  }

  hereSpan(): Span {
    const token = this.peek();
    return token
      ? token.span
      : { start: this.sourceLength, end: this.sourceLength };
  }

  report(id: string, params: Record<string, string>, span: Span): void {
    const template = TEMPLATES[id] ?? id;
    this.diagnostics.push(diagnostic(id, template, params, span));
  }

  /** Consume a specific symbol, or report and return false. */
  expectSymbol(text: string): boolean {
    const token = this.peek();

    if (token !== null && token.kind === "symbol" && token.text === text) {
      this.next();
      return true;
    }

    this.report(
      "expected_token",
      { expected: `"${text}"`, found: token ? token.text : "end of file" },
      this.hereSpan(),
    );
    return false;
  }

  expectIdentifier(): string | null {
    const token = this.peek();

    if (token !== null && token.kind === "identifier") {
      this.next();
      return token.text;
    }

    this.report(
      "expected_token",
      {
        expected: "an identifier",
        found: token ? token.text : "end of file",
      },
      this.hereSpan(),
    );
    return null;
  }

  expectMath(): MathString | null {
    const token = this.peek();

    if (token !== null && token.kind === "math") {
      this.next();
      return { span: token.span, text: token.text };
    }

    this.report(
      "expected_token",
      {
        expected: "a math string",
        found: token ? token.text : "end of file",
      },
      this.hereSpan(),
    );
    return null;
  }

  /** Skip past the next `;`, for error recovery. */
  synchronize(): void {
    while (!this.atEnd()) {
      const token = this.next();
      if (token !== null && token.kind === "symbol" && token.text === ";") {
        return;
      }
    }
  }
}

/** `identifier (identifier)*` — a sort applied to its dependencies. */
function parseTypeRef(cursor: Cursor): TypeRef | null {
  const start = cursor.hereSpan();
  const sort = cursor.expectIdentifier();

  if (sort === null) {
    return null;
  }

  const dependencies: string[] = [];
  let end = start;

  for (;;) {
    const token = cursor.peek();
    if (token === null || token.kind !== "identifier") {
      break;
    }
    cursor.next();
    dependencies.push(token.text);
    end = token.span;
  }

  return { sort, dependencies, span: { start: start.start, end: end.end } };
}

/**
 * One binder group — `{x y: type}` or `(a b: type-or-formula)` — flattened
 * to one Binder per name. `allowFormula` admits hypothesis binders (assert
 * statements); `allowDummy` admits `.`-prefixed names (defs).
 */
function parseBinderGroup(
  cursor: Cursor,
  options: { allowFormula: boolean; allowDummy: boolean },
): Binder[] | null {
  const open = cursor.peek();

  if (open === null || open.kind !== "symbol") {
    return null;
  }

  const binds = open.text === "{";

  if (!binds && open.text !== "(") {
    return null;
  }

  cursor.next();
  const names: { name: string; dummy: boolean; span: Span }[] = [];

  for (;;) {
    const token = cursor.peek();

    if (token === null) {
      break;
    }

    if (token.kind === "symbol" && token.text === ".") {
      if (!options.allowDummy) {
        break;
      }
      cursor.next();
      const name = cursor.expectIdentifier();
      if (name === null) {
        return null;
      }
      names.push({ name, dummy: true, span: token.span });
      continue;
    }

    if (token.kind === "identifier") {
      cursor.next();
      names.push({ name: token.text, dummy: false, span: token.span });
      continue;
    }

    // An anonymous binder position, `_`.
    if (token.kind === "symbol" && token.text === "_") {
      cursor.next();
      names.push({ name: "_", dummy: false, span: token.span });
      continue;
    }

    break;
  }

  if (!cursor.expectSymbol(":")) {
    return null;
  }

  let type: TypeRef | MathString | null;
  const typeToken = cursor.peek();

  if (
    options.allowFormula &&
    typeToken !== null &&
    typeToken.kind === "math"
  ) {
    cursor.next();
    type = { span: typeToken.span, text: typeToken.text };
  } else {
    type = parseTypeRef(cursor);
  }

  if (type === null) {
    return null;
  }

  if (!cursor.expectSymbol(binds ? "}" : ")")) {
    return null;
  }

  return names.map((entry) => ({
    binds,
    dummy: entry.dummy,
    name: entry.name,
    span: entry.span,
    type: type as TypeRef | MathString,
  }));
}

function parseBinders(
  cursor: Cursor,
  options: { allowFormula: boolean; allowDummy: boolean },
): Binder[] | null {
  const binders: Binder[] = [];

  for (;;) {
    const token = cursor.peek();

    if (
      token === null ||
      token.kind !== "symbol" ||
      (token.text !== "(" && token.text !== "{")
    ) {
      return binders;
    }

    const group = parseBinderGroup(cursor, options);

    if (group === null) {
      return null;
    }

    binders.push(...group);
  }
}

function parsePrecedence(cursor: Cursor): Precedence | null {
  const token = cursor.peek();

  if (token !== null && token.kind === "number") {
    cursor.next();
    return Number.parseInt(token.text, 10);
  }

  if (token !== null && token.kind === "identifier" && token.text === "max") {
    cursor.next();
    return "max";
  }

  cursor.report("bad_precedence", {}, cursor.hereSpan());
  return null;
}

/** Split a delimiter math string into its whitespace-separated tokens. */
function delimiterChars(cursor: Cursor, math: MathString): string[] | null {
  const parts = math.text.split(/\s+/).filter((part) => part.length > 0);

  if (parts.length === 0) {
    cursor.report("empty_delimiter", {}, math.span);
    return null;
  }

  for (const part of parts) {
    const points = [...part];
    const single =
      points.length === 1 && (points[0]?.codePointAt(0) ?? 0x80) <= 0x7f;

    if (!single) {
      cursor.report("multibyte_delimiter", { token: part }, math.span);
      return null;
    }
  }

  return parts;
}

interface Pending {
  readonly annotations: Annotation[];
  readonly start: Span;
}

function parseStatement(
  cursor: Cursor,
  keyword: FileToken,
  pending: Pending,
): Statement | null {
  const base = (endSpan: Span): StatementBase => ({
    annotations: pending.annotations,
    span: { start: pending.start.start, end: endSpan.end },
  });

  const finish = <S extends Statement>(statement: S): S | null =>
    cursor.expectSymbol(";") ? statement : null;

  if (SORT_MODIFIERS.has(keyword.text) || keyword.text === "sort") {
    const modifiers: string[] = [];
    let cursorToken: FileToken | null = keyword;

    while (cursorToken !== null && SORT_MODIFIERS.has(cursorToken.text)) {
      modifiers.push(cursorToken.text);
      cursorToken = cursor.next();
    }

    if (cursorToken === null || cursorToken.text !== "sort") {
      cursor.report(
        "expected_token",
        {
          expected: '"sort"',
          found: cursorToken ? cursorToken.text : "end of file",
        },
        cursor.hereSpan(),
      );
      return null;
    }

    const name = cursor.expectIdentifier();

    if (name === null) {
      return null;
    }

    return finish({
      ...base(cursor.hereSpan()),
      kind: "sort",
      modifiers,
      name,
    });
  }

  switch (keyword.text) {
    case "term": {
      const name = cursor.expectIdentifier();
      if (name === null) return null;

      const binders = parseBinders(cursor, {
        allowFormula: false,
        allowDummy: false,
      });
      if (binders === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const returnChain = parseArrowChain(cursor);
      if (returnChain === null) return null;

      return finish({
        ...base(cursor.hereSpan()),
        kind: "term",
        name,
        binders,
        returnChain,
      });
    }

    case "def": {
      const name = cursor.expectIdentifier();
      if (name === null) return null;

      const binders = parseBinders(cursor, {
        allowFormula: false,
        allowDummy: true,
      });
      if (binders === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const returnChain = parseArrowChain(cursor);
      if (returnChain === null) return null;

      let definiens: MathString | null = null;
      const eq = cursor.peek();

      if (eq !== null && eq.kind === "symbol" && eq.text === "=") {
        cursor.next();
        definiens = cursor.expectMath();
        if (definiens === null) return null;
      }

      return finish({
        ...base(cursor.hereSpan()),
        kind: "def",
        name,
        binders,
        returnChain,
        definiens,
      });
    }

    case "axiom":
    case "theorem": {
      const name = cursor.expectIdentifier();
      if (name === null) return null;

      const binders = parseBinders(cursor, {
        allowFormula: true,
        allowDummy: false,
      });
      if (binders === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const chain: (TypeRef | MathString)[] = [];

      for (;;) {
        const token = cursor.peek();

        if (token !== null && token.kind === "math") {
          cursor.next();
          chain.push({ span: token.span, text: token.text });
        } else {
          const type = parseTypeRef(cursor);
          if (type === null) return null;
          chain.push(type);
        }

        const arrow = cursor.peek();
        if (arrow !== null && arrow.kind === "symbol" && arrow.text === ">") {
          cursor.next();
          continue;
        }
        break;
      }

      const conclusion = chain[chain.length - 1];

      if (conclusion === undefined || !("text" in conclusion)) {
        cursor.report(
          "expected_token",
          { expected: "a concluding math string", found: ";" },
          cursor.hereSpan(),
        );
        return null;
      }

      return finish({
        ...base(cursor.hereSpan()),
        kind: keyword.text,
        name,
        binders,
        hypotheses: chain.slice(0, -1),
        conclusion,
      });
    }

    case "delimiter": {
      const first = cursor.expectMath();
      if (first === null) return null;

      const firstChars = delimiterChars(cursor, first);
      if (firstChars === null) return null;

      const maybeSecond = cursor.peek();

      if (maybeSecond !== null && maybeSecond.kind === "math") {
        cursor.next();
        const secondChars = delimiterChars(cursor, {
          span: maybeSecond.span,
          text: maybeSecond.text,
        });
        if (secondChars === null) return null;

        return finish({
          ...base(cursor.hereSpan()),
          kind: "delimiter",
          left: firstChars,
          right: secondChars,
        });
      }

      return finish({
        ...base(cursor.hereSpan()),
        kind: "delimiter",
        left: firstChars,
        right: firstChars,
      });
    }

    case "prefix":
    case "infixl":
    case "infixr": {
      const term = cursor.expectIdentifier();
      if (term === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const token = cursor.expectMath();
      if (token === null) return null;

      const precKeyword = cursor.expectIdentifier();
      if (precKeyword === null) return null;

      if (precKeyword !== "prec") {
        cursor.report(
          "expected_token",
          { expected: '"prec"', found: precKeyword },
          cursor.hereSpan(),
        );
        return null;
      }

      const prec = parsePrecedence(cursor);
      if (prec === null) return null;

      return finish({
        ...base(cursor.hereSpan()),
        kind: "simple-notation",
        fixity: keyword.text,
        term,
        token: token.text.trim(),
        prec,
      });
    }

    case "coercion": {
      const name = cursor.expectIdentifier();
      if (name === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const from = cursor.expectIdentifier();
      if (from === null) return null;
      if (!cursor.expectSymbol(">")) return null;

      const to = cursor.expectIdentifier();
      if (to === null) return null;

      return finish({
        ...base(cursor.hereSpan()),
        kind: "coercion",
        name,
        from,
        to,
      });
    }

    case "notation": {
      const term = cursor.expectIdentifier();
      if (term === null) return null;

      const binders = parseBinders(cursor, {
        allowFormula: false,
        allowDummy: false,
      });
      if (binders === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const returnType = parseTypeRef(cursor);
      if (returnType === null) return null;
      if (!cursor.expectSymbol("=")) return null;

      const literals: NotationLiteral[] = [];

      for (;;) {
        const token = cursor.peek();

        if (token === null) {
          break;
        }

        if (token.kind === "symbol" && token.text === "(") {
          cursor.next();
          const constant = cursor.expectMath();
          if (constant === null) return null;
          if (!cursor.expectSymbol(":")) return null;
          const prec = parsePrecedence(cursor);
          if (prec === null) return null;
          if (!cursor.expectSymbol(")")) return null;

          literals.push({
            kind: "constant",
            prec,
            token: constant.text.trim(),
            span: constant.span,
          });
          continue;
        }

        if (token.kind === "identifier") {
          cursor.next();
          literals.push({
            kind: "variable",
            name: token.text,
            span: token.span,
          });
          continue;
        }

        break;
      }

      const first = literals[0];

      if (first === undefined || first.kind !== "constant") {
        cursor.report(
          "notation_leading_variable",
          {},
          first?.span ?? cursor.hereSpan(),
        );
        return null;
      }

      return finish({
        ...base(cursor.hereSpan()),
        kind: "notation",
        term,
        binders,
        returnType,
        literals,
      });
    }

    case "input":
    case "output": {
      const ioKind = cursor.expectIdentifier();
      if (ioKind === null) return null;
      if (!cursor.expectSymbol(":")) return null;

      const items: (MathString | string)[] = [];

      for (;;) {
        const token = cursor.peek();

        if (token === null) break;

        if (token.kind === "math") {
          cursor.next();
          items.push({ span: token.span, text: token.text });
          continue;
        }

        if (token.kind === "identifier") {
          cursor.next();
          items.push(token.text);
          continue;
        }

        break;
      }

      return finish({
        ...base(cursor.hereSpan()),
        kind: keyword.text,
        ioKind,
        items,
      });
    }

    default:
      cursor.report(
        "unknown_statement",
        { keyword: keyword.text },
        keyword.span,
      );
      return null;
  }
}

/** `type ('>' type)*` — the arrow sugar on a `term` or `def` return. */
function parseArrowChain(cursor: Cursor): TypeRef[] | null {
  const chain: TypeRef[] = [];

  for (;;) {
    const type = parseTypeRef(cursor);
    if (type === null) return null;
    chain.push(type);

    const arrow = cursor.peek();
    if (arrow !== null && arrow.kind === "symbol" && arrow.text === ">") {
      cursor.next();
      continue;
    }
    break;
  }

  return chain;
}

export function parseStatements(source: string): StatementParse {
  const lexed = lexFile(source);
  const cursor = new Cursor(lexed.tokens, source.length);

  for (const error of lexed.errors) {
    cursor.report(
      `lex_${error.id}`,
      {},
      { start: error.position, end: error.position + 1 },
    );
  }

  const statements: Statement[] = [];
  let annotations: Annotation[] = [];

  while (!cursor.atEnd()) {
    const token = cursor.next();

    if (token === null) {
      break;
    }

    if (token.kind === "annotation") {
      annotations.push({ span: token.span, text: token.text });
      continue;
    }

    if (token.kind !== "identifier") {
      cursor.report(
        "expected_token",
        { expected: "a statement keyword", found: token.text },
        token.span,
      );
      cursor.synchronize();
      annotations = [];
      continue;
    }

    const statement = parseStatement(cursor, token, {
      annotations,
      start: annotations[0]?.span ?? token.span,
    });

    if (statement === null) {
      cursor.synchronize();
    } else {
      statements.push(statement);
    }

    annotations = [];
  }

  return { statements, diagnostics: cursor.diagnostics };
}
