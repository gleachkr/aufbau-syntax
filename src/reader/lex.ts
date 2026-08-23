/**
 * The MM0 file-level lexer, per the upstream specification (mm0.md) as
 * summarized in Aufbau's manual (appendix-grammars.md):
 *
 *   lexeme       ::= symbol | identifier | number | math-string
 *   symbol       ::= '*' | '.' | ':' | ';' | '(' | ')' | '>' | '{' | '}'
 *                  | '=' | '_'
 *   identifier   ::= [a-zA-Z_][a-zA-Z0-9_]*
 *   number       ::= 0 | [1-9][0-9]*
 *   math-string  ::= '$' [^$]* '$'
 *
 * `--` starts a line comment; `--|` starts an annotation line, which this
 * lexer surfaces as a token of its own so the statement parser can attach it
 * to the statement that follows. This lexer reads *statements*; the contents
 * of math strings are scanned later, by the layer that owns them.
 */

import type { Span } from "../diagnostics.js";

export type TokenKind =
  | "annotation"
  | "identifier"
  | "math"
  | "number"
  | "symbol";

export interface FileToken {
  readonly kind: TokenKind;
  readonly span: Span;
  /**
   * The token's content: the symbol or identifier text, the digits of a
   * number, a math string's interior (without the dollar signs), or an
   * annotation line's payload (without the leading `--|`).
   */
  readonly text: string;
}

export interface LexError {
  readonly position: number;
  readonly id: "unterminated_math" | "unexpected_character";
}

export interface LexResult {
  readonly tokens: readonly FileToken[];
  readonly errors: readonly LexError[];
}

const SYMBOLS = new Set([
  "*",
  ".",
  ":",
  ";",
  "(",
  ")",
  ">",
  "{",
  "}",
  "=",
  "_",
]);

function isIdentStart(ch: string): boolean {
  return /[A-Za-z_]/.test(ch);
}

function isIdentPart(ch: string): boolean {
  return /[A-Za-z0-9_]/.test(ch);
}

export function lexFile(source: string): LexResult {
  const tokens: FileToken[] = [];
  const errors: LexError[] = [];
  let i = 0;

  while (i < source.length) {
    const ch = source[i];

    if (ch === undefined) {
      break;
    }

    if (/\s/.test(ch)) {
      i += 1;
      continue;
    }

    if (ch === "-" && source[i + 1] === "-") {
      const lineEnd = source.indexOf("\n", i);
      const end = lineEnd === -1 ? source.length : lineEnd;

      if (source[i + 2] === "|") {
        tokens.push({
          kind: "annotation",
          span: { start: i, end },
          text: source.slice(i + 3, end).trim(),
        });
      }

      i = end;
      continue;
    }

    if (ch === "$") {
      const close = source.indexOf("$", i + 1);

      if (close === -1) {
        errors.push({ position: i, id: "unterminated_math" });
        i = source.length;
        continue;
      }

      tokens.push({
        kind: "math",
        span: { start: i, end: close + 1 },
        text: source.slice(i + 1, close),
      });
      i = close + 1;
      continue;
    }

    if (isIdentStart(ch)) {
      let end = i + 1;

      while (end < source.length) {
        const next = source[end];
        if (next === undefined || !isIdentPart(next)) {
          break;
        }
        end += 1;
      }

      // A lone `_` is the symbol, not an identifier.
      const text = source.slice(i, end);
      tokens.push({
        kind: text === "_" ? "symbol" : "identifier",
        span: { start: i, end },
        text,
      });
      i = end;
      continue;
    }

    if (/[0-9]/.test(ch)) {
      let end = i + 1;

      while (end < source.length && /[0-9]/.test(source[end] ?? "")) {
        end += 1;
      }

      tokens.push({
        kind: "number",
        span: { start: i, end },
        text: source.slice(i, end),
      });
      i = end;
      continue;
    }

    if (SYMBOLS.has(ch)) {
      tokens.push({
        kind: "symbol",
        span: { start: i, end: i + 1 },
        text: ch,
      });
      i += 1;
      continue;
    }

    errors.push({ position: i, id: "unexpected_character" });
    i += 1;
  }

  return { tokens, errors };
}
