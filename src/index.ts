/**
 * @aufbau/syntax — surface syntax over MM0.
 *
 * The public API grows stage by stage; see the README for the layer stack.
 */

export type { Diagnostic, Span } from "./diagnostics";
export type {
  ParseFailure,
  ParseResult,
  ParseSuccess,
} from "./parse";
export { SurfaceLanguage } from "./parse";
export type {
  LintName,
  RewriteRule,
  RuleCapture,
  RuleLiteral,
  RulePatternElement,
  RuleReference,
  RuleTemplateElement,
  SyntaxAnnotation,
} from "./reader/annotations";
export type {
  CoercionInfo,
  LetterFamily,
  NotationInfo,
  SortInfo,
  Spec,
  SpecParse,
  TermInfo,
} from "./reader/spec";
export { parseSpec } from "./reader/spec";
export type {
  Annotation,
  AssertStatement,
  Binder,
  CoercionStatement,
  DefStatement,
  DelimiterStatement,
  GenNotationStatement,
  MathString,
  NotationLiteral,
  Precedence,
  SimpleNotationStatement,
  SortStatement,
  Statement,
  StatementParse,
  TermStatement,
  TypeRef,
} from "./reader/statements";
export { parseStatements } from "./reader/statements";
export type { Reading, ScanPoint } from "./scan";
export { Scanner } from "./scan";
export type { AppTerm, Fixity, Term, VariableTerm } from "./term";
export { walkTerm } from "./term";
