/**
 * @aufbau/syntax — surface syntax over MM0.
 *
 * The public API grows stage by stage; see the README for the layer stack.
 */

export type { DelimiterRules, DelimiterSet } from "./delimiters.js";
export {
  chunkAt,
  delimiterRules,
  isReachableChunk,
  segment,
} from "./delimiters.js";
export type { Diagnostic, Severity, Span } from "./diagnostics.js";
export { boundVariableBinders, stripSyntaxAnnotations } from "./engine.js";
export type {
  ParseFailure,
  ParseMode,
  ParseResult,
  ParseSuccess,
} from "./parse.js";
export { SurfaceLanguage } from "./parse.js";
export type { PrintMode } from "./print.js";
export { printTerm } from "./print.js";
export type {
  ElabRule,
  LintName,
  RuleCapture,
  RuleLiteral,
  RulePatternElement,
  RuleReference,
  RuleTemplateElement,
  SyntaxAnnotation,
} from "./reader/annotations.js";
export type {
  CoercionInfo,
  NotationInfo,
  SortInfo,
  Spec,
  SpecParse,
  TermInfo,
} from "./reader/spec.js";
export { parseSpec } from "./reader/spec.js";
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
} from "./reader/statements.js";
export { parseStatements } from "./reader/statements.js";
export type { Reading, ScanPoint, Scope } from "./scan.js";
export { Scanner } from "./scan.js";
export type { AppTerm, Fixity, Term, VariableTerm } from "./term.js";
export { walkTerm } from "./term.js";
export type { NameRef, Vocabulary } from "./vocabulary.js";
export { surfaceVocabulary } from "./vocabulary.js";
