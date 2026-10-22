/**
 * @aufbau/syntax — surface syntax over MM0.
 *
 * The public API grows stage by stage; see the README for the layer stack.
 */

export type { AbstractSites } from "./abstract.js";
export { abstractContext } from "./abstract.js";
export type { DelimiterRules, DelimiterSet } from "./delimiters.js";
export {
  adjoin,
  chunkAt,
  delimiterRules,
  isReachableChunk,
  segment,
} from "./delimiters.js";
export type { Diagnostic, Severity, Span } from "./diagnostics.js";
export { boundVariableBinders, stripSyntaxAnnotations } from "./engine.js";
export type { NormalOptions, VariableInfo, Variables } from "./normal.js";
export {
  engineForm,
  normalTerm,
  RewriteLimitError,
  sameTerm,
  statementVariables,
  termKey,
  Unstatable,
} from "./normal.js";
export type {
  ParseFailure,
  ParseMode,
  ParseResult,
  ParseSuccess,
} from "./parse.js";
export { SurfaceLanguage, TermBuildError } from "./parse.js";
export type { PieceKind, PrintedPiece, PrintMode } from "./print.js";
export { printPieces, printTerm, UnprintableTermError } from "./print.js";
export type {
  ElabRule,
  LintName,
  OperandRelation,
  RuleCapture,
  RuleLiteral,
  RulePatternElement,
  RuleReference,
  RuleTemplateElement,
  SyntaxAnnotation,
} from "./reader/annotations.js";
export type {
  Acui,
  CoercionInfo,
  Definition,
  NotationInfo,
  Relation,
  RuleInfo,
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
export type { SpellingMeanings } from "./spelling.js";
export { notationToken, spellingMeanings, spellingsOf } from "./spelling.js";
export { splitTopLevel } from "./split.js";
export type {
  BinderShadow,
  BinderShadowKind,
  StatementFormula,
  StatementReading,
} from "./statement.js";
export {
  binderShadows,
  parseStatement,
  statementScope,
} from "./statement.js";
export type { AppTerm, Fixity, Term, VariableTerm } from "./term.js";
export { freeVariables, substitute, walkTerm } from "./term.js";
export { unfoldDefinitions } from "./unfold.js";
export type { NameRef, Vocabulary } from "./vocabulary.js";
export { surfaceVocabulary } from "./vocabulary.js";
