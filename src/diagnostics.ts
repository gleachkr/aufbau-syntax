/**
 * Diagnostics carried by every layer of the library.
 *
 * Each diagnostic is structured — a stable id, its parameters, and a source
 * span — so a consumer can reword or translate it. `message` is the id's
 * English template with the parameters filled in, so a consumer that does
 * neither still has something to show.
 */

/** Half-open range of UTF-16 code-unit offsets into the source text. */
export interface Span {
  readonly start: number;
  readonly end: number;
}

/**
 * `error` means the thing being described does not work. `warning` means it
 * works but is very likely not what was meant — a spec that only warns is
 * still usable, and a consumer that ignores the distinction still sees a
 * message.
 */
export type Severity = "error" | "warning";

export interface Diagnostic {
  readonly id: string;
  readonly message: string;
  readonly params: Readonly<Record<string, string>>;
  readonly severity: Severity;
  readonly span: Span;
}

/**
 * Fill `{name}` holes in a template. A hole with no matching parameter is
 * left as written, which makes a mismatched template visible in output
 * rather than silently blank.
 */
export function fillTemplate(
  template: string,
  params: Readonly<Record<string, string>>,
): string {
  return template.replace(/\{(\w+)\}/g, (hole, name: string) => {
    const value = params[name];
    return value === undefined ? hole : value;
  });
}

export function diagnostic(
  id: string,
  template: string,
  params: Readonly<Record<string, string>>,
  span: Span,
  severity: Severity = "error",
): Diagnostic {
  return {
    id,
    message: fillTemplate(template, params),
    params,
    severity,
    span,
  };
}
