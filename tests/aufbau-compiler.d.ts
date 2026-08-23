/**
 * Ambient typings for the untyped `@aufbau/compiler` package, scoped to
 * the test program — only the surface the engine-alignment test drives.
 * Mirrors carnap-server's `tests/aufbau-engines.d.ts`.
 */

declare module "@aufbau/compiler" {
  export interface CompileResult {
    readonly ok?: boolean;
    readonly mmbBytes?: Uint8Array;
    readonly diagnostics?: unknown;
  }

  export interface LoadedCompiler {
    compile(mm0Text: string, proofText: string): CompileResult;
  }

  export function loadCompiler(options?: {
    readonly wasmBytes?: Uint8Array | ArrayBuffer;
    readonly wasmUrl?: string | URL;
    readonly locale?: string;
  }): Promise<LoadedCompiler>;
}
