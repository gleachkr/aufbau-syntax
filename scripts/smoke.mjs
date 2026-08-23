/**
 * Smoke-test the built package the way a consumer meets it: import `dist/`
 * from plain Node, read a shipped spec, parse textbook input, print it back.
 *
 * This is not a substitute for `bun test` — it is the check that the *emitted*
 * artifact works outside Bun. It catches exactly the failures the test suite
 * cannot see: an import specifier Node's ESM resolver rejects, a file missing
 * from `files`, an entry point that points at nothing.
 *
 *   node scripts/smoke.mjs
 */

import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const { parseSpec, printTerm, SurfaceLanguage } = await import(
  new URL("../dist/index.js", import.meta.url)
);

const source = await readFile(
  new URL("../specs/forallx-calgary-2019.mm0", import.meta.url),
  "utf8",
);

const { spec, diagnostics } = parseSpec(source);
assert.deepEqual(diagnostics, [], "the shipped spec must read cleanly");

const language = new SurfaceLanguage(spec);
const result = language.parse("AxF(x) -> G(a)");
assert.ok(result.ok, `parse failed: ${JSON.stringify(result.diagnostics)}`);

const display = printTerm(language, result.term, "display");
assert.equal(display, "∀xF(x) → G(a)");

const engine = printTerm(language, result.term, "engine");
const reparsed = language.parse(engine, { lints: false });
assert.ok(reparsed.ok, "engine output must re-parse");
assert.equal(printTerm(language, reparsed.term, "display"), display);

console.log(`Built package works in Node: ${display}`);
