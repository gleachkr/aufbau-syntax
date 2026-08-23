/**
 * Release-version gate, the counterpart of Aufbau's `scripts/check-version.mjs`.
 *
 * There is one package here, so `package.json` is the single source of truth
 * (Aufbau needs a VERSION file only because four npm packages and a Zig build
 * must agree). Two things are checked: the version is a *stable* semantic
 * version — canary suffixes are minted by CI, never committed — and, when a
 * version is passed as an argument, that the tag being released matches it.
 *
 *   node scripts/check-version.mjs          # shape only
 *   node scripts/check-version.mjs 0.1.0    # …and it must be exactly this
 */

import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const manifest = JSON.parse(await readFile("package.json", "utf8"));
const version = manifest.version;

assert.match(
  version,
  /^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$/,
  `package.json must carry a stable semantic version, got ${version}`,
);

assert.equal(
  manifest.private,
  undefined,
  "package.json is marked private; npm publish would refuse it",
);

const expected = process.argv[2];
if (expected !== undefined) {
  assert.equal(
    version,
    expected,
    `release tag expects ${expected}, package.json has ${version}`,
  );
}

console.log(`Release version is ${version}.`);
