import { describe, expect, test } from "bun:test";
import { readdir, readFile } from "node:fs/promises";
import { join } from "node:path";

/**
 * The library is consumed by browsers, Cloudflare Workers, and Bun alike, so
 * src/ may not touch any platform global. Comments and string literals are
 * stripped first — prose about "a document" is fine; *code* reaching for one
 * is not — and identifier-boundary matching keeps words like "windowed" from
 * tripping it. Property access (`spec.process`) is allowed by the lookbehind.
 */
const FORBIDDEN = [
  "document",
  "window",
  "navigator",
  "localStorage",
  "fetch",
  "XMLHttpRequest",
  "WebSocket",
  "Bun",
  "process",
  "require",
  "__dirname",
];

/**
 * Remove comments and string/template literals, preserving everything else.
 * A character-level pass, not a real lexer, but the constructs it skips are
 * the ones whose contents must not count. Escapes inside strings are honored;
 * template interpolations are left in place (they are code).
 */
function stripNonCode(text: string): string {
  let out = "";
  let i = 0;

  while (i < text.length) {
    const two = text.slice(i, i + 2);

    if (two === "//") {
      while (i < text.length && text[i] !== "\n") i += 1;
    } else if (two === "/*") {
      const end = text.indexOf("*/", i + 2);
      i = end === -1 ? text.length : end + 2;
    } else if (text[i] === '"' || text[i] === "'" || text[i] === "`") {
      const quote = text[i];
      i += 1;
      while (i < text.length && text[i] !== quote) {
        i += text[i] === "\\" ? 2 : 1;
      }
      i += 1;
    } else {
      out += text[i];
      i += 1;
    }
  }

  return out;
}

async function sourceFiles(dir: string): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  const files: string[] = [];

  for (const entry of entries) {
    const path = join(dir, entry.name);

    if (entry.isDirectory()) {
      files.push(...(await sourceFiles(path)));
    } else if (entry.name.endsWith(".ts")) {
      files.push(path);
    }
  }

  return files;
}

describe("platform discipline", () => {
  test("src/ references no platform global", async () => {
    const files = await sourceFiles(
      new URL("../src", import.meta.url).pathname,
    );

    expect(files.length).toBeGreaterThan(0);

    for (const file of files) {
      const code = stripNonCode(await readFile(file, "utf8"));

      for (const name of FORBIDDEN) {
        const pattern = new RegExp(`(?<![\\w$.])${name}(?![\\w$])`);

        expect(
          pattern.test(code) ? `${file} references "${name}"` : null,
        ).toBeNull();
      }
    }
  });
});
