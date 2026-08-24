import { describe, expect, test } from "bun:test";
import {
  chunkAt,
  delimiterRules,
  isReachableChunk,
  segment,
} from "../src/index";

/** A set where every entry delimits on both sides, as MM0's one-list form. */
function symmetric(...entries: string[]) {
  return delimiterRules({
    left: new Set(entries),
    right: new Set(entries),
  });
}

describe("segmentation", () => {
  test("a delimiter is its own chunk, and bounds its neighbours", () => {
    const rules = symmetric("(", ")", ",");

    expect(segment("F(a,b)", rules)).toEqual(["F", "(", "a", ",", "b", ")"]);
    expect(segment("  F ( a , b )  ", rules)).toEqual([
      "F",
      "(",
      "a",
      ",",
      "b",
      ")",
    ]);
  });

  test("whitespace separates whether or not delimiters do", () => {
    const rules = symmetric("(", ")");

    expect(segment("foo bar", rules)).toEqual(["foo", "bar"]);
    expect(segment("foobar", rules)).toEqual(["foobar"]);
  });

  test("the longest delimiter spelling wins", () => {
    // `<->` must not read as `<` then `-` then `>`; the `<->` entry is
    // longer and is matched first.
    const rules = symmetric("<", "-", ">", "<->", "->");

    expect(segment("P<->Q", rules)).toEqual(["P", "<->", "Q"]);
    expect(segment("P->Q", rules)).toEqual(["P", "->", "Q"]);
  });

  test("a multi-character delimiter is one unit", () => {
    // The engine's table holds single bytes; the surface set holds strings,
    // which is the whole reason `∧` and `/\` can delimit at all.
    const rules = symmetric("/\\", "∧", "~");

    expect(segment("P/\\~Q", rules)).toEqual(["P", "/\\", "~", "Q"]);
    expect(segment("P∧Q", rules)).toEqual(["P", "∧", "Q"]);
    expect(segment("~~P", rules)).toEqual(["~", "~", "P"]);
  });

  test("left and right delimiters break on the sides MM0 says", () => {
    // MM0's rule: break *after* consuming a left delimiter, and *before* a
    // right one. With `(` left-only and `)` right-only, `(` glues to what
    // precedes it and `)` to what follows.
    const rules = delimiterRules({
      left: new Set(["("]),
      right: new Set([")"]),
    });

    expect(segment("a(b)c", rules)).toEqual(["a(", "b", ")c"]);
    expect(segment("(x)", rules)).toEqual(["(", "x", ")"]);
  });

  test("an empty set makes whitespace the only separator", () => {
    const rules = delimiterRules({ left: new Set(), right: new Set() });

    expect(segment("~~P->Q", rules)).toEqual(["~~P->Q"]);
    expect(segment("~~P -> Q", rules)).toEqual(["~~P", "->", "Q"]);
  });

  test("an astral character is never split in half", () => {
    const rules = symmetric("(", ")");

    expect(segment("(𝔽𝔾)", rules)).toEqual(["(", "𝔽𝔾", ")"]);
    expect(chunkAt("𝔽𝔾", 0, rules)).toBe("𝔽𝔾");
  });

  test("reachability is segmentation applied to one name", () => {
    const split = symmetric("a", "b");
    const whole = symmetric("(", ")");

    expect(isReachableChunk("ab", split)).toBe(false);
    expect(isReachableChunk("a", split)).toBe(true);
    expect(isReachableChunk("ab", whole)).toBe(true);
    expect(isReachableChunk("", whole)).toBe(false);
  });
});
