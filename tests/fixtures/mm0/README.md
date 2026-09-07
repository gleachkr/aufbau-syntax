# MM0 corpus

Reference `.mm0` files, copied whole, that `tests/mm0-corpus.test.ts`
reads, round-trips, and compiles against the Aufbau engine. They are here
to make one claim testable: that this library reads a superset of MM0 —
every file the engine accepts, read to the same trees.

## Upstream MM0 examples (CC0 1.0)

From `third_party/mm0/examples/` in the Aufbau repository, which vendors
[digama0/mm0](https://github.com/digama0/mm0); the examples are CC0.

- `peano.mm0`, `set.mm0`, `hol.mm0`, `miu.mm0`, `string.mm0`,
  `hello.mm0`, `goldbach.mm0`, `unprovable.mm0` — as upstream.
- `mm0-spec.mm0` — `peano.mm0` + `peano_hex.mm0` + `mm0.mm0`, the
  `import` lines removed (MM1's, not MM0's). `mm0.mm0` is upstream's
  complete formal specification of MM0 itself.
- `x86.mm0` — `peano.mm0` + `peano_hex.mm0` + `x86.mm0`, likewise.

Not included: `church.mm0` from the Aufbau proof cases, which gives one
token (`<->`) to two terms of different sorts. mm0.md forbids that ("the
first token of a notation … must not be shared"); the engine tolerates it
and this library reports it, so it is outside the grammar under test.

## Aufbau (Apache 2.0)

From the [Aufbau](https://github.com/gleachkr/Aufbau) repository.

- `aufbau-nd.mm0`, `aufbau-fol.mm0`, `aufbau-lam.mm0` — the manual's
  preludes, concatenated in the order the manual loads them
  (`nd-base`+`nd-rules`; those plus `fol-base`+`fol-rules`;
  `lam-base`+`lam-rules`).
- The named theories under `tests/proof_cases/` (`aristotle.mm0` …
  `zermelo_hilbert.mm0`); the `pass_*`/`fail_*` feature cases are not
  copied.
- The search fixtures under `src/frontend/compiler/search/fixtures/`.

Copied on 2026-09-07. Refresh by copying again; nothing here is edited.
