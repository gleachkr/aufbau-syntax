# Releasing

`@aufbau/syntax` releases the same way [gleachkr/Aufbau][aufbau] does, so
there is one set of habits for both: **every push to `main` publishes a
canary**, and **a `v1.2.3` tag publishes a stable version**. The workflows
are `.github/workflows/test.yml` and `.github/workflows/npm-canary.yml`.

[aufbau]: https://github.com/gleachkr/Aufbau

## What CI does

`test.yml` runs on every push to `main`, every pull request, and on demand.
It installs with a frozen lockfile, checks the release version, runs
`bun run validate` (tests, `tsc --noEmit`, `biome ci`), builds `dist/`, runs
the built package through **Node** (`scripts/smoke.mjs`), and asserts the
tarball would carry `dist/` and `specs/` but no sources.

The Node smoke test earns its place: the suite runs under Bun, which resolves
extensionless imports and TypeScript alike, so it cannot notice that a
published artifact is unloadable anywhere else. Relative imports in `src/`
carry `.js` extensions for the same reason — `tsc` emits specifiers verbatim,
and Node's ESM resolver does not guess.

`npm-canary.yml` publishes:

| trigger | version | dist-tag |
| --- | --- | --- |
| push to `main` | `0.0.1-canary.20260823T101500Z.42.g0123456789ab` | `canary` |
| tag `v0.1.0` | `0.1.0` (must match `package.json`) | `latest` |

A tag run calls `test.yml` first and publishes only if it passes; a canary run
publishes straight from `main`, which is already green from its own push.
`workflow_dispatch` takes a `dry_run` input that adds `--dry-run` to
`npm publish` — the way to rehearse the whole path without a release.

The committed version in `package.json` is always a *stable* semantic version;
`scripts/check-version.mjs` enforces that, so a canary suffix can never be
committed by accident. CI mints the suffix at publish time and never commits
it back.

## Cutting a stable release

1. Move the `Unreleased` section of `CHANGELOG.md` under the new version.
2. `npm version 0.1.0 --no-git-tag-version` (or edit `package.json`), commit.
3. Tag `v0.1.0` and push the tag. The tag must match `package.json` exactly —
   the workflow fails loudly rather than publishing a mismatch.

## One-time setup on GitHub and npm

The repository is local-only today. Before any of this runs:

1. **Create the GitHub repository** and push `main`. The `repository` field in
   `package.json` says `github.com/gleachkr/aufbau-syntax`; provenance
   attestation compares it against the repository the workflow runs in, so if
   the repository is named something else, that field has to change with it.
2. **Publish `0.0.1` once by hand** — `npm publish --access public` from a
   clean checkout, with `dist/` freshly built (`prepack` handles it). npm can
   only attach a trusted publisher to a package that already exists, so the
   first release bootstraps the mechanism CI then uses.
3. **Configure trusted publishing** on npmjs.com: the package's *Settings* →
   *Trusted publisher* → GitHub Actions, repository `gleachkr/aufbau-syntax`,
   workflow `npm-canary.yml`. That is what makes the workflow's
   `id-token: write` sufficient — there is no `NPM_TOKEN` secret to leak or
   rotate, and `--provenance` gets a verifiable attestation.

`@aufbau` is a scoped package, so the first publish needs the scope to exist
and `--access public` (in `publishConfig` as well as on the command line).

## Consuming a canary

Same as the engine packages:

```sh
bun add @aufbau/syntax@canary
# or pin a commit's build exactly
bun add @aufbau/syntax@0.0.1-canary.20260823T101500Z.42.g0123456789ab
```

Carnap-server pins exact versions rather than ranges — a canary is a specific
build, and pinning is what makes "the server broke when syntax changed"
answerable.
