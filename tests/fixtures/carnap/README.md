# Carnap's theories

The built-in theories Carnap ships, from `src/worker/logic/theories/` in the
Carnap server repository. `tests/normal-engine.test.ts` checks this
library's normal forms and term identity against the Aufbau compiler on
them, since they are the theories whose rows Carnap compares.

- The top-level `.mm0` files are Carnap's base theories, copied whole.
- `derived/` and `modal/` are Carnap's fragments, also copied whole. They
  are not theories on their own. The test joins them as Carnap's
  `theories/index.ts` does: a `-plus` system is a base and its `derived/`
  fragment, and a modal logic past K is `open-logic-modal-k.mm0` and its
  `modal/` fragments.
- `carnap-prop.mm0` is left out: it declares no `@relation`, so there is
  nothing to compare under.

Copied on 2026-10-20 from Carnap 43c916d. Refresh by copying again; nothing
here is edited.
