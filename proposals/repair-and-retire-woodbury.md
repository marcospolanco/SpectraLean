# Proposal: Repair and Retire the Woodbury Identity Axiom

**Status:** Proposed; **priority:** High — reconsidered 2026-08-18 (see
[Priority reconsidered](#priority-reconsidered) below; the original
consumer-driven case for Low, made in [Why it is low
priority](#why-it-is-low-priority), stands unedited for the record). This
document authorizes no Lean changes, axiom removals, API migration, commits,
or external publication on its own.

## Summary

Repair the statement shape of
`Scaffold.Mathlib.Core.woodbury_identity`, then replace the repaired axiom
with Mathlib's proved Woodbury identity. This is a low-priority trust-surface
repair: it has an unusually direct upstream route, but no current Lean
consumer beyond its own API module, so it must not displace the active SGT
work.

## Why this needs repair before proof

The current axiom states the middle inverse as

```text
(C + V A⁻¹ U)⁻¹
```

with no invertibility hypothesis on `C`. The standard Woodbury identity, and
Mathlib's theorem, instead use

```text
(C⁻¹ + V A⁻¹ U)⁻¹
```

and require `C` to be invertible. The existing statement is false even in
the one-dimensional scalar case: take `A = 1`, `U = V = 1`, and `C = 0`.
All three current determinant hypotheses hold (`A`, `C + V A⁻¹ U`, and
`A + U C V` are the scalar `1`), but the left side is `1` and the right side
is `0`.

This is a statement-shape repair, not a refactoring. The old declaration
must not be treated as a theorem merely because it has an explicit citation.

## Existing Mathlib route

The pinned Mathlib already contains the proof in
`Mathlib/Data/Matrix/Invertible.lean`:

```lean
Matrix.invOf_add_mul_mul
```

It proves the identity for `[Invertible A]`, `[Invertible C]`, and
`[Invertible (C⁻¹ + V * A⁻¹ * U)]`, using `⅟` inverses. Scaffold already
imports `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, which supplies
the bridge from `IsUnit M.det` to an `Invertible M` instance and the equality
between `⅟M` and `M⁻¹` under that hypothesis.

This targeted survey corrects no row of the Mathlib Coverage Map: the map
describes spectral linear algebra rather than low-rank inverse-update
identities. It does establish a precise local replacement route for this
axiom.

## Scope

1. Add a QA refutation of the old scalar statement without consuming the
   axiom, so the migration has a durable negative witness.
2. Replace the axiom by a theorem with the standard middle factor and exact
   explicit hypotheses:
   - `IsUnit A.det`;
   - `IsUnit C.det`; and
   - `IsUnit (C⁻¹ + V * A⁻¹ * U).det`.
3. Use `Matrix.invOf_add_mul_mul` plus the proved nonsingular-inverse bridges
   to establish the corrected theorem. Do not add a new axiom or hide the
   change behind an equivalently named wrapper.
4. Add a positive QA instance at nonzero scalar matrices and a small
   non-scalar instance if elaboration remains simple.
5. Update the source/index record, public migration note, scoreboard, and
   current explicit-axiom count.

The theorem's corrected hypotheses and `C⁻¹` factor are an intentional public
API migration. Retain a deprecated compatibility declaration only if the
project's deprecation policy requires one; it must not restate the false old
identity.

## Why it is low priority

`woodbury_identity` has no current Lean consumer; searching the repository
finds only its declaration and documentation. Its neighboring
`sherman_morrison` axiom is not automatically in scope: it needs its own
statement-fidelity review and may require a different proof adaptation.

The work is therefore valuable as a clean pilot for the mushy-center
elimination process, but it does not presently unlock an SGT theorem,
application, or active proposal. Do it only after the High and Medium
consumer-driven work is clear, or when an event-update consumer makes the
identity load-bearing.

## Priority reconsidered

Raised to High 2026-08-18, on review. The case above for Low is a correct
application of the leverage test as written — zero consumers, no unlocked
SGT theorem — and is left in place rather than deleted, because the
override below is a different argument, not a rebuttal of that one.

The axiom is not merely unproven; it is **false**, independently verified
by hand against the current source (`A = 1, U = V = 1, C = 0`: every
stated hypothesis holds, and the axiom's own formula evaluates to `0`
where the true inverse is `1`). A false statement sitting in the trust
base is a different category of risk than an admitted-but-true axiom
awaiting proof, and it does not need a consumer to be dangerous — it needs
the *absence* of one, so far, to be why nobody has been bitten by it yet.
`GraphTheory/Dynamics.lean`'s own docstring names event-driven Laplacian
updates as the intended future consumer of this exact identity; if that
connection is ever wired up before this repair lands, it would silently
inherit a false axiom. Repairing it now, while it is still unconsumed and
the fix is cheap, is strictly better than discovering it the way
`cheeger_lower_bound` was discovered — after something downstream had
already been built on it.

This does not reopen the leverage test generally. It is a narrow claim:
correctness repair of a *known-false* admitted statement is worth doing
ahead of its consumers, not just after them, precisely because deferring
it risks the exact failure mode `docs/1_STRATEGY.md`'s load-bearing-growth
principle exists to catch.

## Acceptance criteria

- The old statement's scalar counterexample is checked in QA.
- The corrected public theorem is proved from Mathlib, with no `axiom`,
  `sorry`, or `admit` introduced.
- Its changed module and QA file elaborate directly; the standard hygiene
  checks and `lake build` pass.
- Documentation distinguishes the false retired statement from the corrected
  proved theorem and records the axiom-count change from generated evidence.
