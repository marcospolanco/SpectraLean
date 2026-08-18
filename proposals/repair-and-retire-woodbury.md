# Proposal: Repair and Retire the Woodbury Identity Axiom

**Status:** Delivered 2026-08-18 (see
[Delivery record](#delivery-record) below; the original proposal text
follows unedited for the record). This document authorizes no Lean
changes, axiom removals, API migration, commits, or external
publication on its own.

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

## Delivery record (2026-08-18)

All acceptance criteria met; run `20260818T193004Z-run-1`.

1. **Refutation QA** (`Scaffold.QA.Core.MatrixUpdates_QA`, the first
   Core-domain QA file): `old_woodbury_identity_refuted_QA` negates the
   retired axiom's own statement at `n = k = Fin 1`, `𝕜 = ℚ`, consuming
   no axiom; `old_woodbury_middle_hyp_holds_QA` and
   `old_woodbury_sum_hyp_holds_QA` separately prove the retired middle
   and sum determinant hypotheses *satisfied* at the counterexample
   (`A = U = V = !![1]`, `C = !![0]`), so the refutation is of a
   genuinely applicable statement, not a vacuous shape.
2. **Repair and proof:** `woodbury_identity` is now a theorem at the
   same name with the standard middle factor `(C⁻¹ + V * A⁻¹ * U)⁻¹`
   and exactly the three hypotheses `IsUnit A.det`, `IsUnit C.det`,
   `IsUnit (C⁻¹ + V * A⁻¹ * U).det`. The former
   `IsUnit (A + U * C * V).det` hypothesis was dropped as derivable —
   a deliberate strengthening beyond the proposal's sketch, taking
   advantage of Mathlib's `Matrix.invertibleAddMulMul`, which
   constructs the sum's `Invertible` instance from the middle one.
   Proof: `Matrix.invOf_add_mul_mul` plus
   `Matrix.invertibleOfIsUnitDet`/`Matrix.invOf_eq_nonsing_inv`, all
   reachable through the module's existing imports; no new axioms, no
   `sorry`, no wrapper.
3. **Hypothesis exclusion witness:**
   `corrected_C_hyp_excludes_counterexample_QA` proves `¬IsUnit
   (!![0]).det` — the new `IsUnit C.det` hypothesis excludes exactly
   the counterexample where the retired statement was false.
4. **Positive QA:** scalar instance `A = 2, U = V = 1, C = 3` — the
   updated matrix `5` inverts to `1/5` computed directly, and the
   theorem's right side is pinned to the same `1/5` by *consuming* the
   theorem; non-scalar rank-one instance `A = diag 2 2`, all-ones
   `U`, `V`, `C = 1` — the sum `!![3,1;1,3]` inverts to
   `!![3/8,-1/8;-1/8,3/8]` by the adjugate formula, the middle factor
   computes to `(1 + 1)⁻¹ = 1/2`, and the theorem's right side is
   pinned to the same inverse through the theorem. Computation route:
   1×1 inverses via `Matrix.inv_eq_left_inv` cancellation and 2×2 via
   the adjugate formula (`Ring.inverse` discharged through
   `Ring.inverse_eq_inv`) — `decide` alone cannot evaluate
   `Matrix.inv` (kernel reduction sticks on `Ring.inverse`), recorded
   here for future QA in this domain.
5. **Records:** both indexes (`index/sources/higham_matrix_updates.md`
   with the repair note, `index/map/perturbation.md` — the row now
   reads "proved (from Mathlib)"), scoreboard (15/443/0 with the
   milestone bullet and verification rows), radar (axiom-minimization
   re-scored 4.0 → 4.5 per its protocol; QA count synced 443/26),
   README (15 axioms, 443 QA declarations), and this record.
   `sherman_morrison` remains admitted, out of scope here.
6. **Verification:** `lake env lean` on `Core.MatrixUpdates` and
   `QA.Core.MatrixUpdates_QA` — zero errors, zero warnings; all
   twenty-six QA modules elaborated directly (zero errors; only the
   documented pre-existing linter notes in untouched modules); full
   `lake build` ✔ (2179 targets); `lint_axioms` (15 covered),
   `check_citations`, `check_markdown_links` pass; scoreboard
   regenerated from source.

**Migration note (public API):** the corrected theorem is an
intentional breaking change at the same name — middle factor and
hypothesis set both changed. No deprecated compatibility declaration
was retained: the retired statement is false, and a compatibility alias
would have to restate a falsehood (per this proposal's own scope and
architecture §9's emergency-removal provision). Zero consumers existed
at retirement time.
