# Higham 2002 / Henderson & Searle 1981 - Matrix Update Identities

## Bibliographic Information

- **Author**: Nicholas J. Higham
- **Title**: Accuracy and Stability of Numerical Algorithms
- **Edition**: 2nd edition
- **Publisher**: SIAM
- **Year**: 2002
- **Note**: book-level citation; section-level locator to be refined
  during citation review.
- **Secondary source**: Henderson, H. V. & Searle, S. R., "On deriving
  the inverse of a sum of matrices", SIAM Review 23(1):53–60, 1981
  (survey of both identities).

## Scope of Results Used

The Woodbury matrix identity and its rank-one special case,
Sherman–Morrison. These are the algebraic mechanism behind low-rank
event updates of graph matrices.

## Theorem to Axiom Mapping

| Theorem | Lean declaration | Status | Module |
|---------|------------------|--------|--------|
| Woodbury identity | `woodbury_identity` | proved theorem (from Mathlib's `Matrix.invOf_add_mul_mul`, 2026-08-18) | `Scaffold.Mathlib.Core.MatrixUpdates` |
| Sherman–Morrison formula | `sherman_morrison` | axiom | `Scaffold.Mathlib.Core.MatrixUpdates` |

## Notes

- Stated over an arbitrary field `𝕜` with explicit `IsUnit …det`
  hypotheses; matrix inversion is total (junk-valued at singular
  matrices), so the invertibility hypotheses make the identities
  meaningful.
- **Woodbury repair (2026-08-18):** the formerly admitted
  `woodbury_identity` used the middle factor `C + V A⁻¹ U` with no
  invertibility hypothesis on `C` — a *false* statement (scalar
  counterexample `A = 1, U = V = 1, C = 0`, where all stated hypotheses
  hold and the two sides evaluate to `1` and `0`; refuted in
  `Scaffold.QA.Core.MatrixUpdates_QA.old_woodbury_identity_refuted_QA`).
  It is now a theorem proved from Mathlib at the standard middle factor
  `C⁻¹ + V A⁻¹ U` with the three explicit `IsUnit` determinant
  hypotheses (invertibility of the sum is derived, not hypothesized).
  The corrected statement is an intentional public API migration; the
  retired shape had zero consumers. See
  `proposals/repair-and-retire-woodbury.md` for the repair record.
- Sherman–Morrison is written with entrywise outer products
  `fun i j => u i * v j` and a scalar denominator
  `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` required to be nonzero. It remains admitted,
  pending its own statement-fidelity review (out of scope of the 2026-08-18
  Woodbury repair).
