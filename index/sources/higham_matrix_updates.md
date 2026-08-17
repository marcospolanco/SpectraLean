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

| Theorem | Lean Axiom | Module |
|---------|------------|--------|
| Woodbury identity | `woodbury_identity` | `Scaffold.Mathlib.Core.MatrixUpdates` |
| Sherman–Morrison formula | `sherman_morrison` | `Scaffold.Mathlib.Core.MatrixUpdates` |

## Notes

- Stated over an arbitrary field `𝕜` with explicit `IsUnit …det`
  hypotheses; matrix inversion is total (junk-valued at singular
  matrices), so the invertibility hypotheses make the identities
  meaningful.
- Sherman–Morrison is written with entrywise outer products
  `fun i j => u i * v j` and a scalar denominator
  `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` required to be nonzero.
