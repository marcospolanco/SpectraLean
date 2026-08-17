# Horn & Johnson - Matrix Analysis

## Bibliographic Information

- **Authors**: Roger A. Horn, Charles R. Johnson
- **Title**: Matrix Analysis
- **Edition**: 2nd edition
- **Publisher**: Cambridge University Press
- **Year**: 2013
- **Note**: Section-level locators recorded; page numbers to be confirmed
  during citation review.

## Scope of Results Used

Classical finite-dimensional symmetric eigenvalue theory used by the SGT
center: Cauchy interlacing for principal submatrices and the
Courant–Fischer variational characterization.

## Theorem to Axiom Mapping

| Theorem | Lean Axiom | Module |
|---------|------------|--------|
| Section 4.3 (Cauchy interlacing) | `eigen_interlacing_principal_submatrix` | `Scaffold.Mathlib.GraphTheory.Spectral` |
| Section 4.2 (Courant–Fischer) | `lambda2_variational` | `Scaffold.Mathlib.GraphTheory.Spectral` |

## Notes

- Statements are indexed against Scaffold's sorted spectrum `evals`
  (nondecreasing, `Fin (Fintype.card V)`-indexed) rather than textbook
  index notation; the index bookkeeping is stated as explicit numeric
  hypotheses.
- `lambda2_variational` additionally follows the Laplacian form in
  Chung (1997) §1.3; see [Chung](chung_spectral_graph.md).

## See Also

- [Spectral Graph Theory map](../map/spectral_graph.md)
