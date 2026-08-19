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

| Theorem | Lean Declaration | Kind | Module |
|---------|-------------------|------|--------|
| Section 4.3 (Cauchy interlacing) | `eigen_interlacing_principal_submatrix` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |
| Section 4.2 (Courant–Fischer, second-eigenvalue instance) | `lambda2_variational` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |
| Section 4.2 (Courant–Fischer, general min–max at every index) | `evals_min_max` | **theorem (proved 2026-08-18; never admitted)** | `Scaffold.Mathlib.GraphTheory.Spectral` |

## Notes

- Statements are indexed against Scaffold's sorted spectrum `evals`
  (nondecreasing, `Fin (Fintype.card V)`-indexed) rather than textbook
  index notation; the index bookkeeping is stated as explicit numeric
  hypotheses.
- `lambda2_variational` additionally follows the Laplacian form in
  Chung (1997) §1.3; see [Chung](chung_spectral_graph.md). It was
  converted from an admitted axiom to a proved theorem on 2026-08-18;
  the proof consumes the citation as classical background only. The
  pre-repair axiom shape (symmetry hypotheses, no weight
  nonnegativity) was materially false and is refuted in
  `Scaffold/QA/SpectralGraph/Variational_QA.lean`
  (`old_lambda2_variational_refuted_QA`).
- `eigen_interlacing_principal_submatrix` was converted from an
  admitted axiom to a proved theorem on 2026-08-18 (a pure proof task:
  the admitted statement was the true textbook window). The proof
  consumes the proved general Courant–Fischer engine (`evals_min_max`
  and its two witness directions) through the extend-by-zero padding
  bridge; the citation is classical background only.

## See Also

- [Spectral Graph Theory map](../map/spectral_graph.md)
