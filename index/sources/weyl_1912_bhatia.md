# Weyl 1912 / Bhatia 1997 - Eigenvalue Perturbation

## Bibliographic Information

- **Author**: Hermann Weyl
- **Title**: Das asymptotische Verteilungsgesetz der Eigenwerte linearer
  partieller Differentialgleichungen
- **Journal**: Mathematische Annalen
- **Volume/Issue**: 71(4)
- **Pages**: 441–479
- **Year**: 1912
- **Secondary source**: Rajendra Bhatia, "Matrix Analysis", Springer,
  1997, Theorem III.2.1 (the modern matrix-analysis statement used
  here).

## Scope of Results Used

Weyl's inequality bounding the movement of each eigenvalue of a real
symmetric matrix under a symmetric perturbation, and its gap-stability
corollary.

## Theorem to Axiom Mapping

| Theorem | Lean Axiom | Module |
|---------|------------|--------|
| Theorem III.2.1 (Weyl's inequality) | `weyl_inequality` — **retired from axiom to proved theorem 2026-08-20** (`proposals/discharge-perturbation-axioms.md`: the additive window from the Courant–Fischer engine + the proved `l2OpNorm_eq_max_abs_evals` bridge; the entry is kept for provenance) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl` |
| Corollary of Theorem III.2.1 | `spectral_gap_stability` (proved; fully hard crust since the Weyl retirement) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl` |

## Notes

- Eigenvalues are Scaffold's sorted `evals` (nondecreasing,
  `Fin (Fintype.card V)`-indexed); the norm is the ℓ² operator norm
  (`Matrix.L2OpNorm`).
- `spectral_gap_stability` states the endpoint-by-endpoint argument
  explicitly: each gap endpoint moves by at most `‖E‖`, so the gap
  shrinks by at most `2‖E‖`.

## See Also

- [Perturbation map](../map/perturbation.md)
