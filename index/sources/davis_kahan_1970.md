# Davis & Kahan 1970 - Rotation of Eigenvectors by a Perturbation

## Bibliographic Information

- **Authors**: Chandler Davis, William M. Kahan
- **Title**: The rotation of eigenvectors by a perturbation
- **Journal**: SIAM Journal on Numerical Analysis
- **Volume/Issue**: 7(1)
- **Pages**: 1–46
- **Year**: 1970
- **Secondary source**: Yu, Y., Wang, T., Samworth, R. J., "A useful
  variant of the Davis–Kahan theorem for statisticians", Annals of
  Statistics 43(3):2028–2061, 2015, Theorem 2 (two-sided separation,
  projector form, constant 1).

## Scope of Results Used

The sin Θ theorem for invariant spectral subspaces, in the projector
form used by the event-driven persistence frontier.

## Theorem to Axiom Mapping

| Theorem | Lean Axiom | Module |
|---------|------------|--------|
| §3 (sin Θ theorem) via Yu–Wang–Samworth Thm 2 | `davis_kahan_sin_theta` | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan` |
| Consequence applied per step | `spectral_persistence` | `Scaffold.Mathlib.GraphTheory.Dynamics` |

## Notes

- The Scaffold statement is for the projector onto the `k+1` smallest
  eigenvalues, with a pairwise separation hypothesis on sorted
  eigenvalue indices, distance measured by the ℓ² operator norm
  (`Matrix.L2OpNorm`).
- `spectral_persistence` composes the per-step Davis–Kahan bound with
  Weyl gap stability (see [Weyl/Bhatia](weyl_1912_bhatia.md)) along an
  event stream; it is Scaffold's dynamic-frontier admission and carries
  the research content, while Davis–Kahan itself is the classical
  engine.

## See Also

- [Perturbation map](../map/perturbation.md)
