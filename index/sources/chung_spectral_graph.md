# Chung - Spectral Graph Theory

## Bibliographic Information

- **Author**: Fan R. K. Chung
- **Title**: Spectral Graph Theory
- **Series**: CBMS Regional Conference Series in Mathematics 92
- **Publisher**: American Mathematical Society
- **Year**: 1997

## Scope of Results Used

Cheeger-type inequalities relating the conductance of a graph to the
spectral gap of its normalized Laplacian, and the Laplacian form of the
variational characterization of the algebraic connectivity.

## Theorem to Axiom Mapping

| Theorem | Lean Axiom | Module |
|---------|------------|--------|
| Chapter 2 (Cheeger lower bound) | `cheeger_lower_bound` | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Chapter 2 (Cheeger upper bound) | `cheeger_upper_bound` | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Section 1.3 (variational λ₂, Laplacian form) | `lambda2_variational` | `Scaffold.Mathlib.GraphTheory.Spectral` |

## Notes

- **Restriction**: the Lean statements are restricted to `d`-regular
  weighted graphs with positive degree `d`, where the symmetric
  normalized Laplacian reduces to `1 - d⁻¹ • A`; the general irregular
  statement requires a matrix square root not available in the pinned
  Mathlib and is future work.
- **Conventions**: `cheegerConstant` is the infimum of the volume-based
  conductance `boundary / min (vol S, vol Sᶜ)` over nonempty proper
  vertex subsets; for a `d`-regular graph of positive degree this is
  the standard conductance.
- Earlier revisions of the repository recorded page-level locators
  (Theorem 2.1 p. 42, Theorem 2.2 p. 44) against a different statement
  shape; they were dropped pending citation review.

## See Also

- [Spectral Graph Theory map](../map/spectral_graph.md)
