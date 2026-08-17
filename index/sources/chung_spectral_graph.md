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
- **Conventions**: `cheegerConstant` is the infimum of the
  volume-based conductance `boundary / min (vol S, vol Sᶜ)` over
  nonempty proper vertex subsets; for a `d`-regular graph of positive
  degree this is the standard conductance.
- **Locator status**: the Cheeger bounds are cited at chapter level
  (Chapter 2). The initial commit of this repository cited
  "Theorem 2.2" without a page; the SGT-center rebuild moved to the
  chapter-level locator because the Lean statement shape changed
  (restriction to `d`-regular graphs, volume-based conductance).
  Theorem-level and page-level numbering remain unconfirmed against the
  printed text and will not be recorded until verified from a physical
  or publisher copy.

## See Also

- [Spectral Graph Theory map](../map/spectral_graph.md)
