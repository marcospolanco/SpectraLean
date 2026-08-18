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

| Theorem | Lean Declaration | Kind | Module |
|---------|-------------------|------|--------|
| Chapter 2 (Cheeger lower bound) | `cheeger_lower_bound` | axiom | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Chapter 2 (Cheeger upper bound) | `cheeger_upper_bound` | axiom | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Section 1.3 (variational λ₂, Laplacian form) | `lambda2_variational` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |

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
- **Statement-shape correction (2026-08-18)**: through 2026-08-17 the
  two Cheeger axioms stated their spectral side by composing `lambda2`
  with `regularNormalizedLaplacian A d`; since `lambda2` reads the
  spectrum of the combinatorial Laplacian *of* its argument, the
  asserted quantity was `λ₂(L(L_sym)) = λ₂(-L_sym)`, not `λ₂(L_sym)` —
  materially false on the two-vertex edge (`1/2 ≤ 0`, refuted in proved
  form by `QA.old_cheeger_lower_bound_refuted_QA`). Both axioms are now
  stated through `secondEval (regularNormalizedLaplacian A d)`, the
  second-smallest eigenvalue of the normalized Laplacian itself, which
  is the reading the citation above always intended.
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
