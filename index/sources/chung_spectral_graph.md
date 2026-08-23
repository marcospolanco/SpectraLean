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
| Chapter 2 (Cheeger lower bound) | `cheeger_lower_bound` | **theorem (proved 2026-08-23; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Chapter 2 (Cheeger upper bound) | `cheeger_upper_bound` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Cheeger` |
| Chapter 2 (cut-existence corollary) | `cheeger_cut_existence` | theorem (proved 2026-08-23; never admitted) | `Scaffold.Mathlib.GraphTheory.Fiedler` |
| Section 1.3 (variational λ₂, Laplacian form) | `lambda2_variational` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |

## Notes

- **Cut-existence corollary (2026-08-23):** `cheeger_cut_existence`
  (Fiedler Phase B, `proposals/fiedler-partitioning.md`) — on every
  connected `d`-regular graph a nonempty proper `S` exists with
  `conductance S ^ 2 ≤ 2 · lambda2 / d` — composed from the proved
  sweep lemma evaluated at the Fiedler vector, the attained conductance
  minimum (`cheegerConstant_attained`), and the Rayleigh transfer
  `R_{L_sym}(f) = lambda2 / d`. Never admitted; hard crust from birth.

- **Retirement (2026-08-23):** the lower bound (`cheeger_lower_bound`,
  the hard direction `φ²/2 ≤ λ₂`) is now *proved* — the median split
  route of `proposals/discharge-perturbation-axioms.md` Steps 1a/1b/1c
  (the Cauchy–Schwarz core and fused contraction; the co-area core; the
  median/level-set/assembly layer and sweep lemma), discharged to the
  spectrum through `secondEval_variational`. No admitted dependencies;
  both Cheeger inequalities are now hard crust, and this source's rows
  are all proved.

- **Retirement (2026-08-18):** the upper bound (`cheeger_upper_bound`,
  the easy direction `λ₂ ≤ 2φ`) is now *proved* from the
  general-operator Courant–Fischer (`secondEval_variational` in
  `Spectral.lean`, whose Laplacian instance is the retired
  `lambda2_variational`) via the volume-centered cut indicator — no
  admitted dependencies.

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
