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
Courant–Fischer variational characterization. Since 2026-08-22, also the
Perron–Frobenius theory of irreducible nonnegative matrices — the
second, non-symmetric spectral toolkit, admitted at the directed axis;
since 2026-08-24, additionally the primitive-matrix power limit — the
directed axis' convergence toolkit (see §8.5 below).

## Theorem to Axiom Mapping

| Theorem | Lean Declaration | Kind | Module |
|---------|-------------------|------|--------|
| Theorem 8.4.4 (Perron–Frobenius, irreducible nonnegative matrices) | `perron_frobenius` | **axiom (admitted 2026-08-22)** | `Scaffold.Mathlib.LinearAlgebra.PerronFrobenius` |
| §8.5 (primitive matrices; the Perron–Frobenius limit for primitive matrices), specialized to the row-stochastic case at Perron root `1` | `primitive_power_tendsto` | **theorem (proved 2026-09-02 by the Doeblin/Dobrushin contraction route; admitted 2026-08-24–2026-09-02)** | `Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence` |
| Section 4.3 (Cauchy interlacing) | `eigen_interlacing_principal_submatrix` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |
| Section 4.2 (Courant–Fischer, second-eigenvalue instance) | `lambda2_variational` | **theorem (proved 2026-08-18; axiom before, retired)** | `Scaffold.Mathlib.GraphTheory.Spectral` |
| Section 4.2 (Courant–Fischer, general min–max at every index) | `evals_min_max` | **theorem (proved 2026-08-18; never admitted)** | `Scaffold.Mathlib.GraphTheory.Spectral` |

## Notes

- `perron_frobenius` is admitted (not proved): the directed axis' second
  spectral toolkit, absent from the pinned Mathlib.
- `primitive_power_tendsto` is **proved** (retired 2026-09-02,
  `proposals/retire-primitive-power-convergence.md`): the elementary
  Doeblin/Dobrushin contraction route — no Perron–Frobenius machinery
  — at the unchanged admitted statement. The primitivity hypothesis
  remains load-bearing and fenced (the `DirectedMixing_QA` 2-cycle
  fence re-proves the `strict_dominance_refuted_QA` boundary in limit
  form, with every other hypothesis verified on the fixture — exactly
  `hprim` isolated). Statement differences from the source, recorded
  in the module documentation: the source's primitive limit is stated
  at the Perron data `lim (A/ρ(A))^m = x yᵀ`; the Lean statement is
  the row-stochastic specialization `Pᵗ *ᵥ x → (π ⬝ᵥ x) • 1` at root
  `1` (the specialization is one line of Perron-vector
  identification, stated directly for a small blast radius);
  primitivity is the positive-power definition
  (`Matrix.IsPrimitive`); the given-π form (no existential —
  consumers hold the delivered unique stationary vector); arbitrary
  `Fintype V` with no guard (the mass-one hypothesis is unsatisfiable
  on the empty type; trivial on a singleton). Honest scope: **no rate
  clause** — geometric rates need the complex spectral theory of
  non-symmetric matrices and are a separate future admission gated on
  a named consumer; entrywise/Π topology only. The stochastic-form
  cross-reference is Levin–Peres–Wilmer, "Markov Chains and Mixing
  Times" (AMS 2009), Theorem 4.9 — the mathematical content admitted
  is Horn–Johnson's; both locators section-level pending the same
  physical-copy review. Statement
  differences from Theorem 8.4.4, recorded in the module documentation:
  the source works at matrix size `n ≥ 2`, where irreducibility already
  forces a positive entry; the Lean statement is over an arbitrary
  `Fintype V` and carries the explicit `hex : ∃ i j, 0 < A i j` guard
  (exactly the missing strength at `card V ≤ 1`); irreducibility is the
  combinatorial strong-connectivity predicate `Matrix.IsIrreducible`
  (`ReflTransGen` on positive entries) rather than permutation
  similarity; simplicity is `rootMultiplicity r A.charpoly = 1` over ℝ;
  and the spectral radius is encoded through the complexified charpoly
  roots (the pin has no matrix spectral radius). Deliberately **no
  strict-dominance clause** — that requires primitivity; the QA
  centerpiece `strict_dominance_refuted_QA` exhibits the asymmetric
  directed 2-cycle `!![0,4;1,0]` (Perron root `2`, second eigenvalue
  `−2` of equal modulus) so the admitted statement cannot be mistaken
  for the stronger primitive case.
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
