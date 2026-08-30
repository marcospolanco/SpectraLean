# Tropp - User-Friendly Tail Bounds for Sums of Random Matrices

## Bibliographic Information

- **Author**: Joel A. Tropp
- **Title**: User-Friendly Tail Bounds for Sums of Random Matrices
- **Journal**: Foundations of Computational Mathematics
- **Year**: 2012
- **Volume**: 12
- **Issue**: 4
- **Pages**: 389-434
- **DOI**: 10.1007/s10208-011-9099-z

## Scope of Results Used

This paper is the primary source for matrix concentration inequalities in Scaffold. Results include:

- Master bound / Laplace transform step (Proposition 3.1 — proved
  locally 2026-08-30, the retirement route's first slice)
- Matrix Bernstein inequality
- Matrix Hoeffding inequality
- Related matrix concentration tools

## Theorem to Axiom Mapping

### Main Results

| Theorem | Page | Lean Declaration | Module |
|---------|------|------------|---------|
| Proposition 3.1 (Laplace transform bound) | §3 | `matrix_master_bound` (**proved** 2026-08-30, `proposals/matrix-master-bound-first-slice.md`, with the deterministic engine `trace_exp_smul_eq_sum_exp_eigvalOf` — the trace-exponential spectral identity the pinned Mathlib lists as an open TODO; stated there one-sided in `λmax`, proved here in the two-sided spectral-norm union-bound form; `[Nonempty V]` guard load-bearing at `V = ∅`, `t = 0`, fenced in QA) | `Matrix/MasterBound.lean` |
| Theorem 1.1 (Matrix Bernstein) | 393 | `matrix_bernstein` (axiom) | `Matrix/Bernstein.lean` |
| Theorem 1.4 (Matrix Hoeffding) | 398 | `matrix_hoeffding` (axiom; `[Nonempty V]`-guarded since 2026-08-28; `iIndepFun`-repaired 2026-08-29, Errata §6; **centering clause `h_mean` added 2026-08-30, Errata §9** — the uncentered pre-repair shape was materially false, refuted by the deterministic constant-ones family) + the consumer `edgePerturbation_norm_tail` / `edgePerturbation_quadForm_tail` (derived, axiom-conditional) | `Matrix/Hoeffding.lean`, `Derived/EdgePerturbationTail.lean` |
| Theorem 7.1 (Matrix Azuma) | 421 | `matrix_azuma_hoeffding` (axiom) | `Matrix/Azuma.lean` |

Corollary 1.5 (simplified Bernstein) is not admitted; it has no current
consumer and can be derived from Theorem 1.1 when needed.

## Notes

- Tropp's matrix Bernstein inequality is the standard reference for matrix concentration
- The paper provides both tail bound and expectation forms
- Scaffold uses the tail bound form for consistency with scalar inequalities
- All matrix inequalities are stated for self-adjoint random matrices
